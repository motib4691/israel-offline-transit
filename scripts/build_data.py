#!/usr/bin/env python3
"""
Build a compact, high-speed offline Israeli public-transport SQLite database (format v6).

1. Filters active schedules only (yesterday to +35 days).
2. Preserves all fields required by the app (stop_desc, platform_code, parent_station,
   route_desc, route_type, stable GTFS stop_id/stop_code, exact per-trip times down
   to the second including dwell times and overnight trips >= 24:00).
3. Replaces raw stop_times / trip_patterns with deduplicated timing_profiles and
   compressed per-pattern schedule BLOBs, eliminating multi-hundred-MB text/index bloat.
4. Prunes inactive routes/stops while preserving active parent_station records.
"""

import argparse
import array
import csv
import io
import os
import re
import sqlite3
import sys
import tempfile
import zipfile
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path


REQUIRED_GTFS_FILES = (
    "agency.txt",
    "routes.txt",
    "trips.txt",
    "stops.txt",
    "stop_times.txt",
    "calendar.txt",
)

WEEKDAY_COLUMNS = (
    "monday",
    "tuesday",
    "wednesday",
    "thursday",
    "friday",
    "saturday",
    "sunday",
)


def encode_uvarint(value: int, out: bytearray) -> None:
    v = int(value)
    if v < 0:
        raise ValueError(f"Unsigned varint cannot encode negative value: {v}")
    while v >= 0x80:
        out.append((v & 0x7F) | 0x80)
        v >>= 7
    out.append(v)


def encode_svarint(value: int, out: bytearray) -> None:
    v = int(value)
    zigzag = (v << 1) ^ (-1 if v < 0 else 0)
    encode_uvarint(zigzag, out)


def decode_uvarint(buf: bytes, pos: int) -> tuple[int, int]:
    result = 0
    shift = 0
    while True:
        b = buf[pos]
        pos += 1
        result |= (b & 0x7F) << shift
        if b < 0x80:
            return result, pos
        shift += 7


def decode_svarint(buf: bytes, pos: int) -> tuple[int, int]:
    z, pos = decode_uvarint(buf, pos)
    val = (z >> 1) ^ (-(z & 1))
    return val, pos


def detect_encoding(archive: zipfile.ZipFile, member_name: str) -> str:
    with archive.open(member_name, "r") as raw:
        sample = raw.read(128 * 1024)
    # Trim potential incomplete trailing UTF-8 sequence at sample boundary
    trimmed = sample[:-4] if len(sample) > 4 else sample
    for encoding in ("utf-8-sig", "utf-8", "cp1255", "windows-1252"):
        try:
            trimmed.decode(encoding)
            return encoding
        except UnicodeDecodeError:
            continue
    return "utf-8-sig"


def open_csv_reader(archive: zipfile.ZipFile, member_name: str):
    encoding = detect_encoding(archive, member_name)
    raw_stream = archive.open(member_name, "r")
    text_stream = io.TextIOWrapper(raw_stream, encoding=encoding, errors="replace", newline="")
    reader = csv.reader(text_stream)
    return raw_stream, text_stream, reader


def normalize_headers(headers: list[str]) -> dict[str, int]:
    mapping: dict[str, int] = {}
    for idx, col in enumerate(headers):
        clean = (col or "").strip().lstrip("\ufeff").lower()
        if clean and clean not in mapping:
            mapping[clean] = idx
    return mapping


def get_col(row: list[str], col_map: dict[str, int], name: str, default: str = "") -> str:
    idx = col_map.get(name)
    if idx is None or idx >= len(row):
        return default
    val = row[idx]
    return val.strip() if val else default


def parse_gtfs_time(value: str, row_number: int) -> int | None:
    if not value:
        return None
    match = re.fullmatch(r"([0-9]{1,3}):([0-5][0-9]):([0-5][0-9])", value)
    if not match:
        raise ValueError(f"Invalid GTFS time at row {row_number}: {value!r}")
    return int(match.group(1)) * 3600 + int(match.group(2)) * 60 + int(match.group(3))


def parse_nonnegative_int(value: str, field_name: str, row_number: int) -> int:
    if not re.fullmatch(r"[0-9]+", value):
        raise ValueError(f"Invalid integer in {field_name} at row {row_number}: {value!r}")
    return int(value)


def parse_optional_float(value: str) -> float | None:
    if not value:
        return None
    try:
        val = float(value)
        return val if val == val else None
    except ValueError:
        return None


def find_archive_member(archive: zipfile.ZipFile, target_name: str) -> str | None:
    target = target_name.lower()
    for name in archive.namelist():
        if not name.endswith("/") and Path(name).name.lower() == target:
            return name
    return None


def load_services(
    archive: zipfile.ZipFile,
    min_date_int: int,
    max_date_int: int,
) -> tuple[dict[str, int], list[tuple[int, int, int, int]], list[tuple[int, int, int]]]:
    """
    Loads active calendar and calendar_dates within [min_date_int, max_date_int],
    deduplicates identical schedules, and returns:
      - service_id_to_idx: dict[str, int]
      - calendar_rows: list[(service_idx, weekday_mask, start_date_int, end_date_int)]
      - calendar_date_rows: list[(service_idx, date_int, exception_type)]
    """
    raw_calendars: dict[str, tuple[int, int, int]] = {}
    calendar_member = find_archive_member(archive, "calendar.txt")
    if not calendar_member:
        raise ValueError("Missing required GTFS file: calendar.txt")

    raw_s, text_s, reader = open_csv_reader(archive, calendar_member)
    try:
        headers = next(reader, [])
        col_map = normalize_headers(headers)
        for row in reader:
            if not row:
                continue
            s_id = get_col(row, col_map, "service_id")
            start_str = get_col(row, col_map, "start_date")
            end_str = get_col(row, col_map, "end_date")
            if not s_id or len(start_str) != 8 or len(end_str) != 8:
                continue
            start_int = int(start_str)
            end_int = int(end_str)
            if end_int < min_date_int or start_int > max_date_int:
                continue
            mask = 0
            for bit_idx, day_col in enumerate(WEEKDAY_COLUMNS):
                if get_col(row, col_map, day_col) == "1":
                    mask |= 1 << bit_idx
            clamped_start = max(start_int, min_date_int)
            clamped_end = min(end_int, max_date_int)
            if clamped_start <= clamped_end:
                raw_calendars[s_id] = (mask, clamped_start, clamped_end)
    finally:
        text_s.close()
        raw_s.close()

    raw_exceptions: dict[str, list[tuple[int, int]]] = defaultdict(list)
    dates_member = find_archive_member(archive, "calendar_dates.txt")
    if dates_member:
        raw_s, text_s, reader = open_csv_reader(archive, dates_member)
        try:
            headers = next(reader, [])
            col_map = normalize_headers(headers)
            for row in reader:
                if not row:
                    continue
                s_id = get_col(row, col_map, "service_id")
                date_str = get_col(row, col_map, "date")
                ex_str = get_col(row, col_map, "exception_type")
                if not s_id or len(date_str) != 8 or ex_str not in ("1", "2"):
                    continue
                date_int = int(date_str)
                if min_date_int <= date_int <= max_date_int:
                    raw_exceptions[s_id].append((date_int, int(ex_str)))
        finally:
            text_s.close()
            raw_s.close()

    candidate_service_ids = set(raw_calendars.keys())
    for s_id, ex_list in raw_exceptions.items():
        if any(ex_type == 1 for _, ex_type in ex_list):
            candidate_service_ids.add(s_id)

    signature_to_idx: dict[tuple, int] = {}
    service_id_to_idx: dict[str, int] = {}
    calendar_rows: list[tuple[int, int, int, int]] = []
    calendar_date_rows: list[tuple[int, int, int]] = []

    for s_id in sorted(candidate_service_ids):
        cal_tuple = raw_calendars.get(s_id, (0, min_date_int, max_date_int))
        mask, start_int, end_int = cal_tuple
        # Deduplicate exceptions by date (keep last if duplicate)
        ex_map = {d: ex for d, ex in raw_exceptions.get(s_id, ())}
        sorted_ex = tuple(sorted(ex_map.items()))
        if mask == 0 and not any(ex == 1 for _, ex in sorted_ex):
            continue

        sig = (mask, start_int, end_int, sorted_ex)
        s_idx = signature_to_idx.get(sig)
        if s_idx is None:
            s_idx = len(signature_to_idx)
            signature_to_idx[sig] = s_idx
            calendar_rows.append((s_idx, mask, start_int, end_int))
            for d_int, ex_type in sorted_ex:
                calendar_date_rows.append((s_idx, d_int, ex_type))

        service_id_to_idx[s_id] = s_idx

    print(
        f"Active service IDs: {len(service_id_to_idx):,} "
        f"(deduplicated into {len(calendar_rows):,} unique schedules)"
    )
    return service_id_to_idx, calendar_rows, calendar_date_rows


def load_agencies(archive: zipfile.ZipFile) -> dict[str, str]:
    member = find_archive_member(archive, "agency.txt")
    if not member:
        raise ValueError("Missing required GTFS file: agency.txt")
    agencies: dict[str, str] = {}
    raw_s, text_s, reader = open_csv_reader(archive, member)
    try:
        headers = next(reader, [])
        col_map = normalize_headers(headers)
        for row in reader:
            if not row:
                continue
            a_id = get_col(row, col_map, "agency_id")
            a_name = get_col(row, col_map, "agency_name")
            if a_name or a_id:
                agencies[a_id] = a_name
    finally:
        text_s.close()
        raw_s.close()
    return agencies


def load_routes(archive: zipfile.ZipFile) -> dict[str, tuple[str, str, str, str, str]]:
    member = find_archive_member(archive, "routes.txt")
    if not member:
        raise ValueError("Missing required GTFS file: routes.txt")
    routes: dict[str, tuple[str, str, str, str, str]] = {}
    raw_s, text_s, reader = open_csv_reader(archive, member)
    try:
        headers = next(reader, [])
        col_map = normalize_headers(headers)
        for row in reader:
            if not row:
                continue
            r_id = get_col(row, col_map, "route_id")
            if not r_id:
                continue
            agency_id = get_col(row, col_map, "agency_id")
            short_name = get_col(row, col_map, "route_short_name")
            long_name = get_col(row, col_map, "route_long_name")
            route_type = get_col(row, col_map, "route_type", "3")
            route_desc = get_col(row, col_map, "route_desc")
            routes[r_id] = (agency_id, short_name, long_name, route_type, route_desc)
    finally:
        text_s.close()
        raw_s.close()
    print(f"Loaded routes: {len(routes):,}")
    return routes


def load_stops(archive: zipfile.ZipFile) -> tuple[
    dict[str, int],
    list[tuple[str, str, str, float | None, float | None, str, str, str]],
]:
    member = find_archive_member(archive, "stops.txt")
    if not member:
        raise ValueError("Missing required GTFS file: stops.txt")
    stop_id_to_raw_idx: dict[str, int] = {}
    raw_stops: list[tuple[str, str, str, float | None, float | None, str, str, str]] = []

    raw_s, text_s, reader = open_csv_reader(archive, member)
    try:
        headers = next(reader, [])
        col_map = normalize_headers(headers)
        for row in reader:
            if not row:
                continue
            s_id = get_col(row, col_map, "stop_id")
            if not s_id or s_id in stop_id_to_raw_idx:
                continue
            s_code = get_col(row, col_map, "stop_code")
            s_name = get_col(row, col_map, "stop_name")
            s_lat = parse_optional_float(get_col(row, col_map, "stop_lat"))
            s_lon = parse_optional_float(get_col(row, col_map, "stop_lon"))
            parent_station = get_col(row, col_map, "parent_station")
            stop_desc = get_col(row, col_map, "stop_desc")
            platform_code = get_col(row, col_map, "platform_code")

            stop_id_to_raw_idx[s_id] = len(raw_stops)
            raw_stops.append(
                (s_id, s_code, s_name, s_lat, s_lon, parent_station, stop_desc, platform_code)
            )
    finally:
        text_s.close()
        raw_s.close()

    print(f"Loaded stops: {len(raw_stops):,}")
    return stop_id_to_raw_idx, raw_stops


def load_active_trips(
    archive: zipfile.ZipFile,
    service_id_to_idx: dict[str, int],
    raw_routes: dict[str, tuple[str, str, str, str, str]],
) -> tuple[
    dict[str, int],
    list[tuple[str, int, str, int]],
    list[str],
]:
    member = find_archive_member(archive, "trips.txt")
    if not member:
        raise ValueError("Missing required GTFS file: trips.txt")

    trip_id_to_idx: dict[str, int] = {}
    trip_meta: list[tuple[str, int, str, int]] = []
    headsign_to_idx: dict[str, int] = {"": 0}
    headsigns: list[str] = [""]

    raw_s, text_s, reader = open_csv_reader(archive, member)
    try:
        headers = next(reader, [])
        col_map = normalize_headers(headers)
        for row in reader:
            if not row:
                continue
            t_id = get_col(row, col_map, "trip_id")
            r_id = get_col(row, col_map, "route_id")
            s_id = get_col(row, col_map, "service_id")
            if not t_id or r_id not in raw_routes:
                continue
            s_idx = service_id_to_idx.get(s_id)
            if s_idx is None:
                continue

            direction_id = get_col(row, col_map, "direction_id")
            headsign = get_col(row, col_map, "trip_headsign")
            h_idx = headsign_to_idx.get(headsign)
            if h_idx is None:
                h_idx = len(headsigns)
                headsign_to_idx[headsign] = h_idx
                headsigns.append(headsign)

            t_idx = len(trip_meta)
            trip_id_to_idx[t_id] = t_idx
            trip_meta.append((r_id, s_idx, direction_id, h_idx))
    finally:
        text_s.close()
        raw_s.close()

    print(f"Active trips loaded: {len(trip_meta):,} (headsigns: {len(headsigns):,})")
    return trip_id_to_idx, trip_meta, headsigns


def build_database(gtfs_path: Path, output_path: Path) -> None:
    today = datetime.now(timezone.utc).date()
    min_date_int = int((today - timedelta(days=1)).strftime("%Y%m%d"))
    max_date_int = int((today + timedelta(days=35)).strftime("%Y%m%d"))
    print(f"Date window for active schedules: {min_date_int} to {max_date_int}")

    with zipfile.ZipFile(gtfs_path, "r") as archive:
        bad = archive.testzip()
        if bad:
            raise ValueError(f"Corrupted ZIP entry: {bad}")

        for req in REQUIRED_GTFS_FILES:
            if not find_archive_member(archive, req):
                raise ValueError(f"Missing required GTFS file: {req}")

        service_id_to_idx, calendar_rows, calendar_date_rows = load_services(
            archive, min_date_int, max_date_int
        )
        if not service_id_to_idx:
            raise ValueError("No active services found inside the target date window")

        agencies = load_agencies(archive)
        raw_routes = load_routes(archive)
        stop_id_to_raw_idx, raw_stops = load_stops(archive)
        trip_id_to_idx, trip_meta, headsigns = load_active_trips(
            archive, service_id_to_idx, raw_routes
        )
        if not trip_meta:
            raise ValueError("No active trips found inside the target date window")

        # Stream stop_times into a compact integer temp SQLite table to keep RAM low
        # and guarantee correct (t_idx, stop_sequence) ordering even on unsorted feeds.
        fd, tmp_st_path_str = tempfile.mkstemp(prefix="gtfs_st_", suffix=".sqlite")
        os.close(fd)
        tmp_st_path = Path(tmp_st_path_str)

        try:
            tmp_conn = sqlite3.connect(str(tmp_st_path))
            tmp_conn.execute("PRAGMA journal_mode=OFF")
            tmp_conn.execute("PRAGMA synchronous=OFF")
            tmp_conn.execute("PRAGMA temp_store=MEMORY")
            tmp_conn.execute("PRAGMA cache_size=-131072")
            tmp_conn.execute(
                """
                CREATE TABLE st (
                    t_idx INTEGER NOT NULL,
                    seq INTEGER NOT NULL,
                    s_idx INTEGER NOT NULL,
                    arr INTEGER NOT NULL,
                    dep INTEGER NOT NULL
                )
                """
            )

            stop_times_member = find_archive_member(archive, "stop_times.txt")
            raw_s, text_s, reader = open_csv_reader(archive, stop_times_member)
            inserted_st = 0
            try:
                headers = next(reader, [])
                col_map = normalize_headers(headers)
                t_col = col_map.get("trip_id")
                s_col = col_map.get("stop_id")
                seq_col = col_map.get("stop_sequence")
                arr_col = col_map.get("arrival_time")
                dep_col = col_map.get("departure_time")
                if None in (t_col, s_col, seq_col, arr_col, dep_col):
                    raise ValueError("stop_times.txt is missing required columns")

                batch = []
                row_num = 1
                for row in reader:
                    row_num += 1
                    if not row:
                        continue
                    t_id = row[t_col].strip() if t_col < len(row) else ""
                    t_idx = trip_id_to_idx.get(t_id)
                    if t_idx is None:
                        continue

                    s_id = row[s_col].strip() if s_col < len(row) else ""
                    s_idx = stop_id_to_raw_idx.get(s_id)
                    if s_idx is None:
                        continue

                    seq_str = row[seq_col].strip() if seq_col < len(row) else ""
                    arr_str = row[arr_col].strip() if arr_col < len(row) else ""
                    dep_str = row[dep_col].strip() if dep_col < len(row) else ""

                    seq = parse_nonnegative_int(seq_str, "stop_sequence", row_num)
                    arr = parse_gtfs_time(arr_str, row_num)
                    dep = parse_gtfs_time(dep_str, row_num)
                    if arr is None and dep is None:
                        continue
                    if arr is None:
                        arr = dep
                    if dep is None:
                        dep = arr

                    batch.append((t_idx, seq, s_idx, arr, dep))
                    inserted_st += 1
                    if len(batch) >= 50000:
                        tmp_conn.executemany("INSERT INTO st VALUES (?, ?, ?, ?, ?)", batch)
                        batch.clear()

                if batch:
                    tmp_conn.executemany("INSERT INTO st VALUES (?, ?, ?, ?, ?)", batch)
                    batch.clear()
            finally:
                text_s.close()
                raw_s.close()

            tmp_conn.commit()
            print(f"Filtered active stop_times rows: {inserted_st:,}")
            print("Sorting stop_times by trip and sequence...")
            tmp_conn.execute("CREATE INDEX idx_st_trip_seq ON st(t_idx, seq)")
            tmp_conn.commit()

            # Build patterns, deduplicated timing profiles, and per-pattern trips
            pattern_key_to_id: dict[tuple, int] = {}
            pattern_stops_raw: dict[int, tuple[int, ...]] = {}
            pattern_route_dir: dict[int, tuple[str, str]] = {}
            pattern_headsign_counts: dict[int, Counter] = defaultdict(Counter)

            profile_bytes_to_id: dict[bytes, int] = {}
            profile_list: list[tuple[int, int, bytes]] = []  # (profile_id, stop_count, blob)

            pattern_trips: dict[int, list[tuple[int, int, int, int]]] = defaultdict(list)

            used_raw_stop_indices: set[int] = set()
            used_route_ids: set[str] = set()
            sample_checks: list[tuple[int, int, int, int, list[tuple[int, int]]]] = []

            def flush_trip(t_idx: int | None, stops_seq: list[tuple[int, int, int]]) -> None:
                if t_idx is None or len(stops_seq) < 2:
                    return

                r_id, s_idx_cal, dir_id, h_idx = trip_meta[t_idx]
                start_sec = stops_seq[0][2]

                stop_tuple = tuple(item[0] for item in stops_seq)
                p_key = (r_id, dir_id, stop_tuple)
                p_id = pattern_key_to_id.get(p_key)
                if p_id is None:
                    p_id = len(pattern_key_to_id) + 1
                    pattern_key_to_id[p_key] = p_id
                    pattern_stops_raw[p_id] = stop_tuple
                    pattern_route_dir[p_id] = (r_id, dir_id)
                    used_raw_stop_indices.update(stop_tuple)
                    used_route_ids.add(r_id)

                pattern_headsign_counts[p_id][h_idx] += 1

                prof_buf = bytearray()
                prev_dep = start_sec
                for _, arr_sec, dep_sec in stops_seq:
                    encode_svarint(arr_sec - prev_dep, prof_buf)
                    encode_svarint(dep_sec - arr_sec, prof_buf)
                    prev_dep = dep_sec

                prof_bytes = bytes(prof_buf)
                prof_id = profile_bytes_to_id.get(prof_bytes)
                if prof_id is None:
                    prof_id = len(profile_list)
                    profile_bytes_to_id[prof_bytes] = prof_id
                    profile_list.append((prof_id, len(stops_seq), prof_bytes))

                pattern_trips[p_id].append((start_sec, s_idx_cal, prof_id, h_idx))

                # Collect diverse sample trips (including dwell > 0 and overnight >= 86400) for validation
                if len(sample_checks) < 200:
                    has_dwell = any(d > a for _, a, d in stops_seq)
                    is_overnight = start_sec >= 86400
                    if len(sample_checks) < 100 or has_dwell or is_overnight:
                        sample_checks.append(
                            (
                                p_id,
                                start_sec,
                                s_idx_cal,
                                prof_id,
                                [(a, d) for _, a, d in stops_seq],
                            )
                        )

            cur_t_idx: int | None = None
            cur_stops: list[tuple[int, int, int]] = []
            for t_idx, s_idx, arr_sec, dep_sec in tmp_conn.execute(
                "SELECT t_idx, s_idx, arr, dep FROM st ORDER BY t_idx, seq"
            ):
                if t_idx != cur_t_idx:
                    flush_trip(cur_t_idx, cur_stops)
                    cur_t_idx = t_idx
                    cur_stops = []
                cur_stops.append((s_idx, arr_sec, dep_sec))
            flush_trip(cur_t_idx, cur_stops)

            tmp_conn.close()
        finally:
            if tmp_st_path.exists():
                tmp_st_path.unlink()

        if not pattern_key_to_id:
            raise ValueError("No valid transit patterns produced")

        # Preserve parent_station records for every kept stop (transitively)
        kept_raw_stop_indices = set(used_raw_stop_indices)
        queue = list(kept_raw_stop_indices)
        while queue:
            idx = queue.pop()
            parent_id = raw_stops[idx][5]
            if parent_id:
                parent_raw_idx = stop_id_to_raw_idx.get(parent_id)
                if parent_raw_idx is not None and parent_raw_idx not in kept_raw_stop_indices:
                    kept_raw_stop_indices.add(parent_raw_idx)
                    queue.append(parent_raw_idx)

        # Dense stop_idx (0 .. N_stops - 1) and route_idx (0 .. N_routes - 1)
        raw_to_dense_stop: dict[int, int] = {}
        final_stops_rows = []
        for dense_idx, raw_idx in enumerate(sorted(kept_raw_stop_indices)):
            raw_to_dense_stop[raw_idx] = dense_idx
            s_id, s_code, s_name, s_lat, s_lon, parent_st, s_desc, p_code = raw_stops[raw_idx]
            final_stops_rows.append(
                (dense_idx, s_id, s_code, s_name, s_lat, s_lon, parent_st, s_desc, p_code)
            )

        route_id_to_idx: dict[str, int] = {}
        final_routes_rows = []
        used_agency_ids: set[str] = set()
        for dense_r_idx, r_id in enumerate(sorted(used_route_ids)):
            route_id_to_idx[r_id] = dense_r_idx
            agency_id, short_name, long_name, route_type, route_desc = raw_routes[r_id]
            used_agency_ids.add(agency_id)
            final_routes_rows.append(
                (dense_r_idx, r_id, agency_id, short_name, long_name, route_type, route_desc)
            )

        final_agency_rows = [
            (a_id, agencies.get(a_id, ""))
            for a_id in sorted(used_agency_ids)
        ]

        # Build output SQLite database
        output_path.parent.mkdir(parents=True, exist_ok=True)
        if output_path.exists():
            output_path.unlink()

        conn = sqlite3.connect(str(output_path))
        try:
            conn.execute("PRAGMA journal_mode=MEMORY")
            conn.execute("PRAGMA synchronous=OFF")
            conn.execute("PRAGMA page_size=4096")

            conn.execute(
                """
                CREATE TABLE import_metadata (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE agency (
                    agency_id TEXT PRIMARY KEY,
                    agency_name TEXT NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE routes (
                    route_idx INTEGER PRIMARY KEY,
                    route_id TEXT UNIQUE NOT NULL,
                    agency_id TEXT NOT NULL,
                    route_short_name TEXT NOT NULL,
                    route_long_name TEXT NOT NULL,
                    route_type TEXT NOT NULL,
                    route_desc TEXT NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE stops (
                    stop_idx INTEGER PRIMARY KEY,
                    stop_id TEXT UNIQUE NOT NULL,
                    stop_code TEXT NOT NULL,
                    stop_name TEXT NOT NULL,
                    stop_lat REAL,
                    stop_lon REAL,
                    parent_station TEXT NOT NULL,
                    stop_desc TEXT NOT NULL,
                    platform_code TEXT NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE calendar (
                    service_idx INTEGER PRIMARY KEY,
                    weekday_mask INTEGER NOT NULL,
                    start_date INTEGER NOT NULL,
                    end_date INTEGER NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE calendar_dates (
                    service_idx INTEGER NOT NULL,
                    date INTEGER NOT NULL,
                    exception_type INTEGER NOT NULL,
                    PRIMARY KEY (service_idx, date)
                ) WITHOUT ROWID
                """
            )
            conn.execute(
                """
                CREATE TABLE headsigns (
                    headsign_idx INTEGER PRIMARY KEY,
                    text TEXT NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE route_patterns (
                    pattern_id INTEGER PRIMARY KEY,
                    route_idx INTEGER NOT NULL,
                    direction_id TEXT NOT NULL,
                    headsign_idx INTEGER NOT NULL,
                    stop_count INTEGER NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE route_pattern_stops (
                    pattern_id INTEGER NOT NULL,
                    stop_sequence INTEGER NOT NULL,
                    stop_idx INTEGER NOT NULL,
                    PRIMARY KEY (pattern_id, stop_sequence)
                ) WITHOUT ROWID
                """
            )
            conn.execute(
                """
                CREATE TABLE timing_profiles (
                    profile_id INTEGER PRIMARY KEY,
                    stop_count INTEGER NOT NULL,
                    data BLOB NOT NULL
                )
                """
            )
            conn.execute(
                """
                CREATE TABLE pattern_schedules (
                    pattern_id INTEGER PRIMARY KEY,
                    trip_count INTEGER NOT NULL,
                    trips_blob BLOB NOT NULL
                )
                """
            )

            conn.executemany("INSERT INTO agency VALUES (?, ?)", final_agency_rows)
            conn.executemany(
                "INSERT INTO routes VALUES (?, ?, ?, ?, ?, ?, ?)", final_routes_rows
            )
            conn.executemany(
                "INSERT INTO stops VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)", final_stops_rows
            )
            conn.executemany("INSERT INTO calendar VALUES (?, ?, ?, ?)", calendar_rows)
            conn.executemany(
                "INSERT INTO calendar_dates VALUES (?, ?, ?)", calendar_date_rows
            )
            conn.executemany(
                "INSERT INTO headsigns VALUES (?, ?)",
                [(idx, text) for idx, text in enumerate(headsigns)],
            )
            conn.executemany("INSERT INTO timing_profiles VALUES (?, ?, ?)", profile_list)

            pattern_rows = []
            pattern_stop_rows = []
            schedule_rows = []
            total_trips_encoded = 0

            for p_id in sorted(pattern_stops_raw.keys()):
                r_id, dir_id = pattern_route_dir[p_id]
                r_idx = route_id_to_idx[r_id]
                stop_tuple = pattern_stops_raw[p_id]
                top_headsign = pattern_headsign_counts[p_id].most_common(1)[0][0]
                pattern_rows.append((p_id, r_idx, dir_id, top_headsign, len(stop_tuple)))

                for seq_idx, raw_s_idx in enumerate(stop_tuple, start=1):
                    pattern_stop_rows.append((p_id, seq_idx, raw_to_dense_stop[raw_s_idx]))

                trips_for_pattern = pattern_trips[p_id]
                trips_for_pattern.sort()
                blob = bytearray()
                prev_start = 0
                for start_sec, s_idx_cal, prof_id, h_idx in trips_for_pattern:
                    encode_uvarint(start_sec - prev_start, blob)
                    encode_uvarint(s_idx_cal, blob)
                    encode_uvarint(prof_id, blob)
                    encode_uvarint(h_idx, blob)
                    prev_start = start_sec

                schedule_rows.append((p_id, len(trips_for_pattern), bytes(blob)))
                total_trips_encoded += len(trips_for_pattern)

            conn.executemany("INSERT INTO route_patterns VALUES (?, ?, ?, ?, ?)", pattern_rows)
            conn.executemany(
                "INSERT INTO route_pattern_stops VALUES (?, ?, ?)", pattern_stop_rows
            )
            conn.executemany("INSERT INTO pattern_schedules VALUES (?, ?, ?)", schedule_rows)

            metadata = {
                "created_utc": datetime.now(timezone.utc).isoformat(),
                "gtfs_source": gtfs_path.name,
                "gtfs_tables": "agency,routes,stops,calendar,calendar_dates,headsigns,route_patterns,route_pattern_stops,timing_profiles,pattern_schedules",
                "format_version": "6",
                "fast_storage": "true",
                "min_service_date": str(min_date_int),
                "max_service_date": str(max_date_int),
                "stop_count": str(len(final_stops_rows)),
                "route_count": str(len(final_routes_rows)),
                "pattern_count": str(len(pattern_rows)),
                "trip_count": str(total_trips_encoded),
            }
            conn.executemany(
                "INSERT INTO import_metadata (key, value) VALUES (?, ?)",
                metadata.items(),
            )

            print("Creating minimal indexes...")
            conn.execute("CREATE UNIQUE INDEX idx_stops_stop_id ON stops(stop_id)")
            conn.execute("CREATE INDEX idx_stops_code ON stops(stop_code)")
            conn.execute("CREATE INDEX idx_stops_parent ON stops(parent_station)")
            conn.execute("CREATE INDEX idx_stops_lat_lon ON stops(stop_lat, stop_lon)")
            conn.execute("CREATE UNIQUE INDEX idx_routes_route_id ON routes(route_id)")
            conn.execute("CREATE INDEX idx_routes_short_name ON routes(route_short_name)")
            conn.execute("CREATE INDEX idx_patterns_route_idx ON route_patterns(route_idx)")
            conn.execute(
                "CREATE INDEX idx_rps_stop_idx ON route_pattern_stops(stop_idx, pattern_id)"
            )
            conn.execute(
                "CREATE INDEX idx_calendar_dates_range ON calendar(start_date, end_date)"
            )
            conn.commit()

            print("Compacting database (VACUUM & ANALYZE)...")
            conn.execute("VACUUM")
            conn.execute("ANALYZE")

            # Integrity and exact timing round-trip verification
            integrity = conn.execute("PRAGMA integrity_check").fetchone()[0]
            if integrity != "ok":
                raise RuntimeError(f"SQLite integrity check failed: {integrity}")

            p_count_db = conn.execute("SELECT COUNT(*) FROM route_patterns").fetchone()[0]
            s_count_db = conn.execute("SELECT COUNT(*) FROM pattern_schedules").fetchone()[0]
            if p_count_db == 0 or p_count_db != s_count_db:
                raise RuntimeError(
                    f"Pattern/schedule count mismatch: {p_count_db} vs {s_count_db}"
                )

            for p_id, expected_start, expected_cal, expected_prof, expected_times in sample_checks:
                row = conn.execute(
                    "SELECT trip_count, trips_blob FROM pattern_schedules WHERE pattern_id = ?",
                    (p_id,),
                ).fetchone()
                if not row:
                    raise RuntimeError(f"Missing schedule for pattern {p_id}")
                t_count, t_blob = row
                pos = 0
                prev_start = 0
                matched = False
                for _ in range(t_count):
                    d_start, pos = decode_uvarint(t_blob, pos)
                    s_cal, pos = decode_uvarint(t_blob, pos)
                    pr_id, pos = decode_uvarint(t_blob, pos)
                    _, pos = decode_uvarint(t_blob, pos)
                    cur_start = prev_start + d_start
                    prev_start = cur_start
                    if cur_start == expected_start and s_cal == expected_cal and pr_id == expected_prof:
                        matched = True
                        break
                if not matched:
                    raise RuntimeError(f"Trip verification failed for pattern {p_id}")

                prof_row = conn.execute(
                    "SELECT stop_count, data FROM timing_profiles WHERE profile_id = ?",
                    (expected_prof,),
                ).fetchone()
                if not prof_row:
                    raise RuntimeError(f"Missing timing profile {expected_prof}")
                k_stops, p_blob = prof_row
                if k_stops != len(expected_times):
                    raise RuntimeError("Profile stop count mismatch")
                p_pos = 0
                prev_dep = expected_start
                for stop_idx in range(k_stops):
                    d_arr, p_pos = decode_svarint(p_blob, p_pos)
                    dwell, p_pos = decode_svarint(p_blob, p_pos)
                    arr_val = prev_dep + d_arr
                    dep_val = arr_val + dwell
                    prev_dep = dep_val
                    if (arr_val, dep_val) != expected_times[stop_idx]:
                        raise RuntimeError(
                            f"Exact time mismatch on profile {expected_prof}: "
                            f"got {(arr_val, dep_val)}, expected {expected_times[stop_idx]}"
                        )

            print(
                f"Done! Stops: {len(final_stops_rows):,}, Routes: {len(final_routes_rows):,}, "
                f"Patterns: {len(pattern_rows):,}, Profiles: {len(profile_list):,}, "
                f"Trips: {total_trips_encoded:,}"
            )
            print(f"Database created: {output_path} ({output_path.stat().st_size:,} bytes)")
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gtfs", required=True, help="Path to GTFS ZIP archive")
    parser.add_argument("--output", required=True, help="Path to output SQLite database")
    args = parser.parse_args()

    gtfs_path = Path(args.gtfs)
    output_path = Path(args.output)

    if not gtfs_path.is_file():
        raise FileNotFoundError(f"GTFS ZIP not found: {gtfs_path}")

    build_database(gtfs_path, output_path)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"BUILD FAILED: {error}", file=sys.stderr)
        sys.exit(1)
