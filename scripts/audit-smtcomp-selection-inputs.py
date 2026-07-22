#!/usr/bin/env python3
"""Verify pinned SMT-COMP inputs and publish a selection-free eligibility audit."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import sys
import urllib.error
import urllib.request
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterator, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.smtcomp_repro.official_selection import (
    HistoricalAccumulator,
    SelectionAuditError,
    adapt_official_benchmark_row,
    adapt_official_result_row,
    adapt_official_submissions,
    canonical_json_bytes,
    competitive_logics,
    division_cap,
    extract_official_logics,
    extract_removed_benchmark_ids,
    extract_single_query_divisions,
    normalize_benchmark,
    sha256_bytes,
)


SCHEMA = "axeyum-smtcomp-selection-input-audit-v1"
CHUNK = 1024 * 1024


class InputAuditError(ValueError):
    """A live input or selection-free audit artifact failed closed."""


class _JsonStream:
    """Incrementally decode one UTF-8 JSON stream without external packages."""

    def __init__(self, source: Any, *, chunk_size: int = 1024 * 1024) -> None:
        self.source = source
        self.chunk_size = chunk_size
        self.buffer = ""
        self.position = 0
        self.eof = False
        self.decoder = json.JSONDecoder()

    def _compact(self) -> None:
        if self.position > self.chunk_size:
            self.buffer = self.buffer[self.position :]
            self.position = 0

    def _fill(self) -> bool:
        if self.eof:
            return False
        self._compact()
        value = self.source.read(self.chunk_size)
        if value == "":
            self.eof = True
            return False
        self.buffer += value
        return True

    def skip_whitespace(self) -> None:
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position].isspace():
                self.position += 1
            if self.position < len(self.buffer) or not self._fill():
                return

    def peek(self) -> str | None:
        self.skip_whitespace()
        if self.position >= len(self.buffer) and not self._fill():
            return None
        self.skip_whitespace()
        return self.buffer[self.position] if self.position < len(self.buffer) else None

    def expect(self, expected: str) -> None:
        actual = self.peek()
        if actual != expected:
            raise InputAuditError(f"expected JSON {expected!r}, got {actual!r}")
        self.position += 1

    def value(self) -> Any:
        self.skip_whitespace()
        while True:
            try:
                value, end = self.decoder.raw_decode(self.buffer, self.position)
            except json.JSONDecodeError as error:
                if self._fill():
                    continue
                raise InputAuditError("truncated or malformed streamed JSON value") from error
            self.position = end
            return value

    def array(self) -> Iterator[Any]:
        self.expect("[")
        if self.peek() == "]":
            self.position += 1
            return
        while True:
            yield self.value()
            separator = self.peek()
            if separator == ",":
                self.position += 1
                continue
            if separator == "]":
                self.position += 1
                return
            raise InputAuditError(f"invalid streamed JSON array separator: {separator!r}")

    def skip_value(self) -> None:
        if self.peek() == "[":
            for _ in self.array():
                pass
        else:
            self.value()


def iter_gzip_object_array(path: Path, key: str) -> Iterator[Any]:
    """Yield one named top-level JSON array from a gzip file incrementally."""
    try:
        with gzip.open(path, "rt", encoding="utf-8", newline="") as source:
            stream = _JsonStream(source)
            stream.expect("{")
            found = False
            if stream.peek() == "}":
                stream.position += 1
            else:
                while True:
                    object_key = stream.value()
                    if not isinstance(object_key, str):
                        raise InputAuditError("streamed JSON object key is not a string")
                    stream.expect(":")
                    if object_key == key:
                        if found:
                            raise InputAuditError(f"duplicate streamed JSON key: {key}")
                        found = True
                        yield from stream.array()
                    else:
                        stream.skip_value()
                    separator = stream.peek()
                    if separator == ",":
                        stream.position += 1
                        continue
                    if separator == "}":
                        stream.position += 1
                        break
                    raise InputAuditError(f"invalid streamed JSON object separator: {separator!r}")
            if not found:
                raise InputAuditError(f"streamed JSON key not found: {key}")
            if stream.peek() is not None:
                raise InputAuditError("trailing data after streamed JSON object")
    except (gzip.BadGzipFile, UnicodeDecodeError, OSError) as error:
        raise InputAuditError(f"cannot stream {path}") from error


def _download(entry: Mapping[str, Any], root: Path) -> dict[str, Any]:
    relative = Path(entry["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise InputAuditError(f"unsafe staged input path: {entry['path']}")
    target = root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + ".part")
    if target.exists() or temporary.exists():
        raise InputAuditError(f"refusing to overwrite staged input: {entry['path']}")
    digest = hashlib.sha256()
    size = 0
    request = urllib.request.Request(
        entry["url"],
        headers={"User-Agent": "axeyum-selection-input-audit/1"},
    )
    with urllib.request.urlopen(request, timeout=180) as response, temporary.open("xb") as output:
        final_url = response.geturl()
        while True:
            data = response.read(CHUNK)
            if not data:
                break
            output.write(data)
            digest.update(data)
            size += len(data)
        output.flush()
        os.fsync(output.fileno())
    actual_sha = digest.hexdigest()
    if size != entry["bytes"] or actual_sha != entry["sha256"]:
        raise InputAuditError(
            f"download identity drift for {entry['path']}: "
            f"bytes={size}/{entry['bytes']} sha256={actual_sha}/{entry['sha256']}"
        )
    os.replace(temporary, target)
    _fsync_directory(target.parent)
    return {
        "bytes": size,
        "final_url": final_url,
        "path": entry["path"],
        "sha256": actual_sha,
        "url": entry["url"],
    }


def _write_new(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())
    _fsync_directory(path.parent)


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _manifest_entry(entry: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "bytes": entry["bytes"],
        "path": entry["path"],
        "sha256": entry["sha256"],
        "url": entry["url"],
    }


def _input_entries(authority: Mapping[str, Any]) -> list[dict[str, Any]]:
    entries = [_manifest_entry(row) for row in authority["organizer"]["source_files"]]
    entries.extend(_manifest_entry(row) for row in authority["submissions"])
    entries.append(_manifest_entry(authority["benchmark_metadata"]))
    entries.extend(_manifest_entry(row) for row in authority["historical_results"])
    entries.append(
        {
            "bytes": authority["rules"]["bytes"],
            "path": "rules/2026-rules.pdf",
            "sha256": authority["rules"]["sha256"],
            "url": authority["rules"]["url"],
        }
    )
    paths = [row["path"] for row in entries]
    if len(paths) != len(set(paths)):
        raise InputAuditError("authority inputs contain a duplicate staged path")
    return sorted(entries, key=lambda row: row["path"])


def _load_submission_documents(authority: Mapping[str, Any], input_root: Path) -> list[dict[str, Any]]:
    documents = []
    for row in authority["submissions"]:
        try:
            document = json.loads((input_root / row["path"]).read_bytes())
        except (json.JSONDecodeError, OSError, UnicodeDecodeError) as error:
            raise InputAuditError(f"cannot decode submission: {row['path']}") from error
        if not isinstance(document, dict):
            raise InputAuditError(f"submission is not an object: {row['path']}")
        documents.append(document)
    return documents


def run(authority_path: Path, output_dir: Path) -> dict[str, Any]:
    """Execute the frozen selection-free input audit in a new directory."""
    authority_raw = authority_path.read_bytes()
    try:
        authority = json.loads(authority_raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise InputAuditError("cannot decode authority manifest") from error
    if authority_raw != canonical_json_bytes(authority):
        raise InputAuditError("authority manifest is not canonical JSON")
    if authority.get("schema") != "axeyum-smtcomp-official-selection-authority-v1":
        raise InputAuditError("wrong authority manifest schema")
    output_dir.mkdir(parents=True, exist_ok=False)
    _fsync_directory(output_dir.parent)
    input_root = output_dir / "inputs"
    input_root.mkdir()
    _fsync_directory(output_dir)

    downloads = []
    for entry in _input_entries(authority):
        downloads.append(_download(entry, input_root))
        print(f"DOWNLOAD_OK|{entry['path']}|bytes={entry['bytes']}", flush=True)
    downloads_doc = {
        "authority_sha256": sha256_bytes(authority_raw),
        "entries": downloads,
        "schema": SCHEMA,
    }
    downloads_bytes = canonical_json_bytes(downloads_doc)
    _write_new(output_dir / "downloads.json", downloads_bytes)

    defs_path = input_root / "smtcomp/defs.py"
    defs_source = defs_path.read_bytes()
    divisions = extract_single_query_divisions(defs_source)
    all_logics = extract_official_logics(defs_source)
    removed_ids = extract_removed_benchmark_ids(defs_source)
    submissions = adapt_official_submissions(
        _load_submission_documents(authority, input_root),
        divisions,
        all_logics,
    )
    competitive = competitive_logics(submissions)
    competitive_submissions = [row for row in submissions if row["competitive"]]
    seed_sum = sum(row["seed"] for row in competitive_submissions)
    seed = seed_sum % authority["policy"]["submission_seed_modulus"] + authority["policy"]["nyse_seed"]
    if len(submissions) != 51 or len(competitive_submissions) != 36 or seed != 22_731_074:
        raise InputAuditError("normalized submission count or seed drift")

    benchmark_path = input_root / authority["benchmark_metadata"]["path"]
    known_ids: set[str] = set()
    metadata_count = 0
    metadata_logics: set[str] = set()
    for official_row in iter_gzip_object_array(benchmark_path, "non_incremental"):
        normalized = normalize_benchmark(adapt_official_benchmark_row(official_row))
        benchmark_id = normalized["benchmark_id"]
        if benchmark_id in known_ids:
            raise InputAuditError(f"duplicate official benchmark ID: {benchmark_id}")
        known_ids.add(benchmark_id)
        metadata_logics.add(normalized["logic"])
        metadata_count += 1
    if metadata_count != authority["benchmark_metadata"]["non_incremental_rows"]:
        raise InputAuditError("streamed official metadata count drift")
    if len(metadata_logics) != authority["benchmark_metadata"]["non_incremental_logics"]:
        raise InputAuditError("streamed official logic count drift")
    if not removed_ids <= known_ids or len(removed_ids) != authority["policy"]["removed_benchmark_count"]:
        raise InputAuditError("official removal table does not match metadata")
    print(f"METADATA_OK|rows={metadata_count}|logics={len(metadata_logics)}", flush=True)

    historical = HistoricalAccumulator(known_ids)
    historical_counts = []
    for row in authority["historical_results"]:
        path = input_root / row["path"]
        count = 0
        for official_result in iter_gzip_object_array(path, "results"):
            historical.add(adapt_official_result_row(official_result, year=row["year"]))
            count += 1
        historical_counts.append({"rows": count, "year": row["year"]})
        print(f"HISTORICAL_OK|year={row['year']}|rows={count}", flush=True)

    eligibility_path = output_dir / "eligibility.jsonl"
    eligibility_digest = hashlib.sha256()
    reason_counts: dict[str, int] = defaultdict(int)
    logic_counts: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    prior_id: str | None = None
    new_count = 0
    with eligibility_path.open("xb") as output:
        for official_row in iter_gzip_object_array(benchmark_path, "non_incremental"):
            benchmark = normalize_benchmark(adapt_official_benchmark_row(official_row))
            benchmark_id = benchmark["benchmark_id"]
            if prior_id is not None and benchmark_id <= prior_id:
                raise InputAuditError("official benchmark metadata is not in strict path order")
            prior_id = benchmark_id
            facts = historical.facts_for(benchmark_id)
            is_new = benchmark["family"][0].startswith(authority["policy"]["new_family_prefix"])
            new_count += is_new
            logic = benchmark["logic"]
            logic_counts[logic]["metadata"] += 1
            if benchmark_id in removed_ids:
                reason = "excluded-explicit-removal"
                logic_counts[logic]["explicit_removal"] += 1
            elif logic not in competitive:
                reason = "excluded-noncompetitive-logic"
                logic_counts[logic]["noncompetitive"] += 1
            elif facts["trivial"]:
                reason = "excluded-trivial"
                logic_counts[logic]["trivial"] += 1
            elif is_new:
                reason = "eligible-new"
                logic_counts[logic]["eligible_new"] += 1
            else:
                reason = "eligible-old"
                logic_counts[logic]["eligible_old"] += 1
            reason_counts[reason] += 1
            ledger_row = {
                **benchmark,
                "historical": facts,
                "is_new": is_new,
                "logic_competitive": logic in competitive,
                "reason": reason,
            }
            encoded = canonical_json_bytes(ledger_row)
            output.write(encoded)
            eligibility_digest.update(encoded)
        output.flush()
        os.fsync(output.fileno())
    _fsync_directory(eligibility_path.parent)
    if new_count != authority["benchmark_metadata"]["new_non_incremental_rows"]:
        raise InputAuditError("streamed new-family count drift")
    if sum(reason_counts.values()) != metadata_count:
        raise InputAuditError("eligibility reasons do not partition metadata")

    logic_summary = []
    for logic in sorted(metadata_logics):
        counts = logic_counts[logic]
        eligible = counts["eligible_new"] + counts["eligible_old"]
        cap = division_cap(eligible) if logic in competitive else 0
        selected_new_quota = min(cap, counts["eligible_new"])
        selected_old_quota = cap - selected_new_quota
        if (
            counts["explicit_removal"]
            + counts["noncompetitive"]
            + counts["trivial"]
            + eligible
            != counts["metadata"]
        ):
            raise InputAuditError(f"per-logic eligibility counts do not balance: {logic}")
        logic_summary.append(
            {
                "cap": cap,
                "eligible_new": counts["eligible_new"],
                "eligible_old": counts["eligible_old"],
                "explicit_removal": counts["explicit_removal"],
                "logic": logic,
                "metadata": counts["metadata"],
                "noncompetitive": counts["noncompetitive"],
                "selected_new_quota": selected_new_quota,
                "selected_old_quota": selected_old_quota,
                "trivial": counts["trivial"],
            }
        )

    summary = {
        "authority_sha256": sha256_bytes(authority_raw),
        "competitive_logics": sorted(competitive),
        "downloads_sha256": sha256_bytes(downloads_bytes),
        "eligibility_bytes": eligibility_path.stat().st_size,
        "eligibility_sha256": eligibility_digest.hexdigest(),
        "historical_ignored_rows": historical.ignored_rows,
        "historical_rows": historical.rows,
        "historical_rows_by_year": historical_counts,
        "logic_summary": logic_summary,
        "metadata_rows": metadata_count,
        "new_rows": new_count,
        "reason_counts": dict(sorted(reason_counts.items())),
        "removed_ids": sorted(removed_ids),
        "schema": SCHEMA,
        "seed": seed,
        "selection_observed": False,
        "submissions": len(submissions),
    }
    summary_bytes = canonical_json_bytes(summary)
    _write_new(output_dir / "summary.json", summary_bytes)
    completion_payload = {
        "artifacts": {
            "downloads.json": sha256_bytes(downloads_bytes),
            "eligibility.jsonl": eligibility_digest.hexdigest(),
            "summary.json": sha256_bytes(summary_bytes),
        },
        "authority_sha256": sha256_bytes(authority_raw),
        "schema": SCHEMA,
        "selection_observed": False,
        "status": "complete",
    }
    completion = {
        **completion_payload,
        "payload_sha256": sha256_bytes(canonical_json_bytes(completion_payload)),
    }
    _write_new(output_dir / "input-audit.json", canonical_json_bytes(completion))
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--authority",
        type=Path,
        default=Path("docs/plan/smtcomp-official-selection-authority-v1.json"),
    )
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    try:
        summary = run(args.authority, args.out)
    except (
        InputAuditError,
        SelectionAuditError,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        urllib.error.URLError,
    ) as error:
        print(f"SMTCOMP_SELECTION_INPUT_AUDIT_ERROR|{error}", file=sys.stderr)
        return 1
    print(
        "SMTCOMP_SELECTION_INPUT_AUDIT|"
        f"metadata={summary['metadata_rows']}|"
        f"historical={summary['historical_rows']}|"
        f"competitive_logics={len(summary['competitive_logics'])}|"
        f"seed={summary['seed']}|"
        "selection_observed=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
