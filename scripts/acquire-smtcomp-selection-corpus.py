#!/usr/bin/env python3
"""Acquire and byte-audit the ADR-0356 SMT-LIB 2025.08.04 corpus."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import sqlite3
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.smtcomp_repro.corpus_acquisition import (
    CorpusAcquisitionError,
    extract_tar_stream,
    hash_file,
    inventory_logic_tree,
    validate_corpus_roots,
)
from scripts.smtcomp_repro.official_selection import canonical_json_bytes, sha256_bytes


SCHEMA = "axeyum-smtcomp-selection-corpus-acquisition-v1"
CHUNK = 1024 * 1024


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _publish(path: Path, data: bytes) -> None:
    if path.exists():
        if path.is_symlink() or path.read_bytes() != data:
            raise CorpusAcquisitionError(f"existing artifact differs: {path}")
        return
    temporary = path.with_name(path.name + ".part")
    if temporary.exists():
        temporary.unlink()
    with temporary.open("xb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())
    os.replace(temporary, path)
    _fsync_directory(path.parent)


def _canonical_document(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or raw != canonical_json_bytes(value):
        raise CorpusAcquisitionError(f"noncanonical JSON document: {path}")
    return value


def _verify_input_audit(root: Path, authority_raw: bytes) -> tuple[dict[str, Any], Path]:
    completion_path = root / "input-audit.json"
    completion = _canonical_document(completion_path)
    if (
        completion.get("schema") != "axeyum-smtcomp-selection-input-audit-v1"
        or completion.get("status") != "complete"
        or completion.get("selection_observed") is not False
        or completion.get("authority_sha256") != sha256_bytes(authority_raw)
    ):
        raise CorpusAcquisitionError("S1 input-audit completion identity differs")
    payload = {key: value for key, value in completion.items() if key != "payload_sha256"}
    if sha256_bytes(canonical_json_bytes(payload)) != completion.get("payload_sha256"):
        raise CorpusAcquisitionError("S1 input-audit payload hash differs")
    for name, expected in completion.get("artifacts", {}).items():
        artifact = root / name
        if artifact.is_symlink() or not artifact.is_file():
            raise CorpusAcquisitionError(f"missing S1 input-audit artifact: {name}")
        if sha256_bytes(artifact.read_bytes()) != expected:
            raise CorpusAcquisitionError(f"S1 input-audit artifact hash differs: {name}")
    summary = _canonical_document(root / "summary.json")
    if summary.get("metadata_rows") != 450_472 or summary.get("selection_observed") is not False:
        raise CorpusAcquisitionError("S1 input-audit summary differs")
    return completion, root / "eligibility.jsonl"


def _safe_release_name(value: Any) -> str:
    if not isinstance(value, str) or not value or Path(value).name != value or value in {".", ".."}:
        raise CorpusAcquisitionError(f"unsafe release filename: {value!r}")
    return value


def _resolve_final_url(url: str) -> str:
    request = urllib.request.Request(
        url,
        method="HEAD",
        headers={"User-Agent": "axeyum-corpus-acquisition/1"},
    )
    with urllib.request.urlopen(request, timeout=180) as response:
        return response.geturl()


def _download_one(entry: Mapping[str, Any], output_root: Path) -> dict[str, Any]:
    name = _safe_release_name(entry["name"])
    target = output_root / "downloads" / name
    partial = target.with_name(target.name + ".part")
    evidence_path = output_root / "download-evidence" / f"{name}.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    evidence_path.parent.mkdir(parents=True, exist_ok=True)
    expected_bytes = entry["bytes"]
    expected_md5 = entry["md5"]
    if isinstance(expected_bytes, bool) or not isinstance(expected_bytes, int) or expected_bytes < 0:
        raise CorpusAcquisitionError(f"invalid release byte count: {name}")
    if not isinstance(expected_md5, str) or len(expected_md5) != 32:
        raise CorpusAcquisitionError(f"invalid release MD5: {name}")

    final_url: str | None = None
    resumed_from = partial.stat().st_size if partial.exists() else 0
    if target.exists():
        if partial.exists():
            raise CorpusAcquisitionError(f"both final and partial download exist: {name}")
    else:
        for attempt in range(5):
            offset = partial.stat().st_size if partial.exists() else 0
            if offset > expected_bytes:
                raise CorpusAcquisitionError(f"oversized partial download: {name}")
            if offset == expected_bytes:
                break
            headers = {"User-Agent": "axeyum-corpus-acquisition/1"}
            if offset:
                headers["Range"] = f"bytes={offset}-"
            request = urllib.request.Request(entry["url"], headers=headers)
            try:
                with urllib.request.urlopen(request, timeout=180) as response:
                    status = response.getcode()
                    if offset:
                        content_range = response.headers.get("Content-Range", "")
                        if status != 206 or not content_range.startswith(f"bytes {offset}-"):
                            raise CorpusAcquisitionError(
                                f"server did not honor byte resume for {name}: {status} {content_range!r}"
                            )
                    final_url = response.geturl()
                    mode = "ab" if offset else "xb"
                    with partial.open(mode) as output:
                        while data := response.read(CHUNK):
                            output.write(data)
                        output.flush()
                        os.fsync(output.fileno())
                if partial.stat().st_size == expected_bytes:
                    break
            except (OSError, urllib.error.URLError) as error:
                if attempt == 4:
                    raise CorpusAcquisitionError(f"download failed after retries: {name}") from error
                time.sleep(min(2**attempt, 8))
        if not partial.exists() or partial.stat().st_size != expected_bytes:
            raise CorpusAcquisitionError(f"download byte count differs: {name}")
        size, md5, sha256 = hash_file(partial)
        if size != expected_bytes or md5 != expected_md5:
            raise CorpusAcquisitionError(
                f"download identity differs: {name} bytes={size}/{expected_bytes} md5={md5}/{expected_md5}"
            )
        os.replace(partial, target)
        _fsync_directory(target.parent)

    size, md5, sha256 = hash_file(target)
    if size != expected_bytes or md5 != expected_md5:
        raise CorpusAcquisitionError(f"retained download identity differs: {name}")
    if evidence_path.exists():
        evidence = _canonical_document(evidence_path)
        expected_evidence = {
            "bytes": size,
            "final_url": evidence.get("final_url"),
            "md5": md5,
            "name": name,
            "resumed_from": evidence.get("resumed_from"),
            "schema": SCHEMA,
            "sha256": sha256,
            "url": entry["url"],
        }
        if evidence != expected_evidence:
            raise CorpusAcquisitionError(f"retained download evidence differs: {name}")
        return evidence
    if final_url is None:
        final_url = _resolve_final_url(entry["url"])
    evidence = {
        "bytes": size,
        "final_url": final_url,
        "md5": md5,
        "name": name,
        "resumed_from": resumed_from,
        "schema": SCHEMA,
        "sha256": sha256,
        "url": entry["url"],
    }
    _publish(evidence_path, canonical_json_bytes(evidence))
    return evidence


def _load_metadata(connection: sqlite3.Connection, eligibility_path: Path) -> int:
    connection.execute(
        "CREATE TABLE files ("
        "benchmark_id TEXT PRIMARY KEY, logic TEXT NOT NULL, family TEXT NOT NULL, "
        "name TEXT NOT NULL, status TEXT NOT NULL, asserts INTEGER NOT NULL, "
        "archive TEXT, bytes INTEGER, sha256 TEXT)"
    )
    count = 0
    batch = []
    with eligibility_path.open("rb") as source:
        for raw in source:
            row = json.loads(raw)
            batch.append(
                (
                    row["benchmark_id"],
                    row["logic"],
                    json.dumps(row["family"], ensure_ascii=False, separators=(",", ":")),
                    row["name"],
                    row["status"],
                    row["asserts"],
                )
            )
            count += 1
            if len(batch) == 10_000:
                connection.executemany(
                    "INSERT INTO files (benchmark_id,logic,family,name,status,asserts) "
                    "VALUES (?,?,?,?,?,?)",
                    batch,
                )
                batch.clear()
    if batch:
        connection.executemany(
            "INSERT INTO files (benchmark_id,logic,family,name,status,asserts) VALUES (?,?,?,?,?,?)",
            batch,
        )
    connection.commit()
    return count


def _recorder(connection: sqlite3.Connection, archive: str, logic: str):
    def record(benchmark_id: str, size: int, sha256: str) -> None:
        cursor = connection.execute(
            "UPDATE files SET archive=?, bytes=?, sha256=? "
            "WHERE benchmark_id=? AND logic=? AND archive IS NULL",
            (archive, size, sha256, benchmark_id, logic),
        )
        if cursor.rowcount != 1:
            existing = connection.execute(
                "SELECT logic,archive FROM files WHERE benchmark_id=?", (benchmark_id,)
            ).fetchone()
            if existing is None:
                raise CorpusAcquisitionError(f"archive contains extra benchmark: {benchmark_id}")
            raise CorpusAcquisitionError(
                f"archive benchmark is duplicated or in the wrong logic: {benchmark_id} {existing!r}"
            )

    return record


def _extract_archive(
    archive_path: Path,
    corpus_root: Path,
    scratch_root: Path,
    logic: str,
    connection: sqlite3.Connection,
) -> tuple[int, int, bool]:
    target = corpus_root / "non-incremental" / logic
    recorder = _recorder(connection, archive_path.name, logic)
    if target.exists():
        with connection:
            files, total_bytes = inventory_logic_tree(corpus_root, logic, recorder)
        return files, total_bytes, True

    staging = scratch_root / logic
    if staging.exists():
        failed = scratch_root / f"{logic}.failed-{time.time_ns()}"
        os.replace(staging, failed)
    scratch_root.mkdir(parents=True, exist_ok=True)
    process = subprocess.Popen(
        ["zstd", "-dc", "--", str(archive_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdout is not None
    try:
        connection.execute("BEGIN")
        files, total_bytes = extract_tar_stream(process.stdout, staging, logic, recorder)
        process.stdout.close()
        stderr = process.stderr.read() if process.stderr is not None else b""
        return_code = process.wait()
        if return_code != 0:
            raise CorpusAcquisitionError(
                f"zstd failed for {archive_path.name}: {stderr.decode('utf-8', 'replace')[-1000:]}"
            )
        validate_corpus_roots(staging, {logic})
        target.parent.mkdir(parents=True, exist_ok=True)
        os.replace(staging / "non-incremental" / logic, target)
        connection.commit()
    except BaseException:
        connection.rollback()
        if process.poll() is None:
            process.kill()
        process.communicate()
        raise
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    return files, total_bytes, False


def _write_corpus_ledger(connection: sqlite3.Connection, path: Path) -> tuple[int, str, int]:
    temporary = path.with_name(path.name + ".part")
    if temporary.exists():
        temporary.unlink()
    digest = hashlib.sha256()
    size = 0
    count = 0
    with temporary.open("xb") as output:
        cursor = connection.execute(
            "SELECT benchmark_id,logic,family,name,status,asserts,archive,bytes,sha256 "
            "FROM files ORDER BY benchmark_id"
        )
        for benchmark_id, logic, family, name, status, asserts, archive, byte_count, sha256 in cursor:
            row = {
                "archive": archive,
                "asserts": asserts,
                "benchmark_id": benchmark_id,
                "bytes": byte_count,
                "family": json.loads(family),
                "logic": logic,
                "name": name,
                "sha256": sha256,
                "status": status,
            }
            encoded = canonical_json_bytes(row)
            output.write(encoded)
            digest.update(encoded)
            size += len(encoded)
            count += 1
        output.flush()
        os.fsync(output.fileno())
    if path.exists():
        existing_size, _, existing_sha = hash_file(path)
        if existing_size != size or existing_sha != digest.hexdigest():
            raise CorpusAcquisitionError("existing corpus ledger differs")
        temporary.unlink()
    else:
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    return size, digest.hexdigest(), count


def run(
    authority_path: Path,
    input_audit_root: Path,
    output_root: Path,
    *,
    resume: bool,
    workers: int,
) -> dict[str, Any]:
    authority_raw = authority_path.read_bytes()
    authority = json.loads(authority_raw)
    if authority_raw != canonical_json_bytes(authority):
        raise CorpusAcquisitionError("authority manifest is not canonical")
    archives = authority.get("corpus_release", {}).get("archives")
    if (
        authority.get("schema") != "axeyum-smtcomp-official-selection-authority-v1"
        or not isinstance(archives, list)
        or len(archives) != 90
        or sum(row["bytes"] for row in archives) != 4_890_207_406
    ):
        raise CorpusAcquisitionError("authority release identity differs")
    names = [_safe_release_name(row["name"]) for row in archives]
    if names != sorted(names) or len(names) != len(set(names)):
        raise CorpusAcquisitionError("authority release filenames are not unique and sorted")
    logic_archives = [row for row in archives if row["name"].endswith(".tar.zst")]
    expected_logics = {row["name"][: -len(".tar.zst")] for row in logic_archives}
    if len(logic_archives) != 89 or len(expected_logics) != 89:
        raise CorpusAcquisitionError("authority logic archive identity differs")

    input_completion, eligibility_path = _verify_input_audit(input_audit_root, authority_raw)
    if output_root.exists():
        if not resume or output_root.is_symlink() or not output_root.is_dir():
            raise CorpusAcquisitionError("output exists without a valid --resume request")
        if (output_root / "corpus-audit.json").exists():
            raise CorpusAcquisitionError("corpus acquisition is already complete")
    else:
        output_root.mkdir(parents=True)
        _fsync_directory(output_root.parent)

    if isinstance(workers, bool) or not isinstance(workers, int) or not 1 <= workers <= 16:
        raise CorpusAcquisitionError("download workers must be in 1..16")
    evidence: list[dict[str, Any]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures = {executor.submit(_download_one, row, output_root): row for row in archives}
        for future in concurrent.futures.as_completed(futures):
            row = futures[future]
            result = future.result()
            evidence.append(result)
            print(f"CORPUS_DOWNLOAD_OK|{row['name']}|bytes={row['bytes']}", flush=True)
    evidence.sort(key=lambda row: row["name"])
    archives_document = {
        "authority_sha256": sha256_bytes(authority_raw),
        "entries": evidence,
        "schema": SCHEMA,
    }
    archives_bytes = canonical_json_bytes(archives_document)
    _publish(output_root / "archives.json", archives_bytes)

    database = output_root / "corpus-index.sqlite3"
    for suffix in ("", "-journal", "-shm", "-wal"):
        candidate = Path(str(database) + suffix)
        if candidate.exists():
            candidate.unlink()
    connection = sqlite3.connect(database)
    connection.execute("PRAGMA synchronous=FULL")
    metadata_rows = _load_metadata(connection, eligibility_path)
    if metadata_rows != 450_472:
        raise CorpusAcquisitionError(f"S1 eligibility row count differs: {metadata_rows}")

    corpus_root = output_root / "corpus"
    corpus_root.mkdir(exist_ok=True)
    scratch_root = output_root / "extracting"
    logic_summary = []
    for row in logic_archives:
        logic = row["name"][: -len(".tar.zst")]
        files, total_bytes, resumed_tree = _extract_archive(
            output_root / "downloads" / row["name"],
            corpus_root,
            scratch_root,
            logic,
            connection,
        )
        logic_summary.append(
            {
                "archive": row["name"],
                "bytes": total_bytes,
                "files": files,
                "logic": logic,
            }
        )
        print(
            f"CORPUS_EXTRACT_OK|{logic}|files={files}|bytes={total_bytes}|"
            f"resumed_tree={str(resumed_tree).lower()}",
            flush=True,
        )

    validate_corpus_roots(corpus_root, expected_logics)
    missing = connection.execute("SELECT COUNT(*) FROM files WHERE archive IS NULL").fetchone()[0]
    actual = connection.execute("SELECT COUNT(*) FROM files WHERE archive IS NOT NULL").fetchone()[0]
    corpus_bytes = connection.execute("SELECT SUM(bytes) FROM files").fetchone()[0]
    if missing != 0 or actual != metadata_rows:
        raise CorpusAcquisitionError(
            f"metadata/tree bijection differs: metadata={metadata_rows} actual={actual} missing={missing}"
        )
    ledger_bytes, ledger_sha256, ledger_rows = _write_corpus_ledger(
        connection, output_root / "corpus.jsonl"
    )
    if ledger_rows != metadata_rows:
        raise CorpusAcquisitionError("corpus ledger row count differs")
    connection.close()
    database.unlink()
    for suffix in ("-journal", "-shm", "-wal"):
        candidate = Path(str(database) + suffix)
        if candidate.exists():
            candidate.unlink()

    summary = {
        "archive_count": len(archives),
        "archive_download_bytes": sum(row["bytes"] for row in evidence),
        "archives_sha256": sha256_bytes(archives_bytes),
        "authority_sha256": sha256_bytes(authority_raw),
        "corpus_bytes": corpus_bytes,
        "corpus_ledger_bytes": ledger_bytes,
        "corpus_ledger_sha256": ledger_sha256,
        "corpus_rows": ledger_rows,
        "input_audit_completion_sha256": sha256_bytes(
            canonical_json_bytes(input_completion)
        ),
        "logic_archives": logic_summary,
        "logic_count": len(expected_logics),
        "schema": SCHEMA,
        "selection_observed": False,
    }
    summary_bytes = canonical_json_bytes(summary)
    _publish(output_root / "summary.json", summary_bytes)
    completion_payload = {
        "artifacts": {
            "archives.json": sha256_bytes(archives_bytes),
            "corpus.jsonl": ledger_sha256,
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
    _publish(output_root / "corpus-audit.json", canonical_json_bytes(completion))
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--authority",
        type=Path,
        default=Path("docs/plan/smtcomp-official-selection-authority-v1.json"),
    )
    parser.add_argument("--input-audit", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    try:
        summary = run(
            args.authority,
            args.input_audit,
            args.out,
            resume=args.resume,
            workers=args.workers,
        )
    except (
        CorpusAcquisitionError,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        sqlite3.Error,
        subprocess.SubprocessError,
        urllib.error.URLError,
    ) as error:
        print(f"SMTCOMP_CORPUS_ACQUISITION_ERROR|{error}", file=sys.stderr)
        return 1
    print(
        "SMTCOMP_CORPUS_ACQUISITION|"
        f"archives={summary['archive_count']}|"
        f"logics={summary['logic_count']}|"
        f"files={summary['corpus_rows']}|"
        f"bytes={summary['corpus_bytes']}|"
        "selection_observed=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
