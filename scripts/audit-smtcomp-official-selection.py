#!/usr/bin/env python3
"""Build or verify the complete independent ADR-0356 selection artifact."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.smtcomp_repro.final_selection_audit import (
    FINAL_REASONS,
    FinalSelectionAuditError,
    merge_decision,
    read_selected,
    run_registered_mutations,
    sha256_file,
    validate_benchmark_id,
    validate_logic_summary,
    validate_published_decision,
)
from scripts.smtcomp_repro.official_selection import canonical_json_bytes


SCHEMA = "axeyum-smtcomp-official-selection-v1"
EXPECTED_AUTHORITY_SHA256 = "0fd1f479e809e0d8f740aa72cff193871b35f45c95a2eb9d96440ca7508b3d1a"
EXPECTED_CONTRACT_SHA256 = "6ff746c3d0521e895a35a534d375bb151612bc32aa47e9a55fab48fc09b36fb9"
IMPLEMENTATION_PATHS = (
    "docs/plan/smtcomp-official-selection-authority-v1.json",
    "docs/plan/smtcomp-official-selection-contract-v1.json",
    "scripts/audit-smtcomp-official-selection.py",
    "scripts/smtcomp_repro/final_selection_audit.py",
)
REQUIRED_ARTIFACTS = (
    "authority.json",
    "archives.json",
    "corpus.jsonl",
    "historical.jsonl",
    "decisions.jsonl",
    "official-selected.txt",
    "selected-files.jsonl",
    "summary.json",
    "producer.json",
    "audit.json",
)
PRIOR_ARTIFACTS = {
    "input-audit.json": {"downloads.json", "eligibility.jsonl", "summary.json"},
    "corpus-audit.json": {"archives.json", "corpus.jsonl", "summary.json"},
    "producer-audit.json": {
        "official-selected.txt",
        "per-logic.json",
        "producer.json",
        "requirements.lock",
    },
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_document(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or raw != canonical_json_bytes(value):
        raise FinalSelectionAuditError(f"noncanonical JSON document: {path}")
    return value


def verify_completion(
    root: Path,
    name: str,
    schema: str,
    selection_observed: bool,
) -> tuple[dict[str, Any], str]:
    path = root / name
    document = canonical_document(path)
    if (
        document.get("schema") != schema
        or document.get("status") != "complete"
        or document.get("selection_observed") is not selection_observed
        or document.get("authority_sha256") != EXPECTED_AUTHORITY_SHA256
    ):
        raise FinalSelectionAuditError(f"prior completion differs: {path}")
    payload = {key: value for key, value in document.items() if key != "payload_sha256"}
    if sha256_bytes(canonical_json_bytes(payload)) != document.get("payload_sha256"):
        raise FinalSelectionAuditError(f"prior completion payload differs: {path}")
    artifacts = document.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != PRIOR_ARTIFACTS[name]:
        raise FinalSelectionAuditError(f"prior artifact map is missing: {path}")
    for relative, expected in artifacts.items():
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise FinalSelectionAuditError(f"invalid prior artifact entry: {path}")
        if sha256_file(root / relative)[1] != expected:
            raise FinalSelectionAuditError(f"prior artifact differs: {root / relative}")
    return document, sha256_file(path)[1]


def implementation_commit() -> str:
    for relative in IMPLEMENTATION_PATHS:
        result = subprocess.run(
            ["git", "ls-files", "--error-unmatch", relative],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if result.returncode != 0:
            raise FinalSelectionAuditError(f"S4 implementation is not committed: {relative}")
    result = subprocess.run(
        ["git", "diff", "--quiet", "HEAD", "--", *IMPLEMENTATION_PATHS],
        cwd=ROOT,
        check=False,
    )
    if result.returncode != 0:
        raise FinalSelectionAuditError("S4 implementation differs from HEAD")
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout.decode().strip()


def publish(path: Path, data: bytes) -> tuple[int, str]:
    if path.exists():
        raise FinalSelectionAuditError(f"artifact already exists: {path}")
    temporary = path.with_name(path.name + ".part")
    with temporary.open("xb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())
    os.replace(temporary, path)
    return len(data), sha256_bytes(data)


def copy_artifact(source: Path, destination: Path) -> tuple[int, str]:
    if destination.exists():
        raise FinalSelectionAuditError(f"artifact already exists: {destination}")
    expected = sha256_file(source)
    temporary = destination.with_name(destination.name + ".part")
    with source.open("rb") as input_file, temporary.open("xb") as output:
        shutil.copyfileobj(input_file, output, length=1024 * 1024)
        output.flush()
        os.fsync(output.fileno())
    observed = sha256_file(temporary)
    if observed != expected:
        raise FinalSelectionAuditError(f"copied artifact differs: {source}")
    os.replace(temporary, destination)
    return observed


class JsonlWriter:
    """Write canonical JSONL to a temporary file and publish it atomically."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.temporary = path.with_name(path.name + ".part")
        self.output: BinaryIO = self.temporary.open("xb")
        self.digest = hashlib.sha256()
        self.bytes = 0
        self.rows = 0

    def write(self, value: object) -> bytes:
        data = canonical_json_bytes(value)
        self.output.write(data)
        self.digest.update(data)
        self.bytes += len(data)
        self.rows += 1
        return data

    def finish(self) -> dict[str, object]:
        self.output.flush()
        os.fsync(self.output.fileno())
        self.output.close()
        os.replace(self.temporary, self.path)
        return {"bytes": self.bytes, "rows": self.rows, "sha256": self.digest.hexdigest()}


def parse_json_line(raw: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as error:
        raise FinalSelectionAuditError(f"invalid JSONL row: {label}") from error
    if not isinstance(value, dict) or raw != canonical_json_bytes(value):
        raise FinalSelectionAuditError(f"noncanonical JSONL row: {label}")
    return value


def build_artifact(args: argparse.Namespace) -> Path:
    authority_raw = args.authority.read_bytes()
    if sha256_bytes(authority_raw) != EXPECTED_AUTHORITY_SHA256:
        raise FinalSelectionAuditError("authority SHA-256 differs")
    authority = json.loads(authority_raw)
    if not isinstance(authority, dict) or authority_raw != canonical_json_bytes(authority):
        raise FinalSelectionAuditError("authority is not canonical JSON")
    contract_raw = args.contract.read_bytes()
    if sha256_bytes(contract_raw) != EXPECTED_CONTRACT_SHA256:
        raise FinalSelectionAuditError("contract SHA-256 differs")
    contract = json.loads(contract_raw)
    if not isinstance(contract, dict):
        raise FinalSelectionAuditError("contract is not a JSON object")

    _, s1_completion_sha256 = verify_completion(
        args.input_audit,
        "input-audit.json",
        "axeyum-smtcomp-selection-input-audit-v1",
        False,
    )
    _, s2_completion_sha256 = verify_completion(
        args.corpus_acquisition,
        "corpus-audit.json",
        "axeyum-smtcomp-selection-corpus-acquisition-v1",
        False,
    )
    _, s3_completion_sha256 = verify_completion(
        args.producer,
        "producer-audit.json",
        "axeyum-smtcomp-official-producer-v1",
        True,
    )
    s1_summary = canonical_document(args.input_audit / "summary.json")
    s2_summary = canonical_document(args.corpus_acquisition / "summary.json")
    producer = canonical_document(args.producer / "producer.json")
    per_logic_document = canonical_document(args.producer / "per-logic.json")
    if (
        s1_summary.get("metadata_rows") != 450_472
        or s2_summary.get("corpus_rows") != 450_472
        or producer.get("selected") != 45_905
        or producer.get("repetition", {}).get("equal") is not True
    ):
        raise FinalSelectionAuditError("prior stage population or repetition differs")

    selected_paths = read_selected(args.producer / "official-selected.txt")
    if len(selected_paths) != 45_905:
        raise FinalSelectionAuditError("official selected count differs")
    selected = set(selected_paths)
    remaining = set(selected)
    registered_logics = s1_summary.get("logic_summary")
    official_logic_rows = per_logic_document.get("logics")
    if not isinstance(registered_logics, list) or not isinstance(official_logic_rows, list):
        raise FinalSelectionAuditError("per-logic input summaries are missing")
    registered_by_logic = {row["logic"]: row for row in registered_logics}
    official_by_logic = {row["logic"]: row for row in official_logic_rows}
    if len(registered_by_logic) != 89 or len(official_by_logic) != 88:
        raise FinalSelectionAuditError("per-logic input population differs")

    commit = implementation_commit()
    args.output_parent.mkdir(parents=True, exist_ok=True)
    attempt = args.output_parent / f"selection-audit-{time.time_ns()}-{commit[:8]}"
    attempt.mkdir()
    artifacts: dict[str, dict[str, object]] = {}
    for name, source in (
        ("authority.json", args.authority),
        ("archives.json", args.corpus_acquisition / "archives.json"),
        ("corpus.jsonl", args.corpus_acquisition / "corpus.jsonl"),
        ("official-selected.txt", args.producer / "official-selected.txt"),
        ("producer.json", args.producer / "producer.json"),
    ):
        size, sha256 = copy_artifact(source, attempt / name)
        artifacts[name] = {"bytes": size, "sha256": sha256}

    decisions_writer = JsonlWriter(attempt / "decisions.jsonl")
    historical_writer = JsonlWriter(attempt / "historical.jsonl")
    selected_writer = JsonlWriter(attempt / "selected-files.jsonl")
    logic_counts: dict[str, Counter[str]] = defaultdict(Counter)
    logic_decision_digests: dict[str, Any] = defaultdict(hashlib.sha256)
    logic_selected_digests: dict[str, Any] = defaultdict(hashlib.sha256)
    global_reasons: Counter[str] = Counter()
    previous: str | None = None
    rows = 0
    selected_bytes = 0
    eligibility_path = args.input_audit / "eligibility.jsonl"
    corpus_path = args.corpus_acquisition / "corpus.jsonl"
    with eligibility_path.open("rb") as eligibility_file, corpus_path.open("rb") as corpus_file:
        for index, pair in enumerate(itertools.zip_longest(eligibility_file, corpus_file), start=1):
            eligibility_raw, corpus_raw = pair
            if eligibility_raw is None or corpus_raw is None:
                raise FinalSelectionAuditError("eligibility/corpus row counts differ")
            eligibility = parse_json_line(eligibility_raw, f"eligibility:{index}")
            corpus = parse_json_line(corpus_raw, f"corpus:{index}")
            benchmark_id = validate_benchmark_id(eligibility.get("benchmark_id"))
            if previous is not None and benchmark_id <= previous:
                raise FinalSelectionAuditError("eligibility ledger is not strictly path-sorted")
            previous = benchmark_id
            is_selected = benchmark_id in selected
            decision = merge_decision(eligibility, corpus, is_selected)
            decision_bytes = decisions_writer.write(decision)
            historical_writer.write({"benchmark_id": benchmark_id, "historical": decision["historical"]})
            logic = decision["logic"]
            reason = decision["reason"]
            logic_counts[logic]["metadata"] += 1
            logic_counts[logic][reason] += 1
            global_reasons[reason] += 1
            logic_decision_digests[logic].update(decision_bytes)
            if is_selected:
                remaining.remove(benchmark_id)
                physical = args.corpus_acquisition / "corpus" / Path(*PurePosixPath(benchmark_id).parts)
                size, sha256 = sha256_file(physical)
                if size != corpus["bytes"] or sha256 != corpus["sha256"]:
                    raise FinalSelectionAuditError(f"selected file bytes differ: {benchmark_id}")
                selected_row = {
                    "archive": corpus["archive"],
                    "benchmark_id": benchmark_id,
                    "bytes": size,
                    "logic": logic,
                    "sha256": sha256,
                }
                selected_row_bytes = selected_writer.write(selected_row)
                logic_selected_digests[logic].update(selected_row_bytes)
                selected_bytes += size
            rows += 1
            if rows % 50_000 == 0:
                print(f"S4_AUDIT_PROGRESS|rows={rows}/450472|selected_hashed={selected_writer.rows}/45905")
    if rows != 450_472 or remaining:
        raise FinalSelectionAuditError(f"final population differs: rows={rows} unknown_selected={len(remaining)}")

    decision_identity = decisions_writer.finish()
    historical_identity = historical_writer.finish()
    selected_identity = selected_writer.finish()
    artifacts["decisions.jsonl"] = decision_identity
    artifacts["historical.jsonl"] = historical_identity
    artifacts["selected-files.jsonl"] = selected_identity

    logic_summary = []
    for logic in sorted(registered_by_logic):
        observed = logic_counts[logic]
        validate_logic_summary(registered_by_logic[logic], observed, official_by_logic.get(logic))
        logic_summary.append(
            {
                **dict(sorted(observed.items())),
                "decision_sha256": logic_decision_digests[logic].hexdigest(),
                "logic": logic,
                "selected_files_sha256": logic_selected_digests[logic].hexdigest(),
            }
        )
    if set(logic_counts) != set(registered_by_logic):
        raise FinalSelectionAuditError("observed logic set differs")
    if sum(global_reasons.values()) != 450_472 or sum(
        global_reasons[reason] for reason in ("selected-new", "selected-old")
    ) != 45_905:
        raise FinalSelectionAuditError("global terminal partition differs")

    summary = {
        "artifacts": dict(artifacts),
        "authority_sha256": EXPECTED_AUTHORITY_SHA256,
        "corpus_bytes": s2_summary["corpus_bytes"],
        "implementation_commit": commit,
        "input_audit_completion_sha256": s1_completion_sha256,
        "logic_summary": logic_summary,
        "metadata_rows": rows,
        "producer_completion_sha256": s3_completion_sha256,
        "reason_counts": dict(sorted(global_reasons.items())),
        "schema": SCHEMA,
        "selected_bytes": selected_bytes,
        "selected_files": selected_writer.rows,
        "selection_observed": True,
        "verified_corpus_completion_sha256": s2_completion_sha256,
    }
    summary_bytes = canonical_json_bytes(summary)
    artifacts["summary.json"] = dict(zip(("bytes", "sha256"), publish(attempt / "summary.json", summary_bytes)))

    mutations = run_registered_mutations(contract)
    invariants = contract.get("invariants")
    if not isinstance(invariants, list) or len(invariants) != 18:
        raise FinalSelectionAuditError("registered invariant list differs")
    audit = {
        "invariants": [
            {"id": row["id"], "result": "passed", "statement": row["statement"]}
            for row in invariants
        ],
        "mutations": mutations,
        "schema": SCHEMA,
        "selected_files_rehashed": selected_writer.rows,
        "selection_observed": True,
    }
    audit_bytes = canonical_json_bytes(audit)
    artifacts["audit.json"] = dict(zip(("bytes", "sha256"), publish(attempt / "audit.json", audit_bytes)))

    if set(artifacts) != set(REQUIRED_ARTIFACTS):
        raise FinalSelectionAuditError("final artifact set differs before completion")
    completion_payload = {
        "artifacts": {name: artifacts[name]["sha256"] for name in sorted(artifacts)},
        "authority_sha256": EXPECTED_AUTHORITY_SHA256,
        "metadata_rows": 450_472,
        "schema": SCHEMA,
        "selected_files": 45_905,
        "selection_observed": True,
        "status": "complete",
    }
    completion = {
        **completion_payload,
        "payload_sha256": sha256_bytes(canonical_json_bytes(completion_payload)),
    }
    complete_bytes = canonical_json_bytes(completion)
    publish(attempt / "complete.json", complete_bytes)
    complete_sha256 = sha256_bytes(complete_bytes)
    accepted = args.output_parent / f"accepted-{complete_sha256}"
    if accepted.exists():
        raise FinalSelectionAuditError(f"content-addressed accepted root already exists: {accepted}")
    os.replace(attempt, accepted)
    print(
        "SMTCOMP_FINAL_SELECTION_OK|metadata=450472|selected=45905|"
        f"selected_bytes={selected_bytes}|mutations=18|complete_sha256={complete_sha256}"
    )
    print(accepted)
    return accepted


def verify_artifact(root: Path, corpus_acquisition: Path) -> None:
    completion = canonical_document(root / "complete.json")
    if (
        completion.get("schema") != SCHEMA
        or completion.get("status") != "complete"
        or completion.get("selection_observed") is not True
        or completion.get("authority_sha256") != EXPECTED_AUTHORITY_SHA256
        or completion.get("metadata_rows") != 450_472
        or completion.get("selected_files") != 45_905
    ):
        raise FinalSelectionAuditError("final completion differs")
    payload = {key: value for key, value in completion.items() if key != "payload_sha256"}
    if sha256_bytes(canonical_json_bytes(payload)) != completion.get("payload_sha256"):
        raise FinalSelectionAuditError("final completion payload differs")
    if set(completion.get("artifacts", {})) != set(REQUIRED_ARTIFACTS):
        raise FinalSelectionAuditError("final artifact set differs")
    complete_sha256 = sha256_file(root / "complete.json")[1]
    if root.name != f"accepted-{complete_sha256}":
        raise FinalSelectionAuditError("final content-addressed root differs")
    for name, expected in completion["artifacts"].items():
        if sha256_file(root / name)[1] != expected:
            raise FinalSelectionAuditError(f"final artifact differs: {name}")
    summary = canonical_document(root / "summary.json")
    audit = canonical_document(root / "audit.json")
    selected = read_selected(root / "official-selected.txt")
    mutation_rows = audit.get("mutations", [])
    invariant_rows = audit.get("invariants", [])
    if (
        summary.get("schema") != SCHEMA
        or summary.get("authority_sha256") != EXPECTED_AUTHORITY_SHA256
        or summary.get("selection_observed") is not True
        or audit.get("schema") != SCHEMA
        or audit.get("selection_observed") is not True
        or audit.get("selected_files_rehashed") != 45_905
        or sha256_file(root / "authority.json")[1] != EXPECTED_AUTHORITY_SHA256
        or len(selected) != 45_905
        or summary.get("metadata_rows") != 450_472
        or summary.get("selected_files") != 45_905
        or [row.get("id") for row in invariant_rows] != [f"S{number:02d}" for number in range(1, 19)]
        or any(row.get("result") != "passed" for row in invariant_rows)
        or [row.get("id") for row in mutation_rows] != [f"M{number:02d}" for number in range(1, 19)]
        or any(row.get("result") != "rejected" for row in mutation_rows)
    ):
        raise FinalSelectionAuditError("final summary or audit differs")
    summary_artifacts = summary.get("artifacts")
    if not isinstance(summary_artifacts, dict) or set(summary_artifacts) != {
        "archives.json",
        "authority.json",
        "corpus.jsonl",
        "decisions.jsonl",
        "historical.jsonl",
        "official-selected.txt",
        "producer.json",
        "selected-files.jsonl",
    }:
        raise FinalSelectionAuditError("summary artifact identities differ")
    for name, identity in summary_artifacts.items():
        if not isinstance(identity, dict) or sha256_file(root / name) != (
            identity.get("bytes"),
            identity.get("sha256"),
        ):
            raise FinalSelectionAuditError(f"summary artifact identity differs: {name}")

    selected_set = set(selected)
    remaining = set(selected)
    rows = 0
    selected_rows = 0
    selected_bytes = 0
    previous: str | None = None
    reasons: Counter[str] = Counter()
    logic_counts: dict[str, Counter[str]] = defaultdict(Counter)
    with (
        (root / "corpus.jsonl").open("rb") as corpus_file,
        (root / "historical.jsonl").open("rb") as historical_file,
        (root / "decisions.jsonl").open("rb") as decisions_file,
        (root / "selected-files.jsonl").open("rb") as selected_file,
    ):
        selected_iterator = iter(selected_file)
        next_selected = next(selected_iterator, None)
        for index, triple in enumerate(
            itertools.zip_longest(corpus_file, historical_file, decisions_file), start=1
        ):
            corpus_raw, historical_raw, decision_raw = triple
            if corpus_raw is None or historical_raw is None or decision_raw is None:
                raise FinalSelectionAuditError("published ledger row counts differ")
            corpus = parse_json_line(corpus_raw, f"corpus:{index}")
            historical = parse_json_line(historical_raw, f"historical:{index}")
            decision = parse_json_line(decision_raw, f"decisions:{index}")
            benchmark_id = validate_benchmark_id(decision.get("benchmark_id"))
            if previous is not None and benchmark_id <= previous:
                raise FinalSelectionAuditError("published ledger order differs")
            previous = benchmark_id
            is_selected = benchmark_id in selected_set
            reason = validate_published_decision(decision, corpus, historical, is_selected)
            logic = decision["logic"]
            reasons[reason] += 1
            logic_counts[logic]["metadata"] += 1
            logic_counts[logic][reason] += 1
            if is_selected:
                if next_selected is None:
                    raise FinalSelectionAuditError("selected-file ledger ended early")
                selected_row = parse_json_line(next_selected, f"selected-files:{selected_rows + 1}")
                expected_selected_row = {
                    "archive": corpus["archive"],
                    "benchmark_id": benchmark_id,
                    "bytes": corpus["bytes"],
                    "logic": logic,
                    "sha256": corpus["sha256"],
                }
                if selected_row != expected_selected_row:
                    raise FinalSelectionAuditError(f"selected-file row differs: {benchmark_id}")
                physical = corpus_acquisition / "corpus" / Path(*PurePosixPath(benchmark_id).parts)
                if sha256_file(physical) != (corpus["bytes"], corpus["sha256"]):
                    raise FinalSelectionAuditError(f"selected-file rehash differs: {benchmark_id}")
                remaining.remove(benchmark_id)
                selected_rows += 1
                selected_bytes += corpus["bytes"]
                next_selected = next(selected_iterator, None)
            rows += 1
            if rows % 50_000 == 0:
                print(f"S4_VERIFY_PROGRESS|rows={rows}/450472|selected_hashed={selected_rows}/45905")
        if next_selected is not None:
            raise FinalSelectionAuditError("selected-file ledger has trailing rows")
    observed_logic_summary = {
        row.get("logic"): row for row in summary.get("logic_summary", [])
        if isinstance(row, dict)
    }
    if (
        rows != 450_472
        or selected_rows != 45_905
        or remaining
        or selected_bytes != summary.get("selected_bytes")
        or dict(sorted(reasons.items())) != summary.get("reason_counts")
        or set(observed_logic_summary) != set(logic_counts)
    ):
        raise FinalSelectionAuditError("published population summary differs")
    for logic, observed in logic_counts.items():
        recorded = observed_logic_summary[logic]
        for key, value in observed.items():
            if recorded.get(key) != value:
                raise FinalSelectionAuditError(f"published per-logic summary differs: {logic} {key}")
    print(
        "SMTCOMP_FINAL_SELECTION_VERIFY_OK|metadata=450472|selected=45905|"
        f"mutations=18|complete_sha256={complete_sha256}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--authority",
        type=Path,
        default=ROOT / "docs/plan/smtcomp-official-selection-authority-v1.json",
    )
    parser.add_argument(
        "--contract",
        type=Path,
        default=ROOT / "docs/plan/smtcomp-official-selection-contract-v1.json",
    )
    parser.add_argument("--input-audit", type=Path)
    parser.add_argument("--corpus-acquisition", type=Path, required=True)
    parser.add_argument("--producer", type=Path)
    parser.add_argument("--output-parent", type=Path)
    parser.add_argument("--verify-root", type=Path)
    args = parser.parse_args()
    if args.verify_root is not None:
        verify_artifact(args.verify_root, args.corpus_acquisition)
        return 0
    if args.input_audit is None or args.producer is None or args.output_parent is None:
        parser.error("build mode requires --input-audit, --producer, and --output-parent")
    build_artifact(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
