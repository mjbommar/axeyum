#!/usr/bin/env python3
"""Select the first bounded hash-order real proof with external DRAT teeth."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


MANIFEST_SHA256 = (
    "67c7f14f5f2f8db1eaa1bb17649cf3623e268e3f7ea678cbe53326bfa8cd899b"
)
OBSERVED_HASH = (
    "0015f5bd8a50e7d1859888c308e0621fede3e8fb322ffaf1222c4e6aad28000e"
)
CHECKER_SHA256 = (
    "c0b9bd6a2369918f171a42d024aa2993d5eff4f597e019850c073d0aa08bd9db"
)
MAX_ATTEMPTS = 32
PROCESS_TIMEOUT_SECONDS = 30


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def stream_record(raw: bytes) -> dict[str, Any]:
    return {
        "bytes": len(raw),
        "sha256": sha256(raw),
        "text": raw.decode("utf-8", errors="replace"),
    }


def run(command: list[str]) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            check=False,
            timeout=PROCESS_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        return {
            "command": command,
            "timed_out": True,
            "exit_code": None,
            "stdout": stream_record(error.stdout or b""),
            "stderr": stream_record(error.stderr or b""),
        }
    return {
        "command": command,
        "timed_out": False,
        "exit_code": completed.returncode,
        "stdout": stream_record(completed.stdout),
        "stderr": stream_record(completed.stderr),
    }


def verified(result: dict[str, Any]) -> bool:
    return (
        result["timed_out"] is False
        and result["exit_code"] == 0
        and any(
            line.strip() == "s VERIFIED"
            for line in result["stdout"]["text"].splitlines()
        )
    )


def candidate_rows(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    if manifest.get("version") != 1 or manifest.get("logic") != "QF_BV":
        raise ValueError("manifest version/logic differs from the preregistration")
    files = manifest.get("files")
    if not isinstance(files, list):
        raise ValueError("manifest files must be an array")
    candidates: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, row in enumerate(files):
        if not isinstance(row, dict):
            raise ValueError(f"manifest files[{index}] must be an object")
        content_hash = row.get("content_hash")
        path = row.get("path")
        if (
            not isinstance(content_hash, str)
            or not content_hash.startswith("sha256:")
            or len(content_hash) != 71
            or not isinstance(path, str)
        ):
            raise ValueError(f"manifest files[{index}] has invalid identity")
        digest = content_hash[7:]
        if digest in seen:
            raise ValueError(f"manifest repeats content hash {digest}")
        seen.add(digest)
        if row.get("expected") == "unsat" and digest != OBSERVED_HASH:
            candidates.append(row)
    candidates.sort(key=lambda row: row["content_hash"])
    if len(candidates) < MAX_ATTEMPTS:
        raise ValueError("manifest has fewer candidates than the fixed attempt cap")
    return candidates[:MAX_ATTEMPTS]


def select(
    *,
    corpus_root: Path,
    manifest_path: Path,
    exporter: Path,
    checker: Path,
    work_root: Path,
    report_path: Path,
) -> tuple[dict[str, Any], bool]:
    if work_root.exists():
        raise ValueError(f"refusing existing work root {work_root}")
    if report_path.exists():
        raise ValueError(f"refusing to overwrite report {report_path}")
    manifest_raw = manifest_path.read_bytes()
    if sha256(manifest_raw) != MANIFEST_SHA256:
        raise ValueError("manifest SHA-256 differs from the preregistration")
    if sha256(checker.read_bytes()) != CHECKER_SHA256:
        raise ValueError("checker binary SHA-256 differs from the preregistration")
    exporter_sha256 = sha256(exporter.read_bytes())
    rows = candidate_rows(json.loads(manifest_raw))
    work_root.mkdir(parents=True)
    attempts: list[dict[str, Any]] = []
    selected_hash: str | None = None

    for row in rows:
        digest = row["content_hash"][7:]
        source = corpus_root / row["path"]
        source_raw = source.read_bytes()
        if sha256(source_raw) != digest:
            raise ValueError(f"source SHA-256 differs for {row['path']}")
        attempt_root = work_root / digest
        proof_root = attempt_root / "proof"
        attempt_root.mkdir()
        export_result = run([str(exporter), str(source), str(proof_root)])
        attempt: dict[str, Any] = {
            "content_hash": digest,
            "family": row.get("family"),
            "source_path": row["path"],
            "source_bytes": len(source_raw),
            "export": export_result,
            "accepted": False,
        }
        attempts.append(attempt)
        if export_result["exit_code"] != 0 or export_result["timed_out"]:
            attempt["status"] = "export-failed"
            continue

        export_manifest_path = proof_root / "manifest.json"
        export_manifest = json.loads(export_manifest_path.read_bytes())
        if export_manifest.get("self_rechecked") is not True:
            raise ValueError(f"exporter did not self-recheck {digest}")
        source_record = export_manifest.get("source", {})
        if source_record.get("sha256") != f"sha256:{digest}":
            raise ValueError(f"export manifest source identity differs for {digest}")
        dimacs = proof_root / "problem.cnf"
        proof = proof_root / "proof.drat"
        proof_raw = proof.read_bytes()
        empty_proof = attempt_root / "empty.drat"
        empty_proof.write_bytes(b"")
        positive = run([str(checker), str(dimacs), str(proof)])
        empty = run([str(checker), str(dimacs), str(empty_proof)])
        proof_lines = len(proof_raw.splitlines())
        positive_verified = verified(positive)
        input_alone_verified = verified(empty)
        accepted = (
            len(proof_raw) > 2
            and proof_lines > 1
            and positive_verified
            and not input_alone_verified
        )
        attempt.update(
            {
                "status": "accepted" if accepted else "insufficient-teeth",
                "proof_bytes": len(proof_raw),
                "proof_lines": proof_lines,
                "proof_sha256": sha256(proof_raw),
                "positive": positive,
                "empty_proof": empty,
                "positive_verified": positive_verified,
                "input_alone_verified": input_alone_verified,
                "accepted": accepted,
            }
        )
        if accepted:
            selected_hash = digest
            break

    report = {
        "schema": "axeyum.nontrivial-external-drat-selection.v1",
        "status": "accepted" if selected_hash is not None else "no-selection",
        "selection": {
            "manifest_sha256": MANIFEST_SHA256,
            "excluded_observed_hash": OBSERVED_HASH,
            "order": "ascending content hash among expected-UNSAT rows",
            "maximum_attempts": MAX_ATTEMPTS,
            "process_timeout_seconds": PROCESS_TIMEOUT_SECONDS,
            "acceptance": (
                "proof >2 bytes and >1 line; real proof VERIFIED; empty proof "
                "over the same CNF not VERIFIED"
            ),
        },
        "binaries": {
            "exporter_sha256": exporter_sha256,
            "checker_sha256": CHECKER_SHA256,
        },
        "candidate_hashes": [row["content_hash"][7:] for row in rows],
        "attempted": attempts,
        "selected_hash": selected_hash,
        "claim_limits": [
            "Selection is proof-shape-conditioned but deterministic and retains every attempted row.",
            "No timing is performance evidence.",
            "External clausal verification does not certify SMT-LIB source lowering.",
        ],
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report, selected_hash is not None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    report, accepted = select(
        corpus_root=args.corpus_root,
        manifest_path=args.manifest,
        exporter=args.exporter,
        checker=args.checker,
        work_root=args.work_root,
        report_path=args.report,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if accepted else 2


if __name__ == "__main__":
    raise SystemExit(main())
