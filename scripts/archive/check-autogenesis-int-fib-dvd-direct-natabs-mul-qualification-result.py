#!/usr/bin/env python3
"""Validate sealed direct natAbs multiplication qualification."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-direct-natabs-mul-qualification-result-v6.json"


class ResultError(RuntimeError):
    """The sealed qualification changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    evidence = result["evidence"]
    theorem = result["theorem"]
    execution = result["execution"]
    pack = pathlib.Path(evidence["pack"])
    expected_dependencies = [
        "Eq.symm",
        "_private.AxeyumIntNatAbsMulDirectV1.0.Axeyum.Autogenesis.intNatAbsNegOfNatDirectV1",
    ]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-direct-natabs-mul-qualification-result-v6"
        or result.get("state")
        != "exact-two-dependency-empty-closure-qualified-and-sealed"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(pack / "manifest.json") != evidence.get("manifest_sha256")
        or sha256(pack / "root.ndjson") != evidence.get("root_sha256")
        or sha256(pack / "replay.ndjson") != evidence.get("replay_sha256")
        or stat.S_IMODE(pack.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack.iterdir())
        or theorem.get("axiom_footprint") != []
        or theorem.get("direct_theorem_dependencies") != expected_dependencies
        or execution
        != {
            "stream_hash_reads": 2,
            "audit_report_reads": 0,
            "exporter_invocations": 0,
            "importer_runs": 0,
            "manifest_writes": 1,
            "retries": 0,
            "target_fib_dvd_submissions": 0,
            "ledger_writes": 0,
        }
        or result["authority"].get("support_theorem_credit") != 1
        or result["authority"].get("target_fib_dvd_credit") != 0
    ):
        raise ResultError("sealed pack, exact dependency closure, or budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-direct-natabs-mul-qualification-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-direct-natabs-mul-qualification-result: PASS: "
        "dependencies=2|axioms=0|sealed=true|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
