#!/usr/bin/env python3
"""Validate the fail-closed Int.fib_dvd support export result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-support-export-result-v1.json"


class ResultError(RuntimeError):
    """The declined support evidence changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    capsule = result["capsule"]
    root = result["root"]
    execution = result["execution"]
    decision = result["decision"]
    path = pathlib.Path(capsule["path"])
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-support-export-result-v1"
        or result.get("state")
        != "official-root-rejected-for-nonempty-axiom-footprint"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(path) != capsule.get("sha256")
        or path.stat().st_size != capsule.get("bytes")
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(path.parent.stat().st_mode) != 0o555
        or sha256(path.parent / "manifest.json") != capsule.get("manifest_sha256")
        or root.get("name") != "Int.natAbs_dvd_natAbs"
        or root.get("declaration_sha256")
        != "6a1e9779d4b927213174e13a2e09578a4de1062072c22ec97127e93f406b063a"
        or root.get("axiom_footprint") != ["propext"]
        or execution
        != {
            "exporter_invocations": 1,
            "root_stream_writes": 1,
            "importer_runs": 2,
            "imports_byte_identical": True,
            "retries": 0,
            "target_theorem_submissions": 0,
            "ledger_writes": 0,
        }
        or decision.get("accepted_as_clean_support") is not False
    ):
        raise ResultError("declined support identity, footprint, or budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-support-export-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-support-export-result: PASS: "
        "root=Int.natAbs_dvd_natAbs|axioms=propext|accepted=false|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
