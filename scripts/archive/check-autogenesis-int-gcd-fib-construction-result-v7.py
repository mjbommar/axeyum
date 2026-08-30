#!/usr/bin/env python3
"""Validate the clean function-abstracted Int Fibonacci natAbs residual."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v7.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v7.json"
SOURCE = ROOT / "artifacts/autogenesis/sources/int-fib-natabs-residual-v2.lean"
MANIFEST = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-natabs-residual-v2/manifest.json"
)


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    capsule = pathlib.Path(result["capsule"]["path"])
    second = capsule.with_name("residual-2.ndjson")
    if (
        result.get("state")
        != "function-abstracted-residual-exported-twice-empty-footprint"
        or result["plan"].get("sha256") != sha256(PLAN)
        or result["source"].get("sha256") != sha256(SOURCE)
        or capsule.stat().st_size != result["capsule"].get("bytes")
        or sha256(capsule) != result["capsule"].get("sha256")
        or sha256(second) != result["capsule"].get("sha256")
        or result["root"].get("name")
        != "Axeyum.Autogenesis.intFibNatAbsResidualV2"
        or result["root"].get("axiom_footprint") != []
        or result["root"].get("direct_theorem_dependencies")
        != ["Eq.symm", "congrArg"]
        or result["execution"]
        != {
            "compiler_invocations": 1,
            "exporter_invocations": 2,
            "exports_byte_identical": True,
            "fresh_imports": 2,
            "specialization_submissions": 0,
            "int_gcd_fib_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or result["measured"].get("official_int_fib_even_closure_removed") is not True
        or result["measured"].get("assumptions_removed") != 8
        or stat.S_IMODE(capsule.stat().st_mode) != 0o444
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
    ):
        raise ValueError("clean residual identity, assurance, or seal changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-result-v7: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-result-v7: PASS: "
        "bytes=351201|imports=2|axioms=0|dependencies=2|specializations=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
