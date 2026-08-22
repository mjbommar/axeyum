#!/usr/bin/env python3
"""Validate the deterministic, assumption-bearing Int Fibonacci natAbs decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v2.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v2.json"
SOURCE = ROOT / "artifacts/autogenesis/sources/int-fib-natabs-residual-v1.lean"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-natabs-residual-v1")


class ResultError(RuntimeError):
    """The measured decline changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    root = result["root"]
    exports = result["exports"]
    execution = result["execution"]
    expected_axioms = [
        "Classical.choice", "Lean.opaqueId", "Quot", "Quot.lift", "Quot.mk",
        "Quot.sound", "String.Internal.append", "propext",
    ]
    expected_dependencies = ["Eq.symm", "congrArg", "congrFun'", "if_neg", "if_pos"]
    if (
        result.get("state") != "declined-assumption-bearing-before-specialization"
        or result["plan"].get("sha256") != sha256(PLAN)
        or result["source"].get("sha256") != sha256(SOURCE)
        or result["source"].get("compiler_invocations") != 1
        or result["source"].get("compiler_accepted") is not True
        or exports.get("exporter_invocations") != 2
        or exports.get("residual_imports") != 2
        or exports.get("byte_identical") is not True
        or sha256(PACK / "residual-1.ndjson") != exports.get("stream_sha256")
        or sha256(PACK / "residual-2.ndjson") != exports.get("stream_sha256")
        or root.get("name") != "Axeyum.Autogenesis.intFibNatAbsResidualV1"
        or root.get("axiom_footprint") != expected_axioms
        or root.get("direct_theorem_dependencies") != expected_dependencies
        or result["direct_dependency_audit"].get("all_five_empty_footprint") is not True
        or execution != {
            "specialization_submissions": 0,
            "int_gcd_fib_submissions": 0,
            "retries": 0,
            "fact_status_changes": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("decline evidence or zero-credit boundary changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-result-v2: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-result-v2: PASS: "
        "deterministic=1|root_axioms=8|direct_dependencies_clean=5/5|"
        "specializations=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
