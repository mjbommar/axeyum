#!/usr/bin/env python3
"""Validate the bounded non-rendering Int Fibonacci natAbs path audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v3.json"
PARENT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v2.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/declaration_blocker_path_batch_audit.rs"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    source = pathlib.Path(plan["input"]["path"])
    expected_blockers = [
        "Classical.choice", "Lean.opaqueId", "Quot", "Quot.lift", "Quot.mk",
        "Quot.sound", "String.Internal.append", "propext",
    ]
    if (
        plan.get("state")
        != "preregistered-before-single-nonrendering-blocker-path-read"
        or sha256(PARENT) != plan["parent_result"].get("sha256")
        or plan.get("root") != "Axeyum.Autogenesis.intFibNatAbsResidualV1"
        or plan.get("ordered_blockers") != expected_blockers
        or source.stat().st_size != plan["input"].get("bytes")
        or stat.S_IMODE(source.stat().st_mode) != 0o444
        or sha256(source) != plan["input"].get("sha256")
        or sha256(TOOL) != plan["measurement"].get("tool_sha256")
        or plan["measurement"].get("proof_terms_types_or_values_may_be_rendered")
        is not False
        or plan.get("budget")
        != {
            "max_importer_runs": 1,
            "max_proof_bearing_stream_reads": 1,
            "max_retries": 0,
            "max_theorem_submissions": 0,
            "max_ledger_writes": 0,
        }
        or plan["authority"].get("proof_bodies_readable_by_model") is not False
        or plan["authority"].get("definition_bodies_readable_by_model") is not False
        or plan["authority"].get("ledger_writes") != 0
    ):
        raise ValueError("path-audit identity, budget, or authority changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-plan-v3: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-plan-v3: PASS: "
        "root=intFibNatAbsResidualV1|blockers=8|reads=1|rendered=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
