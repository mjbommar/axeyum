#!/usr/bin/env python3
"""Validate the durable V5 blocker-path audit boundary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v5.json"
REPAIR = ROOT / "artifacts/autogenesis/int-gcd-fib-blocker-auditor-repair-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/declaration_blocker_path_batch_audit.rs"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    source = pathlib.Path(plan["input"]["path"])
    execution = plan["execution"]
    acceptance = plan["acceptance"]
    output = pathlib.Path(execution["output_path"])
    if (
        plan.get("state")
        != "preregistered-before-single-durable-blocker-path-read"
        or plan["tool_repair"].get("sha256") != sha256(REPAIR)
        or source.stat().st_size != plan["input"].get("bytes")
        or stat.S_IMODE(source.stat().st_mode) != 0o444
        or sha256(source) != plan["input"].get("sha256")
        or plan.get("root") != "Axeyum.Autogenesis.intFibNatAbsResidualV1"
        or len(plan.get("ordered_blockers", [])) != 8
        or execution.get("tool_sha256") != sha256(TOOL)
        or execution.get("output_must_not_preexist") is not True
        or execution.get("max_importer_runs") != 1
        or execution.get("max_proof_bearing_stream_reads") != 1
        or execution.get("max_retries") != 0
        or execution.get("max_theorem_submissions") != 0
        or execution.get("max_ledger_writes") != 0
        or acceptance.get("candidate_closures_reused_across_blockers") is not True
        or any(acceptance.get(key) != 0 for key in (
            "rendered_proof_terms", "rendered_theorem_types", "rendered_theorem_values"
        ))
        or plan["authority"].get("definition_bodies_readable_by_model") is not False
        or plan["authority"].get("ledger_writes") != 0
    ):
        raise ValueError("durable audit identity, budget, or authority changed")
    if output.exists():
        report = json.loads(output.read_text())
        if (
            report.get("kind") != "axeyum-declaration-blocker-path-batch-audit"
            or len(report.get("blocker_rows", [])) != 8
            or report.get("performance", {}).get(
                "candidate_closures_reused_across_blockers"
            )
            is not True
            or any(report.get("rendered_material", {}).get(key) != 0 for key in (
                "proof_terms", "theorem_types", "theorem_values"
            ))
        ):
            raise ValueError("durable report changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-plan-v5: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-plan-v5: PASS: "
        "blockers=8|reads=1|durable=1|memoized=1|rendered=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
