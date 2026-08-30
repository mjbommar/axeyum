#!/usr/bin/env python3
"""Validate the durable V5 diagnosis and function-abstracted V6 residual."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V5_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v5.json"
V5_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v5.json"
V6_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v6.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(V5_RESULT.read_text())
    plan = json.loads(V6_PLAN.read_text())
    report_path = pathlib.Path(result["report"]["path"])
    report = json.loads(report_path.read_text())
    all_carriers = [
        {row["name"] for row in blocker["carriers_nearest_first"]}
        for blocker in report["blocker_rows"]
    ]
    common = set.intersection(*all_carriers)
    required_common = {
        "Int.instDecidablePredEven._proof_1",
        "Int.instDecidablePredEven",
        "Int.fib",
    }
    if (
        result.get("state") != "durable-blocker-path-audit-complete"
        or result["plan"].get("sha256") != sha256(V5_PLAN)
        or report_path.stat().st_size != result["report"].get("bytes")
        or stat.S_IMODE(report_path.stat().st_mode) != 0o444
        or sha256(report_path) != result["report"].get("sha256")
        or result["execution"].get("candidate_closure_computations") != 2538
        or result["execution"].get("completed_audit_documents") != 1
        or result["execution"].get("ledger_writes") != 0
        or len(report.get("blocker_rows", [])) != 8
        or not required_common <= common
        or result["authority"].get("rendered_proof_terms") != 0
        or plan.get("state")
        != "preregistered-before-function-abstracted-residual-source-construction"
        or plan["parent_result"].get("sha256") != sha256(V5_RESULT)
        or plan["residual"].get("name")
        != "Axeyum.Autogenesis.intFibNatAbsResidualV2"
        or len(plan["residual"].get("explicit_parameters", [])) != 8
        or plan["residual"].get("forbidden_constants")
        != [
            "Int.fib", "Int.instDecidablePredEven", "Int.even_iff",
            "Classical.propDecidable",
        ]
        or plan["execution"].get("max_lean_compiler_invocations") != 1
        or plan["execution"].get("max_exporter_invocations") != 2
        or plan["execution"].get("max_importer_runs") != 2
        or plan["execution"].get("max_retries") != 0
        or plan["execution"].get("specialization_submissions") != 0
        or plan["execution"].get("ledger_writes") != 0
        or plan["acceptance"].get("axiom_footprint") != []
        or plan["acceptance"].get("forbidden_constants_absent_from_root_closure")
        is not True
        or plan["authority"].get("ledger_writes") != 0
    ):
        raise ValueError("V5 diagnosis or V6 residual boundary changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v5-v6: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-v5-v6: PASS: "
        "report=durable|blockers=8|common=Int.fib+EvenDecision|"
        "v6_parameters=8|specializations=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
