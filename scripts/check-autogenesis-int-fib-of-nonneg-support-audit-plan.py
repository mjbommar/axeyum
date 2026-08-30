#!/usr/bin/env python3
"""Validate the frozen Int.fib_of_nonneg support audit boundary."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-nonneg-support-audit-plan-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        target = plan["target"]
        input_ = plan["input"]
        audit = plan["audit"]
        boundary = plan["construction_boundary_on_accept"]
        fact = ROOT / "artifacts/facts/F-ml430-int-fib-of-nonneg-438018c5.json"
        capsule = pathlib.Path(input_["path"])
        assert plan["state"] == "preregistered-before-support-inspection-or-target-construction"
        assert target["fact_id"] == "F:ml430-int-fib-of-nonneg-438018c5"
        assert target["name"] == "Int.fib_of_nonneg"
        assert sha256(fact) == target["fact_sha256"]
        assert json.loads(fact.read_text())["epistemic_status"] == "open"
        assert sha256(capsule) == input_["sha256"]
        assert capsule.stat().st_size == input_["bytes"]
        assert sha256(ROOT / input_["construction_result"]) == input_["construction_result_sha256"]
        assert plan["candidate_support"]["name"] == "if_pos"
        assert audit["importer_runs"] == audit["stream_reads"] == 1
        assert audit["render_proof_terms"] == audit["render_theorem_types"] == audit["render_theorem_values"] == 0
        assert audit["target_theorem_submissions"] == audit["ledger_writes"] == 0
        assert boundary["forbidden_roots"] == ["Int.fib_of_nonneg"]
        assert boundary["max_target_submissions"] == 1
        assert boundary["max_fresh_imports"] == 2
        assert boundary["max_search_invocations"] == 0
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-of-nonneg-support-audit-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-of-nonneg-support-audit-plan: PASS: reads=1|rendering=0|targets=0|ledger_writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
