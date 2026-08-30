#!/usr/bin/env python3
"""Verify the preregistered clean Int.fib_add_two construction plan."""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v1.json"


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        source = ROOT / plan["execution"]["source"]
        pack = pathlib.Path(plan["execution"]["pack"])
        facts = []
        for premise in plan["premises"]:
            path = ROOT / f"artifacts/facts/{premise['fact_id'].replace('F:', 'F-')}.json"
            facts.append(json.loads(path.read_text()))
        if (
            plan["state"] != "preregistered-after-natcast-admission-before-source-or-execution"
            or plan["target"]["theorem"] != "Int.fib_add_two"
            or source.exists() != plan["execution"]["source_present_at_plan_commit"]
            or pack.exists() != plan["execution"]["pack_present_at_plan_commit"]
            or any(fact["epistemic_status"] != "proved" for fact in facts)
            or any(fact.get("axiom_footprint") != [] for fact in facts)
            or plan["budget"] != {
                "max_compiler_invocations": 1,
                "max_exporter_invocations": 1,
                "max_importer_runs": 2,
                "max_retries": 0,
                "max_target_theorem_submissions": 1,
                "max_search_invocations": 0,
                "max_ledger_writes": 0,
            }
            or "official Int.fib_neg_natCast proof"
            not in plan["representation"]["forbidden"]
        ):
            raise RuntimeError("target, premise, prestate, budget, or proof boundary changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_CONSTRUCTION_PLAN_OK|premises=2|compile=0/1|submissions=0/1|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-construction-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
