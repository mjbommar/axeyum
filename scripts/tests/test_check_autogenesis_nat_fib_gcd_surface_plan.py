#!/usr/bin/env python3
"""Mutation controls for the Nat.fib_gcd surface-audit plan."""

from __future__ import annotations

import copy
import importlib.util
import unittest
from unittest import mock


SCRIPT = __import__("pathlib").Path(__file__).parents[1] / (
    "check-autogenesis-nat-fib-gcd-surface-plan.py"
)
SPEC = importlib.util.spec_from_file_location("check_nat_fib_gcd_surface_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SurfacePlanTests(unittest.TestCase):
    def test_committed_plan_passes(self) -> None:
        plan = MODULE.validate()
        self.assertEqual(plan["target"]["name"], "Nat.fib_gcd")

    def test_target_mutation_fails(self) -> None:
        original = MODULE.json.loads(MODULE.PLAN.read_text())
        changed = copy.deepcopy(original)
        changed["target"]["name"] = "Nat.wrong"
        with mock.patch.object(MODULE.json, "loads", return_value=changed):
            with self.assertRaisesRegex(MODULE.PlanError, "target identity"):
                MODULE.validate()

    def test_capsule_hash_mutation_fails(self) -> None:
        # `MODULE.validate()` calls `json.loads` a SECOND time if the target fact
        # file's on-disk digest no longer matches the plan's recorded
        # `fact_file_sha256` (a real, unrelated event: the fact can be settled
        # further after this plan was frozen). Patching `json.loads` globally to
        # `return_value=changed` for every call -- as this test previously did --
        # makes that second read return the mutated PLAN dict too, so the
        # fact-settlement fallback sees a malformed "fact" and raises "target
        # fact changed without axiom-free kernel settlement" before validate()
        # ever reaches the capsule-hash check this test means to isolate. Scope
        # the substitution to the exact PLAN text instead, so any OTHER
        # `json.loads` call (the live fact file) still gets real data.
        plan_text = MODULE.PLAN.read_text()
        original = MODULE.json.loads(plan_text)
        changed = copy.deepcopy(original)
        changed["accepted_inputs"][0]["capsule_sha256"] = "0" * 64
        real_loads = MODULE.json.loads

        def fake_loads(text, *args, **kwargs):
            if text == plan_text:
                return changed
            return real_loads(text, *args, **kwargs)

        with mock.patch.object(MODULE.json, "loads", side_effect=fake_loads):
            with self.assertRaisesRegex(MODULE.PlanError, "input identity"):
                MODULE.validate()

    def test_submission_budget_mutation_fails(self) -> None:
        # Same scoping requirement as test_capsule_hash_mutation_fails above.
        plan_text = MODULE.PLAN.read_text()
        original = MODULE.json.loads(plan_text)
        changed = copy.deepcopy(original)
        changed["budget"]["target_theorem_submissions"] = 1
        real_loads = MODULE.json.loads

        def fake_loads(text, *args, **kwargs):
            if text == plan_text:
                return changed
            return real_loads(text, *args, **kwargs)

        with mock.patch.object(MODULE.json, "loads", side_effect=fake_loads):
            with self.assertRaisesRegex(MODULE.PlanError, "budget"):
                MODULE.validate()


if __name__ == "__main__":
    unittest.main()
