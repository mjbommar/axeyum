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
        original = MODULE.json.loads(MODULE.PLAN.read_text())
        changed = copy.deepcopy(original)
        changed["accepted_inputs"][0]["capsule_sha256"] = "0" * 64
        with mock.patch.object(MODULE.json, "loads", return_value=changed):
            with self.assertRaisesRegex(MODULE.PlanError, "input identity"):
                MODULE.validate()

    def test_submission_budget_mutation_fails(self) -> None:
        original = MODULE.json.loads(MODULE.PLAN.read_text())
        changed = copy.deepcopy(original)
        changed["budget"]["target_theorem_submissions"] = 1
        with mock.patch.object(MODULE.json, "loads", return_value=changed):
            with self.assertRaisesRegex(MODULE.PlanError, "budget"):
                MODULE.validate()


if __name__ == "__main__":
    unittest.main()
