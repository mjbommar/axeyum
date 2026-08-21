"""Mutation controls for official clean-order V5 preregistration."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("plan_v5", ROOT / "scripts/check-autogenesis-official-r091-clean-dvd-antisymm-plan-v5.py")
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)

BOUNDARY_SPEC = importlib.util.spec_from_file_location("v5_v6", ROOT / "scripts/check-autogenesis-official-r091-clean-dvd-antisymm-v5-v6.py")
assert BOUNDARY_SPEC and BOUNDARY_SPEC.loader
BOUNDARY = importlib.util.module_from_spec(BOUNDARY_SPEC)
BOUNDARY_SPEC.loader.exec_module(BOUNDARY)

V7_SPEC = importlib.util.spec_from_file_location("v6_v7", ROOT / "scripts/check-autogenesis-official-r091-clean-dvd-antisymm-v6-v7.py")
assert V7_SPEC and V7_SPEC.loader
V7 = importlib.util.module_from_spec(V7_SPEC)
V7_SPEC.loader.exec_module(V7)

V8_SPEC = importlib.util.spec_from_file_location("v7_v8", ROOT / "scripts/check-autogenesis-official-r091-clean-dvd-antisymm-v7-v8.py")
assert V8_SPEC and V8_SPEC.loader
V8 = importlib.util.module_from_spec(V8_SPEC)
V8_SPEC.loader.exec_module(V8)


class PlanControls(unittest.TestCase):
    def test_live_plan_passes(self) -> None:
        self.assertEqual(CHECK.validate()["acceptance"]["exact_target_submissions"], 0)

    def test_support_mutation_fails(self) -> None:
        plan = copy.deepcopy(CHECK.load())
        plan["construction"]["supports"].pop()
        with self.assertRaises(CHECK.PlanError):
            CHECK.validate(plan)


class V5V6BoundaryControls(unittest.TestCase):
    def test_live_boundary_passes(self) -> None:
        self.assertEqual(BOUNDARY.validate()[0]["decline"]["name"], "Iff")

    def test_retry_mutation_fails(self) -> None:
        result, plan = BOUNDARY.validate()
        plan = copy.deepcopy(plan)
        plan["budget"]["max_retries"] = 1
        with self.assertRaises(BOUNDARY.BoundaryError):
            BOUNDARY.validate(result, plan)


class V6V7BoundaryControls(unittest.TestCase):
    def test_live_boundary_passes(self) -> None:
        self.assertEqual(V7.validate()[1]["new_support"]["name"], "Axeyum.Autogenesis.oneLeRightOfMulOfficialV1")

    def test_leaf_mutation_fails(self) -> None:
        result, plan = V7.validate()
        plan = copy.deepcopy(plan)
        plan["new_support"]["exact_required_theorem_leaves"].pop()
        with self.assertRaises(V7.BoundaryError):
            V7.validate(result, plan)


class V7V8BoundaryControls(unittest.TestCase):
    def test_live_boundary_passes(self) -> None:
        self.assertEqual(len(V8.validate()[1]["new_supports"]), 2)

    def test_support_mutation_fails(self) -> None:
        result, plan = V8.validate()
        plan = copy.deepcopy(plan)
        plan["new_supports"].pop()
        with self.assertRaises(V8.BoundaryError):
            V8.validate(result, plan)

    def test_target_budget_mutation_fails(self) -> None:
        plan = copy.deepcopy(CHECK.load())
        plan["budget"]["max_exact_target_submissions"] = 1
        with self.assertRaises(CHECK.PlanError):
            CHECK.validate(plan)


if __name__ == "__main__":
    unittest.main()
