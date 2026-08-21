from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan.py"
SPEC = importlib.util.spec_from_file_location("clean_dvd_antisymm_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CleanDvdAntisymmPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.CleanDvdAntisymmPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_one_run(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("fresh_complete_invocations", 1))

    def test_rejects_official_le_of_dvd(self) -> None:
        self.reject(lambda value: value["construction"]["clean_le_of_dvd"].__setitem__("source", "reuse official Nat.le_of_dvd"))

    def test_rejects_dependency_loss(self) -> None:
        self.reject(lambda value: value["construction"]["clean_dvd_antisymm"]["required_direct_dependencies"].pop())

    def test_rejects_axiom(self) -> None:
        self.reject(lambda value: value["construction"]["clean_le_of_dvd"].__setitem__("axiom_footprint", ["propext"]))

    def test_rejects_rendering(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("proof_terms_types_or_values_may_be_rendered", True))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exact_target_submissions", 1))

    def test_rejects_early_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("support_credit", 1))


if __name__ == "__main__":
    unittest.main()
