from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan.py"
SPEC = importlib.util.spec_from_file_location("balanced_bezout_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BalancedBezoutPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.BalancedBezoutPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_public_quotient(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("public_quotient_used", True))

    def test_rejects_removed_forbidden_dependency(self) -> None:
        self.reject(lambda value: value["construction"]["forbidden_dependencies"].pop())

    def test_rejects_closed_specialization_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("target_specialization_credit", 1))

    def test_rejects_fibonacci_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exact_fibonacci_target_submissions", 1))

    def test_rejects_mutable_preexisting_file(self) -> None:
        self.reject(lambda value: value["preexisting_status_baseline"][0].__setitem__("sha256", "0" * 64))

    def test_rejects_more_compilations(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_source_compilations", 3))

    def test_rejects_readable_proof_stream(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("proof_bodies_readable_by_model", True))


if __name__ == "__main__":
    unittest.main()
