from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-official-kernel-plan.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_official_kernel_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutOfficialKernelPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutOfficialKernelPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_target_change(self) -> None:
        self.reject(lambda value: value["inputs"]["target_base"].__setitem__("sha256", "0" * 64))

    def test_rejects_leaf_change(self) -> None:
        self.reject(lambda value: value["inputs"]["successor"].__setitem__("root", "Nat.gcd_succ"))

    def test_rejects_proof_rendering(self) -> None:
        self.reject(lambda value: value["implementation"].__setitem__("proof_terms_types_or_values_may_be_rendered", True))

    def test_rejects_one_invocation(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("fresh_complete_invocations", 1))

    def test_rejects_dependency_weakening(self) -> None:
        self.reject(lambda value: value["acceptance"]["forbidden_dependencies"].pop())

    def test_rejects_stream_read_increase(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_input_stream_reads", 11))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exact_fibonacci_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
