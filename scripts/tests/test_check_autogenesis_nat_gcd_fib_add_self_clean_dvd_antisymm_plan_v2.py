from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v2.py"
SPEC = importlib.util.spec_from_file_location("clean_dvd_antisymm_plan_v2", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CleanDvdAntisymmPlanV2Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.CleanDvdAntisymmPlanV2Error):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_cross_kernel_rule(self) -> None:
        self.reject(lambda value: value["construction"].__setitem__("kernel_identity_rule", "reuse numeric handles"))

    def test_rejects_dependency_change(self) -> None:
        self.reject(lambda value: value["construction"]["clean_dvd_antisymm"]["required_direct_dependencies"].append("Eq.symm"))

    def test_rejects_transport_root_loss(self) -> None:
        self.reject(lambda value: value["construction"]["transport_roots"].pop())

    def test_rejects_second_stream(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_input_stream_reads", 4))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exact_target_submissions", 1))

    def test_rejects_early_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("support_credit", 1))


if __name__ == "__main__":
    unittest.main()
