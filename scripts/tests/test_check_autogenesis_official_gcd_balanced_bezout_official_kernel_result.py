from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-official-kernel-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_official_kernel_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutOfficialKernelResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutOfficialKernelResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_second_invocation(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("complete_invocations", 2))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("retries", 1))

    def test_rejects_decline_change(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("first_rejected", "WellFounded.fix"))

    def test_rejects_partial_publication(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("partial_kernel_published", True))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_reverse_boundary_loss(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("generic_kernel_as_base_selected", False))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("exact_fibonacci_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
