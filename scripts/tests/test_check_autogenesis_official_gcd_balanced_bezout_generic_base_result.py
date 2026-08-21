from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-generic-base-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_generic_base_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutGenericBaseResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutGenericBaseResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_second_invocation(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("complete_invocations", 2))

    def test_rejects_successful_composition(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("successful_composition_operations", 1))

    def test_rejects_decline_change(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("class", "missing"))

    def test_rejects_partial_publication(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("partial_kernel_published", True))

    def test_rejects_exact_reuse_loss(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("exact_reuse_selected", False))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_target_submission(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("exact_fibonacci_target_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
