from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-closed-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_closed_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutClosedResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutClosedResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_blocker_name_drift(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("first_rejected", "WellFounded.fix_eq"))

    def test_rejects_source_shape_drift(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("source_type_shape_sha256", "0" * 64))

    def test_rejects_target_shape_drift(self) -> None:
        self.reject(lambda value: value["decline"].__setitem__("target_type_shape_sha256", "0" * 64))

    def test_rejects_second_invocation(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("complete_invocations", 2))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("retries", 1))

    def test_rejects_closed_submission(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("closed_theorem_submissions", 1))

    def test_rejects_compatibility_override(self) -> None:
        self.reject(lambda value: value["next_boundary"].__setitem__("compatibility_override_authorized", True))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
