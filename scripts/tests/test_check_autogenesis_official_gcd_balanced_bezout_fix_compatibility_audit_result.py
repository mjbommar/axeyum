from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-fix-compatibility-audit-result.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_fix_audit_result", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutFixAuditResultTests(unittest.TestCase):
    def setUp(self) -> None:
        self.result = MODULE.load(MODULE.RESULT)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.result)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutFixAuditResultError):
            MODULE.validate(changed)

    def test_current_result_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.result))

    def test_rejects_closure_count_drift(self) -> None:
        self.reject(lambda value: value["observation"].__setitem__("source_closure_count", 8))

    def test_rejects_missing_name_loss(self) -> None:
        self.reject(lambda value: value["observation"]["missing_target_names"].pop())

    def test_rejects_class_drift(self) -> None:
        self.reject(lambda value: value["observation"]["class_counts"].__setitem__("type-shape-mismatch", 0))

    def test_rejects_root_shape_drift(self) -> None:
        self.reject(lambda value: value["observation"].__setitem__("target_root_type_shape_sha256", "0" * 64))

    def test_rejects_translation_authority(self) -> None:
        self.reject(lambda value: value["selected_next_boundary"].__setitem__("translation_authorized", True))

    def test_rejects_retry_authority(self) -> None:
        self.reject(lambda value: value["selected_next_boundary"].__setitem__("closed_specialization_retry_authorized", True))

    def test_rejects_closed_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("closed_gcd_balanced_bezout_credit", 1))

    def test_rejects_theorem_submission(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("closed_theorem_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
