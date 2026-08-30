from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-fix-compatibility-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_balanced_bezout_fix_audit_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdBalancedBezoutFixAuditPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdBalancedBezoutFixAuditPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_root_drift(self) -> None:
        self.reject(lambda value: value["implementation"].__setitem__("root", "WellFounded.fix_eq"))

    def test_rejects_proof_rendering_scope(self) -> None:
        self.reject(lambda value: value["implementation"]["forbidden_rendered_fields"].pop())

    def test_rejects_shape_drift(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("root_source_type_shape_sha256", "0" * 64))

    def test_rejects_one_invocation(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("fresh_complete_invocations", 1))

    def test_rejects_transport_authority(self) -> None:
        self.reject(lambda value: value["acceptance"].__setitem__("transport_or_reconstruction_may_be_authorized", True))

    def test_rejects_theorem_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_closed_theorem_submissions", 1))

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_translation_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("translation_credit", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
