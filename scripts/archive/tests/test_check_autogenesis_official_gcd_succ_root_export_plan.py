from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PATH = ROOT / "scripts/check-autogenesis-official-gcd-succ-root-export-plan.py"
SPEC = importlib.util.spec_from_file_location("official_gcd_succ_root_export_plan", PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OfficialGcdSuccRootExportPlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutation) -> None:
        changed = copy.deepcopy(self.plan)
        mutation(changed)
        with self.assertRaises(MODULE.OfficialGcdSuccRootExportPlanError):
            MODULE.validate(changed)

    def test_current_plan_passes(self) -> None:
        MODULE.validate(copy.deepcopy(self.plan))

    def test_rejects_source_change(self) -> None:
        self.reject(lambda value: value["inputs"]["authored_source"].__setitem__("sha256", "0" * 64))

    def test_rejects_representation_reason_loss(self) -> None:
        self.reject(lambda value: value["inputs"].__setitem__("representation_reason", "native"))

    def test_rejects_root_change(self) -> None:
        self.reject(lambda value: value["export"]["ordered_roots"].__setitem__(0, "Nat.gcd_succ"))

    def test_rejects_ceiling_increase(self) -> None:
        self.reject(lambda value: value["export"].__setitem__("max_stream_bytes", 3000000))

    def test_rejects_environment_change(self) -> None:
        self.reject(lambda value: value["fixed_environment"].__setitem__("mathlib_commit", "0" * 40))

    def test_rejects_proof_rendering(self) -> None:
        self.reject(lambda value: value["execution"].__setitem__("proof_terms_types_or_values_may_be_rendered", True))

    def test_rejects_dependency_weakening(self) -> None:
        self.reject(lambda value: value["acceptance"]["forbidden_dependencies"].pop())

    def test_rejects_retry(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1))

    def test_rejects_successor_credit(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("new_official_gcd_succ_credit", 1))

    def test_rejects_closed_submission(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_closed_balanced_bezout_submissions", 1))

    def test_rejects_ledger_write(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("ledger_writes", 1))


if __name__ == "__main__":
    unittest.main()
