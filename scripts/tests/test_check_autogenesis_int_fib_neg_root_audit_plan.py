from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-int-fib-neg-root-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("int_fib_neg_root_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IntFibNegRootAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.IntFibNegRootAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_change_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_root"].__setitem__("name", "Int.gcd_fib"), "fixed proof-free root")

    def test_remote_baseline_change_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_environment"]["mathlib_untracked_baseline"].__setitem__("AxeyumFibGeneric.lean", "0" * 64), "fixed fleet environment")

    def test_second_export_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_exporter_invocations", 2), "audit budget")

    def test_reconstruction_authority_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("reconstruction_allowed", True), "audit authority")

    def test_proof_rendering_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_measurement"].__setitem__("proof_terms_types_or_values_may_be_rendered", True), "fixed measurement")


if __name__ == "__main__":
    unittest.main()
