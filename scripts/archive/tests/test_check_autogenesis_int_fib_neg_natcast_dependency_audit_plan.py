from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-int-fib-neg-natcast-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("int_fib_neg_natcast_dependency_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IntFibNegNatcastDependencyAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.IntFibNegNatcastDependencyAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_omission_is_rejected(self) -> None:
        self.reject(lambda value: value["ordered_roots"].pop(), "exact child frontier")

    def test_second_read_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_proof_bearing_stream_reads", 2), "audit budget")

    def test_reconstruction_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("reconstruction_allowed", True), "audit authority")


if __name__ == "__main__":
    unittest.main()
