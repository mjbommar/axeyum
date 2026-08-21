from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-int-fib-of-odd-private-root-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("int_fib_of_odd_private_root_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class IntFibOfOddPrivateRootAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaises(MODULE.IntFibOfOddPrivateRootAuditPlanError):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_private_root_is_bound(self) -> None:
        self.reject(lambda value: value.__setitem__("fixed_root", "Int.fib_of_odd"))

    def test_second_read_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_proof_bearing_stream_reads", 2))

    def test_reconstruction_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("reconstruction_allowed", True))


if __name__ == "__main__":
    unittest.main()
