from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-public-gcd-def-direct-reconstruction-plan.py"
SPEC = importlib.util.spec_from_file_location("public_gcd_def_direct_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class PublicGcdDefDirectPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PublicGcdDefDirectPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_target_change_is_rejected(self) -> None:
        self.reject(lambda value: value["target"].__setitem__("name", "other"), "target")

    def test_fix_equation_permission_is_rejected(self) -> None:
        self.reject(
            lambda value: value["construction"]["forbidden_dependencies"].remove(
                "WellFounded.Nat.fix_eq"
            ),
            "construction",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(lambda value: value["budget"].__setitem__("max_retries", 1), "budget")

    def test_equation_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("public_gcd_equation_credit", 1),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
