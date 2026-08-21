from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-extended-gcd-dependency-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("extended_gcd_dependency_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ExtendedGcdDependencyAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(
            MODULE.ExtendedGcdDependencyAuditPlanError, message
        ):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_root_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_roots"].pop(), "fixed dependency roots")

    def test_core_expansion_is_rejected(self) -> None:
        self.reject(
            lambda value: value["candidate_coefficient_core"].append("Eq.trans"),
            "fixed dependency roots",
        )

    def test_export_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_exporter_invocations", 1),
            "audit budget",
        )

    def test_reconstruction_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "reconstruction_allowed", True
            ),
            "audit authority",
        )

    def test_successor_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["decision_rule"].__setitem__(
                "authorize_either_successor_in_this_increment", True
            ),
            "successor decision rule",
        )


if __name__ == "__main__":
    unittest.main()
