from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-public-equation-carrier-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("euclidean_equation_carrier_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanEquationCarrierAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.EquationCarrierAuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_population_change_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_population"].pop(),
            "direct child population",
        )

    def test_proof_rendering_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_measurement"].__setitem__(
                "proof_terms_or_values_may_be_rendered", True
            ),
            "fixed measurement",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "audit budget",
        )

    def test_replacement_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "public_equation_replacement_allowed", True
            ),
            "audit authority",
        )


if __name__ == "__main__":
    unittest.main()
