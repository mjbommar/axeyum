from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-euclidean-dependency-footprint-audit-plan.py"
SPEC = importlib.util.spec_from_file_location("euclidean_dependency_audit_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanDependencyAuditPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = MODULE.load(MODULE.PLAN)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.AuditPlanError, message):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_population_reselection_is_rejected(self) -> None:
        self.reject(lambda value: value["fixed_population"].pop(), "population")

    def test_second_importer_run_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_importer_runs", 2),
            "audit budget",
        )

    def test_retry_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_retries", 1),
            "audit budget",
        )

    def test_revised_proof_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("revised_euclidean_proof_allowed", True),
            "audit authority",
        )

    def test_proof_rendering_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_measurement"].__setitem__(
                "proof_terms_or_values_may_be_rendered", True
            ),
            "fixed measurement",
        )


if __name__ == "__main__":
    unittest.main()
