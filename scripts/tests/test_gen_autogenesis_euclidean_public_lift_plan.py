from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-euclidean-public-lift-plan.py"
SPEC = importlib.util.spec_from_file_location("euclidean_public_lift_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class EuclideanPublicLiftPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = json.loads(MODULE.OUTPUT.read_text())

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.plan)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.PublicLiftPlanError, "differs"):
            MODULE.validate(changed)

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.plan)

    def test_statement_population_expansion_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_lift"].__setitem__(
                "additional_statement_names_allowed", 1
            )
        )

    def test_official_proof_access_is_rejected(self) -> None:
        self.reject(
            lambda value: value["fixed_lift"].__setitem__(
                "official_nat_div_add_mod_proof_allowed", True
            )
        )

    def test_type_identity_gate_is_rejected(self) -> None:
        self.reject(
            lambda value: value["target"].__setitem__(
                "required_type_relation", "pretty-type-equal"
            )
        )

    def test_third_submission_is_rejected(self) -> None:
        self.reject(
            lambda value: value["budget"].__setitem__("max_kernel_theorem_submissions", 3)
        )

    def test_bezout_authority_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "balanced_bezout_reconstruction_allowed", True
            )
        )


if __name__ == "__main__":
    unittest.main()
