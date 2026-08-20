from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-fib-coprime-premise-plan.py"
SPEC = importlib.util.spec_from_file_location("check_fib_coprime_plan", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FibCoprimePremisePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads(MODULE.MANIFEST.read_text())

    def test_exact_plan_is_accepted(self) -> None:
        MODULE.validate(self.manifest)

    def test_probe_and_authority_mutations_are_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"]["first_conflict"] = "Nat"
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"][
            "kernel_type_shape_compatible_content_mismatches"
        ] = 9
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["authority"]["kernel_submissions"] = 4
        with self.assertRaisesRegex(MODULE.PlanError, "authority"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_probe"]["api_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "API"):
            MODULE.validate(changed)

    def test_required_surface_mutation_is_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["proof_plan"]["required_native_declarations"][0] = "Nat.rec"
        with self.assertRaisesRegex(MODULE.PlanError, "semantics"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["target"]["sole_admitted_theorem_premise"] = "F:unreviewed"
        with self.assertRaisesRegex(MODULE.PlanError, "premise"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["closure_census"]["first_dependency_count"] = 9
        with self.assertRaisesRegex(MODULE.PlanError, "closure census"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["added_theorem_names"].pop()
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["singleton_inductive_result"]["added_singleton_inductives"][0][
            "constructors"
        ] = []
        with self.assertRaisesRegex(MODULE.PlanError, "singleton inductive"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["receipt_sha256"] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["reused_exact_declarations"] = 3
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["composition_result"]["reused_compatibility"][
            "translated-definitional-equality"
        ] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "composition result"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["definition_result"]["added_definitions"][0][
            "target_declaration_sha256"
        ] = "0" * 64
        with self.assertRaisesRegex(MODULE.PlanError, "definition composition"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["definition_result"]["added_definitions"][1]["reducibility"] = (
            "regular:3"
        )
        with self.assertRaisesRegex(MODULE.PlanError, "definition composition"):
            MODULE.validate(changed)

        changed = copy.deepcopy(self.manifest)
        changed["definition_result"]["reused_compatibility"][
            "translated-definitional-equality"
        ] = 3
        with self.assertRaisesRegex(MODULE.PlanError, "definition composition"):
            MODULE.validate(changed)


if __name__ == "__main__":
    unittest.main()
