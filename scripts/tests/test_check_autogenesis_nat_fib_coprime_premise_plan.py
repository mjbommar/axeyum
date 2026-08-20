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
        changed["authority"]["kernel_submissions"] = 1
        with self.assertRaisesRegex(MODULE.PlanError, "authority"):
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


if __name__ == "__main__":
    unittest.main()
