from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-factorial-zero-family.py"
SPEC = importlib.util.spec_from_file_location(
    "check_autogenesis_factorial_zero_family", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FactorialZeroFamilyCheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = MODULE.load(MODULE.MANIFEST)
        self.members = MODULE.validate_structure(self.manifest)

    def test_exact_structure_is_accepted(self) -> None:
        self.assertEqual(len(self.members), 2)

    def test_held_out_access_is_rejected(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["population"]["held_out_inspected"] = True
        with self.assertRaisesRegex(MODULE.FamilyError, "isolation"):
            MODULE.validate_structure(changed)

    def test_family_cannot_expand_without_new_version(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["members"].append(copy.deepcopy(changed["members"][0]))
        changed["population"]["members"] = 3
        with self.assertRaisesRegex(MODULE.FamilyError, "population|exactly two"):
            MODULE.validate_structure(changed)

    def test_operation_authority_must_be_distinct(self) -> None:
        changed = copy.deepcopy(self.manifest)
        changed["members"][1]["operation_id"] = changed["members"][0]["operation_id"]
        with self.assertRaisesRegex(MODULE.FamilyError, "independently exact-bound"):
            MODULE.validate_structure(changed)

    def test_mutated_receipt_is_rejected(self) -> None:
        member = self.members[1]
        receipt = MODULE.expected_receipt(member)
        receipt["goal"] = "goal"
        receipt["proof"] = "proof"
        receipt["target_dependency"] = "true"
        with self.assertRaisesRegex(MODULE.FamilyError, "receipt changed"):
            MODULE.validate_member_receipt(member, receipt)

    def test_open_credit_cannot_smuggle_admission_fields(self) -> None:
        with self.assertRaisesRegex(MODULE.FamilyError, "admission fields"):
            MODULE.validate_credit(
                self.members[1],
                {
                    "epistemic_status": "open",
                    "evidence": [],
                    "proof_route": "kernel-lean",
                },
            )


if __name__ == "__main__":
    unittest.main()
