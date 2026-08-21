from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-mathlib-stable-statement-comparison.py"
SPEC = importlib.util.spec_from_file_location("stable_statement_comparison", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class StableStatementComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.comparison = json.loads(MODULE.OUTPUT.read_text())

    def reject(self, mutate) -> None:
        changed = copy.deepcopy(self.comparison)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.ComparisonError, "comparison differs"):
            MODULE.validate(changed)

    def test_exact_comparison_is_accepted(self) -> None:
        MODULE.validate(self.comparison)

    def test_row_removal_is_rejected(self) -> None:
        self.reject(lambda value: value["rows"].pop())

    def test_class_mutation_is_rejected(self) -> None:
        self.reject(
            lambda value: value["rows"][0].__setitem__(
                "class", "absent-in-current-stable"
            )
        )

    def test_inventory_identity_is_rejected(self) -> None:
        self.reject(
            lambda value: value["comparison"].__setitem__("inventory_sha256", "0" * 64)
        )

    def test_proof_body_read_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__(
                "mathlib_source_proof_bodies_read", 1
            )
        )

    def test_extractor_patch_is_rejected(self) -> None:
        self.reject(
            lambda value: value["extractor"].__setitem__("compatibility_patches", 1)
        )

    def test_fact_change_is_rejected(self) -> None:
        self.reject(lambda value: value["authority"].__setitem__("fact_status_changes", 1))


if __name__ == "__main__":
    unittest.main()
