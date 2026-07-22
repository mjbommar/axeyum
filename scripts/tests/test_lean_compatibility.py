from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_compatibility",
    ROOT / "scripts" / "gen-lean-compatibility.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanCompatibilityContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_manifest()

    def row(self, row_id: str) -> dict:
        return next(row for row in self.data["rows"] if row["id"] == row_id)

    def failures(self) -> list[str]:
        return GEN.validate_manifest(self.data)

    def test_committed_contract_is_valid_and_rendering_is_deterministic(self) -> None:
        self.assertEqual(self.failures(), [])
        first = GEN.render(self.data)
        second = GEN.render(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        self.assertIn("| `K1-import` |", first)
        self.assertIn("`literal-string-typing`", first)
        self.assertNotIn("`inductive-mutual`", first)
        self.assertNotIn("`literal-nat-typing`", first)

    def test_translation_cannot_receive_credit_without_parsing(self) -> None:
        row = self.row("lean4export-flat-fixture")
        row["states"]["parsed"] = "not_attempted"
        self.assertTrue(
            any("translation outcome requires parsed=succeeded" in failure for failure in self.failures())
        )

    def test_official_oracle_cannot_grant_independent_admission(self) -> None:
        row = self.row("official-source-selected-reconstruction")
        row["states"]["admitted"] = "succeeded"
        self.assertTrue(
            any("independent admission requires" in failure for failure in self.failures())
        )

    def test_proof_credit_requires_independent_admission(self) -> None:
        row = self.row("planned-native-proof-profile")
        row["states"]["proof_checked"] = "succeeded"
        self.assertTrue(
            any("proof checking requires admitted=succeeded" in failure for failure in self.failures())
        )

    def test_declines_require_registered_codes_and_codes_require_declines(self) -> None:
        row = self.row("lean4export-quotient-root")
        row["decline_codes"] = []
        self.assertTrue(
            any("declined assurance requires a decline code" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        row = self.row("lean4export-flat-fixture")
        row["decline_codes"] = ["quotient-package"]
        self.assertTrue(
            any("decline code without a declined assurance" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        row = self.row("lean4export-quotient-root")
        row["decline_codes"] = ["invented-code"]
        self.assertTrue(
            any("unregistered decline codes" in failure for failure in self.failures())
        )

    def test_assurance_fields_and_evidence_are_fail_closed(self) -> None:
        row = self.row("lean4export-flat-fixture")
        del row["states"]["official_admitted"]
        self.assertTrue(
            any("assurance fields missing=" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        row = self.row("lean4export-flat-fixture")
        row["evidence"][0]["path"] = "docs/plan/fixtures/does-not-exist.ndjson"
        self.assertTrue(
            any("missing evidence path" in failure for failure in self.failures())
        )


if __name__ == "__main__":
    unittest.main()
