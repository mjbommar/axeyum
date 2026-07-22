from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_axiom_ledger",
    ROOT / "scripts" / "gen-lean-axiom-ledger.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanAxiomLedgerContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        # Construct the three preludes once.  Individual mutation tests then
        # exercise the manifest contract without repeatedly invoking Cargo.
        cls.source_rows = GEN.run_source_inventory()

    def setUp(self) -> None:
        self.data = GEN.load_manifest()

    def failures(self) -> list[str]:
        return GEN.validate_manifest(self.data, self.source_rows)

    def test_committed_ledger_matches_runtime_and_renders_deterministically(self) -> None:
        self.assertEqual(self.failures(), [])
        counts = Counter(row["prelude"] for row in self.source_rows)
        self.assertEqual(counts, {"integer": 34, "real": 30, "string": 1})
        self.assertEqual(len(self.source_rows), 65)
        first = GEN.render(self.data)
        second = GEN.render(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        self.assertIn("**65 total assumptions:** real 30, integer 34, string 1", first)
        self.assertIn("`axeyum.string.append`", first)

    def test_missing_and_extra_runtime_entries_fail(self) -> None:
        removed = self.data["entries"].pop()
        failures = self.failures()
        self.assertTrue(any("ledger must contain 65 entries" in failure for failure in failures))
        self.assertTrue(any("ledger missing source axioms" in failure for failure in failures))

        self.data = GEN.load_manifest()
        extra = copy.deepcopy(removed)
        extra["name"] = "invented"
        self.data["entries"].append(extra)
        self.data["entries"].sort(key=GEN.entry_key)
        self.assertTrue(any("ledger has non-source axioms" in failure for failure in self.failures()))

    def test_duplicate_entry_fails(self) -> None:
        self.data["entries"].append(copy.deepcopy(self.data["entries"][-1]))
        self.assertTrue(any("duplicate prelude/name" in failure for failure in self.failures()))

    def test_name_preserving_type_and_digest_drift_fail(self) -> None:
        self.data["entries"][0]["canonical_type"] += " "
        failures = self.failures()
        self.assertTrue(any("canonical type drift" in failure for failure in failures))
        self.assertTrue(any("stored type and digest disagree" in failure for failure in failures))

        self.data = GEN.load_manifest()
        self.data["entries"][0]["type_sha256"] = "0" * 64
        failures = self.failures()
        self.assertTrue(any("type digest drift" in failure for failure in failures))
        self.assertTrue(any("stored type and digest disagree" in failure for failure in failures))

    def test_classification_and_discharge_states_are_closed_enums(self) -> None:
        self.data["entries"][0]["classification"] = "probably-okay"
        self.assertTrue(any("invalid classification" in failure for failure in self.failures()))

        self.data = GEN.load_manifest()
        self.data["entries"][0]["discharge_status"] = "done-ish"
        self.assertTrue(any("invalid discharge_status" in failure for failure in self.failures()))

    def test_discharged_requires_retained_repository_evidence(self) -> None:
        self.data["entries"][0]["discharge_status"] = "discharged"
        self.assertTrue(
            any("discharged row requires retained evidence" in failure for failure in self.failures())
        )

    def test_derivable_theorem_cannot_be_retained_as_an_axiom(self) -> None:
        self.data["entries"][0]["classification"] = "derivable-theorem"
        self.data["entries"][0]["discharge_status"] = "retained"
        self.assertTrue(
            any("derivable theorem cannot be retained" in failure for failure in self.failures())
        )


if __name__ == "__main__":
    unittest.main()
