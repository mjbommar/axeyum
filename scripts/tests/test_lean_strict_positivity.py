from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lean_strict_positivity",
    ROOT / "scripts" / "check-lean-strict-positivity.py",
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class LeanStrictPositivitySourceFreezeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = CHECK.load_manifest()

    def failures(self) -> list[str]:
        return CHECK.validate_manifest(self.data)

    def test_committed_source_freeze_is_valid(self) -> None:
        self.assertEqual(self.failures(), [])

    def test_source_hash_drift_rejects(self) -> None:
        self.data["sources"]["negative-mixed"]["sha256"] = "0" * 64
        self.assertTrue(any("source hash drift" in item for item in self.failures()))

    def test_case_population_order_and_identity_are_frozen(self) -> None:
        self.data["cases"].pop()
        self.assertTrue(any("case population" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["cases"][0], self.data["cases"][1] = (
            self.data["cases"][1],
            self.data["cases"][0],
        )
        self.assertTrue(any("case population" in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["cases"][1]["id"] = self.data["cases"][0]["id"]
        failures = self.failures()
        self.assertTrue(any("case population" in item for item in failures))
        self.assertTrue(any("case IDs must be unique" in item for item in failures))

    def test_rule_class_drift_rejects(self) -> None:
        self.data["cases"][4]["expected_rule_class"] = "positive-pi-codomain"
        self.assertTrue(any("case population" in item for item in self.failures()))

    def test_pin_resource_and_command_drift_rejects(self) -> None:
        mutations = (
            ("pins", "lean_git_commit", "0" * 40, "Lean pin drift"),
            ("resource_policy", "memory_max", "8G", "resource policy drift"),
        )
        for section, key, value, message in mutations:
            with self.subTest(section=section, key=key):
                mutated = copy.deepcopy(CHECK.load_manifest())
                mutated[section][key] = value
                self.data = mutated
                self.assertTrue(any(message in item for item in self.failures()))

        self.data = CHECK.load_manifest()
        self.data["commands"]["lean_argv_template"][3] = "-j8"
        self.assertTrue(any("Lean argv template drift" in item for item in self.failures()))

    def test_negative_diagnostic_cannot_be_removed(self) -> None:
        self.data["sources"]["negative-deep"]["expected_diagnostic_substring"] = None
        self.assertTrue(any("negative diagnostic drift" in item for item in self.failures()))

    def test_case_and_source_outcomes_must_agree(self) -> None:
        self.data["cases"][3]["expected_official_outcome"] = "accepted"
        failures = self.failures()
        self.assertTrue(any("case population" in item for item in failures))
        self.assertTrue(any("case/source outcome drift" in item for item in failures))

    def test_source_freeze_rejects_premature_observations(self) -> None:
        self.data["official_observations"] = {"negative-mixed": "rejected"}
        failures = self.failures()
        self.assertTrue(any("top-level fields drift" in item for item in failures))
        self.assertTrue(any("premature observations" in item for item in failures))


if __name__ == "__main__":
    unittest.main()
