"""Discriminating input controls for the Rules-as-Code pack validator."""
import copy
import json
import importlib.util
from pathlib import Path
import shutil
import tempfile
from unittest.mock import patch
import sys
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "validate-rules-as-code.py"
spec = importlib.util.spec_from_file_location("rules_pack_checker", SCRIPT)
checker = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = checker
spec.loader.exec_module(checker)


class InputControls(unittest.TestCase):
    def test_valid_gregorian_dates(self):
        for value in ("0001-01-01", "9999-12-31", "2000-02-29", "2024-02-29", "1900-02-28"):
            self.assertEqual(checker.require_date("date", value), value)

    def test_invalid_gregorian_dates(self):
        for value in ("2023-02-29", "1900-02-29", "2024-04-31", "0000-01-01", "2024-00-01", "2024-01-00"):
            with self.assertRaises(checker.ValidationError):
                checker.require_date("date", value)

    def test_date_shape(self):
        for value in (None, 20240101, "2024-1-01", "2024-01-01T00:00:00", "２０２４-０１-０１"):
            with self.assertRaises(checker.ValidationError):
                checker.require_date("date", value)

    def test_integer_values(self):
        for value in (0, -1, 2**200):
            self.assertEqual(checker.require_int("count", value), value)

    def test_boolean_is_not_integer(self):
        for value in (True, False):
            with self.assertRaises(checker.ValidationError):
                checker.require_int("count", value)

    def test_non_integer_values(self):
        for value in (None, "1", 1.0):
            with self.assertRaises(checker.ValidationError):
                checker.require_int("count", value)


class MetadataControls(unittest.TestCase):
    def setUp(self):
        self.pack = SCRIPT.parent.parent / "docs/rules-as-code/examples/benefit-eligibility-v0"
        self.metadata = json.loads((self.pack / "metadata.json").read_text())

    def test_existing_and_finite_interval(self):
        checker.validate_metadata(self.pack, self.metadata)
        self.metadata["effective_interval"]["to"] = "2027-01-01"
        checker.validate_metadata(self.pack, self.metadata)

    def test_invalid_interval_dates(self):
        for field in ("from", "to"):
            metadata = copy.deepcopy(self.metadata)
            metadata["effective_interval"][field] = "2026-02-30"
            with self.assertRaises(checker.ValidationError):
                checker.validate_metadata(self.pack, metadata)

    def test_empty_or_reversed_interval(self):
        for end in ("2026-01-01", "2025-12-31"):
            metadata = copy.deepcopy(self.metadata)
            metadata["effective_interval"]["to"] = end
            with self.assertRaises(checker.ValidationError):
                checker.validate_metadata(self.pack, metadata)

    def test_missing_interval_start(self):
        self.metadata["effective_interval"] = {"to": None}
        with self.assertRaises(checker.ValidationError):
            checker.validate_metadata(self.pack, self.metadata)


class StatuteControls(unittest.TestCase):
    def test_committed_template_manifest(self):
        self.assertEqual(checker.validate_statute_templates(), (1, 0))

    def test_missing_certificate_population(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = SCRIPT.parent.parent / "docs/rules-as-code/statute-templates"
            target = root / "docs/rules-as-code/statute-templates"
            shutil.copytree(source, target)
            for fixture in target.glob("*/fixtures/*.certificate.json"):
                fixture.unlink()
            with patch.object(checker, "ROOT", root), self.assertRaises(checker.ValidationError):
                checker.validate_statute_templates()


if __name__ == "__main__":
    unittest.main()
