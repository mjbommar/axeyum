"""Discriminating input controls for the Rules-as-Code pack validator."""
import importlib.util
from pathlib import Path
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
            with self.subTest(value=value), self.assertRaises(checker.ValidationError):
                checker.require_date("date", value)

    def test_date_shape(self):
        for value in (None, 20240101, "2024-1-01", "2024-01-01T00:00:00", "２０２４-０１-０１"):
            with self.subTest(value=value), self.assertRaises(checker.ValidationError):
                checker.require_date("date", value)

    def test_integer_values(self):
        for value in (0, -1, 2**200):
            self.assertEqual(checker.require_int("count", value), value)

    def test_boolean_is_not_integer(self):
        for value in (True, False):
            with self.subTest(value=value), self.assertRaises(checker.ValidationError):
                checker.require_int("count", value)

    def test_non_integer_values(self):
        for value in (None, "1", 1.0):
            with self.subTest(value=value), self.assertRaises(checker.ValidationError):
                checker.require_int("count", value)


if __name__ == "__main__":
    unittest.main()
