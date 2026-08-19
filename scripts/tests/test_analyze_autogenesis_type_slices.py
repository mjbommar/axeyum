from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "analyze-autogenesis-type-slices.py"
SPEC = importlib.util.spec_from_file_location("analyze_autogenesis_type_slices", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def records(*declarations):
    prefix = [
        {"meta": {}},
        {"in": 1, "str": {"pre": 0, "str": "trusted"}},
        {"in": 2, "str": {"pre": 0, "str": "helper"}},
        {"in": 3, "str": {"pre": 0, "str": "target"}},
        {"ie": 0, "sort": 0},
        {"ie": 1, "const": {"name": 1, "us": []}},
        {"ie": 2, "const": {"name": 2, "us": []}},
    ]
    return prefix + list(declarations)


def write_stream(path: Path, values) -> None:
    path.write_text("".join(json.dumps(value) + "\n" for value in values))


class TypeSliceAnalysisTests(unittest.TestCase):
    def analyze(self, values):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "target.ndjson"
            write_stream(path, values)
            return MODULE.analyze_stream(path, "target")

    def test_unrelated_theorem_does_not_enter_either_closure(self):
        result = self.analyze(
            records(
                {"thm": {"name": 1, "type": 0, "value": 0}},
                {"def": {"name": 3, "type": 0, "value": 0}},
            )
        )
        self.assertEqual(result.implementation_trusted, ())
        self.assertEqual(result.type_trusted, ())

    def test_theorem_reached_only_through_helper_body_stops_at_type_boundary(self):
        result = self.analyze(
            records(
                {"thm": {"name": 1, "type": 0, "value": 0}},
                {"def": {"name": 2, "type": 0, "value": 1}},
                {"def": {"name": 3, "type": 0, "value": 2}},
            )
        )
        self.assertEqual(result.implementation_trusted, ("trusted",))
        self.assertEqual(result.type_trusted, ())
        self.assertEqual(result.abstractable_type_boundary, ("helper",))

    def test_direct_theorem_reference_remains_a_hard_type_boundary_rejection(self):
        result = self.analyze(
            records(
                {"thm": {"name": 1, "type": 0, "value": 0}},
                {"def": {"name": 3, "type": 0, "value": 1}},
            )
        )
        self.assertEqual(result.type_trusted, ("trusted",))

    def test_forward_expression_reference_fails_closed(self):
        values = records({"def": {"name": 3, "type": 0, "value": 0}})
        values.insert(4, {"ie": 9, "app": {"fn": 0, "arg": 0}})
        with self.assertRaisesRegex(MODULE.TypeSliceError, "expected dense expression"):
            self.analyze(values)

    def test_duplicate_target_declaration_fails_closed(self):
        with self.assertRaisesRegex(MODULE.TypeSliceError, "duplicate declaration"):
            self.analyze(
                records(
                    {"def": {"name": 3, "type": 0, "value": 0}},
                    {"def": {"name": 3, "type": 0, "value": 0}},
                )
            )


if __name__ == "__main__":
    unittest.main()
