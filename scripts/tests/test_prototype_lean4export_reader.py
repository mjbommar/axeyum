#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "prototype_lean4export_reader.py"
FIXTURE = ROOT / "docs" / "plan" / "fixtures" / "lean4export-v4.30-axeyum-probe.ndjson"
SPEC = importlib.util.spec_from_file_location("prototype_lean4export_reader", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PROBE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PROBE
SPEC.loader.exec_module(PROBE)


def lines(*records: dict) -> list[str]:
    return [json.dumps(record) + "\n" for record in records]


META = {
    "meta": {
        "exporter": {"name": "lean4export", "version": "3.1.0"},
        "format": {"version": "3.1.0"},
        "lean": {"githash": "test", "version": "4.30.0"},
    }
}


class ProbeTests(unittest.TestCase):
    def test_official_probe_inventory(self) -> None:
        result = PROBE.probe_path(FIXTURE)
        self.assertEqual((result.names, result.levels, result.exprs, result.decls), (14, 2, 43, 5))
        self.assertEqual(result.blockers, ())
        self.assertEqual(result.declaration_kinds, {"axiom": 1, "def": 2, "inductive": 1, "thm": 1})

    def test_unknown_record_fails_closed(self) -> None:
        with self.assertRaisesRegex(PROBE.ProbeError, "exactly one record kind"):
            PROBE.probe_lines(lines(META, {"mystery": {}}))

    def test_forward_expression_reference_fails(self) -> None:
        with self.assertRaisesRegex(PROBE.ProbeError, "forward or missing reference"):
            PROBE.probe_lines(lines(META, {"ie": 0, "app": {"fn": 1, "arg": 1}}))

    def test_projection_literal_and_quotient_are_blockers(self) -> None:
        records = lines(
            META,
            {"in": 1, "str": {"pre": 0, "str": "T"}},
            {"ie": 0, "bvar": 0},
            {"ie": 1, "proj": {"typeName": 1, "idx": 0, "struct": 0}},
            {"ie": 2, "natVal": "340282366920938463463374607431768211456"},
            {"ie": 3, "strVal": "x"},
            {"quot": {"name": 1, "levelParams": [], "type": 0, "kind": "type"}},
        )
        result = PROBE.probe_lines(records)
        self.assertEqual(
            set(result.blockers),
            {
                "expr-projection",
                "literal-nat-bignum-and-typing",
                "literal-string-typing",
                "quotient-package",
            },
        )

    def test_partial_definition_is_rejected(self) -> None:
        records = lines(
            META,
            {"in": 1, "str": {"pre": 0, "str": "loop"}},
            {"ie": 0, "sort": 0},
            {
                "def": {
                    "name": 1,
                    "levelParams": [],
                    "type": 0,
                    "value": 0,
                    "hints": "opaque",
                    "safety": "partial",
                    "all": [1],
                }
            },
        )
        with self.assertRaisesRegex(PROBE.ProbeError, "unsafe/partial"):
            PROBE.probe_lines(records)


if __name__ == "__main__":
    unittest.main()
