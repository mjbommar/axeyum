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
RECURSIVE_FIXTURE = (
    ROOT / "docs" / "plan" / "fixtures" / "lean4export-v4.30-recursive-shapes.ndjson"
)
CONSTRUCT_FIXTURES = ROOT / "docs" / "plan" / "fixtures"
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
        self.assertEqual(
            (result.names, result.levels, result.exprs, result.decls), (14, 2, 43, 5)
        )
        self.assertEqual(result.blockers, ())
        self.assertEqual(
            result.declaration_kinds,
            {"axiom": 1, "def": 2, "inductive": 1, "thm": 1},
        )

    def test_official_direct_recursive_inventory(self) -> None:
        result = PROBE.probe_path(RECURSIVE_FIXTURE)
        self.assertEqual(
            (result.names, result.levels, result.exprs, result.decls), (30, 4, 130, 5)
        )
        self.assertEqual(result.blockers, ())
        self.assertEqual(result.declaration_kinds, {"def": 3, "inductive": 2})

    def test_official_construct_group_metadata(self) -> None:
        recursive = PROBE.probe_path(
            CONSTRUCT_FIXTURES
            / "lean4export-v4.30-construct-matrix-recursive-indexed.ndjson"
        )
        vector = next(
            inductive
            for group in recursive.inductive_groups
            for inductive in group.types
            if inductive.name == "AxeyumConstructMatrix.MiniVector"
        )
        self.assertEqual(
            (
                vector.num_params,
                vector.num_indices,
                vector.num_nested,
                vector.is_rec,
                vector.is_reflexive,
            ),
            (1, 1, 0, True, False),
        )

        mutual = PROBE.probe_path(
            CONSTRUCT_FIXTURES / "lean4export-v4.30-construct-matrix-mutual.ndjson"
        )
        mutual_group = next(
            group
            for group in mutual.inductive_groups
            if tuple(inductive.name for inductive in group.types)
            == (
                "AxeyumConstructMatrix.EvenTree",
                "AxeyumConstructMatrix.OddTree",
            )
        )
        self.assertEqual(
            tuple((recursor.num_motives, recursor.num_minors) for recursor in mutual_group.recursors),
            ((2, 4), (2, 4)),
        )

        nested = PROBE.probe_path(
            CONSTRUCT_FIXTURES / "lean4export-v4.30-construct-matrix-nested.ndjson"
        )
        rose_group = next(
            group
            for group in nested.inductive_groups
            if any(inductive.name == "AxeyumConstructMatrix.Rose" for inductive in group.types)
        )
        self.assertEqual(rose_group.types[0].num_nested, 1)
        self.assertEqual(
            tuple(recursor.name for recursor in rose_group.recursors),
            (
                "AxeyumConstructMatrix.Rose.rec_1",
                "AxeyumConstructMatrix.Rose.rec",
            ),
        )

        well_founded = PROBE.probe_path(
            CONSTRUCT_FIXTURES
            / "lean4export-v4.30-construct-matrix-well-founded.ndjson"
        )
        acc = next(
            inductive
            for group in well_founded.inductive_groups
            for inductive in group.types
            if inductive.name == "Acc"
        )
        self.assertEqual((acc.num_indices, acc.is_rec, acc.is_reflexive), (1, True, True))
        self.assertEqual(
            well_founded.declaration_names[-1],
            "AxeyumConstructMatrix.wellFoundedWitness",
        )

    def test_unknown_record_fails_closed(self) -> None:
        with self.assertRaisesRegex(PROBE.ProbeError, "exactly one record kind"):
            PROBE.probe_lines(lines(META, {"mystery": {}}))

    def test_forward_expression_reference_fails(self) -> None:
        with self.assertRaisesRegex(PROBE.ProbeError, "forward or missing reference"):
            PROBE.probe_lines(lines(META, {"ie": 0, "app": {"fn": 1, "arg": 1}}))

    def test_projection_string_literal_and_quotient_are_blockers(self) -> None:
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
