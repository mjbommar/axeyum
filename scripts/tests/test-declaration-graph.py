#!/usr/bin/env python3
"""In-process assertions for `check-declaration-graph.py` and
`declaration_graph.py` (L1 phase C1/G1). The guard-deletion kill table lives
in `test-declaration-graph-mutations.sh`; this file checks the fixtures
behave as documented and exercises the parser/cycle-classifier directly.

Usage: python3 scripts/tests/test-declaration-graph.py
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "tests"))
import declaration_graph as dg  # noqa: E402
import declaration_graph_mutations as fixtures  # noqa: E402

def _load_checker_module():
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "_check_declaration_graph", REPO_ROOT / "scripts" / "check-declaration-graph.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CDG = _load_checker_module()


class FixtureBehaviorTests(unittest.TestCase):
    """Each of the eight mutation fixtures must fail validation, and the
    good fixture must pass -- the same claim the mutation harness's
    baseline check makes via subprocess, re-asserted here in-process so a
    plain `python3` run (no bash) also exercises it."""

    @classmethod
    def setUpClass(cls):
        cls.pack, cls.typeproj, cls.edges, cls.cycles = fixtures.load_good()

    def _write(self, tmp_path: Path, name: str, pack, typeproj, edges, cycles) -> Path:
        fixtures.write_fixture(tmp_path, name, pack, typeproj, edges, cycles)
        pop_dir = tmp_path / "populations"
        pop_dir.mkdir(exist_ok=True)
        import json

        (pop_dir / f"{fixtures.POPULATION_ID}.json").write_text(
            json.dumps({"population_id": fixtures.POPULATION_ID, "expected_roots": ["Root"]})
        )
        return tmp_path / f"{name}.rows.json"

    def test_good_fixture_passes(self):
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            rows_path = self._write(Path(td), "good", self.pack, self.typeproj, self.edges, self.cycles)
            errors = CDG.validate_graph(rows_path, Path(td) / "populations")
            self.assertEqual(errors, [])

    def test_each_mutation_fails(self):
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            builders = {
                "missing": lambda: fixtures.build_missing(self.pack, self.edges),
                "duplicate": lambda: (fixtures.build_duplicate(self.pack), self.edges),
                "reordered": lambda: (fixtures.build_reordered(self.pack), self.edges),
                "truncated": lambda: (fixtures.build_truncated(self.pack), self.edges),
                "row_deleted": lambda: fixtures.build_row_deleted(self.pack, self.edges),
                "edge_deleted": lambda: (self.pack, fixtures.build_edge_deleted(self.edges)),
                "unexpected_cycle": lambda: fixtures.build_unexpected_cycle(self.pack, self.edges),
            }
            for name, build in builders.items():
                with self.subTest(mutation=name):
                    pack, edges = build()
                    typeproj = self.typeproj
                    rows_path = self._write(tmp, name, pack, typeproj, edges, self.cycles)
                    errors = CDG.validate_graph(rows_path, tmp / "populations")
                    self.assertTrue(errors, f"mutation {name!r} should have failed validation")

            # value_exposed mutates the typeproj file, not the pack.
            typeproj = fixtures.build_value_exposed(self.typeproj)
            rows_path = self._write(tmp, "value_exposed", self.pack, typeproj, self.edges, self.cycles)
            errors = CDG.validate_graph(rows_path, tmp / "populations")
            self.assertTrue(errors)


class CycleClassificationTests(unittest.TestCase):
    """`classify_cycles` must classify a genuine mutual-recursion cycle, a
    genuine mutual-inductive cycle, and reject an unexplained one -- proven
    against synthetic fixtures independent of any real lean4export data, so
    this suite exercises the classifier even when a bounded real population
    happens to contain no cycle of a given kind."""

    def test_mutual_recursion_classified(self):
        rows = [
            {"name": "A", "kind": "Definition", "direct_type_deps": [], "direct_value_deps": ["B"], "mutual_group": ["A", "B"]},
            {"name": "B", "kind": "Definition", "direct_type_deps": [], "direct_value_deps": ["A"], "mutual_group": ["A", "B"]},
        ]
        result = dg.classify_cycles(rows, mode="full")
        self.assertEqual(result["unexpected_cycles"], [])
        self.assertEqual(len(result["expected_cycles"]), 1)
        self.assertEqual(result["expected_cycles"][0]["classification"], "mutual_recursion")

    def test_mutual_inductive_classified(self):
        rows = [
            {"name": "T1", "kind": "Inductive", "direct_type_deps": ["T1.ctor"], "direct_value_deps": [], "mutual_group": ["T1", "T1.ctor", "T2", "T2.ctor"]},
            {"name": "T1.ctor", "kind": "Constructor", "direct_type_deps": ["T2"], "direct_value_deps": [], "mutual_group": ["T1", "T1.ctor", "T2", "T2.ctor"]},
            {"name": "T2", "kind": "Inductive", "direct_type_deps": ["T2.ctor"], "direct_value_deps": [], "mutual_group": ["T1", "T1.ctor", "T2", "T2.ctor"]},
            {"name": "T2.ctor", "kind": "Constructor", "direct_type_deps": ["T1"], "direct_value_deps": [], "mutual_group": ["T1", "T1.ctor", "T2", "T2.ctor"]},
        ]
        result = dg.classify_cycles(rows, mode="type")
        self.assertEqual(result["unexpected_cycles"], [])
        self.assertEqual(len(result["expected_cycles"]), 1)
        self.assertEqual(result["expected_cycles"][0]["classification"], "mutual_inductive")
        self.assertEqual(sorted(result["expected_cycles"][0]["nodes"]), ["T1", "T1.ctor", "T2", "T2.ctor"])

    def test_unexplained_cycle_rejected(self):
        rows = [
            {"name": "X", "kind": "Definition", "direct_type_deps": [], "direct_value_deps": ["Y"], "mutual_group": ["X"]},
            {"name": "Y", "kind": "Definition", "direct_type_deps": [], "direct_value_deps": ["X"], "mutual_group": ["Y"]},
        ]
        result = dg.classify_cycles(rows, mode="full")
        self.assertEqual(result["expected_cycles"], [])
        self.assertEqual(len(result["unexpected_cycles"]), 1)
        self.assertEqual(result["unexpected_cycles"][0]["classification"], "UNEXPECTED_CYCLE")

    def test_self_loop_reported_not_treated_as_scc(self):
        rows = [
            {"name": "S", "kind": "Definition", "direct_type_deps": [], "direct_value_deps": ["S"], "mutual_group": ["S"]},
        ]
        result = dg.classify_cycles(rows, mode="full")
        self.assertEqual(result["self_loops"], ["S"])
        self.assertEqual(result["expected_cycles"], [])
        self.assertEqual(result["unexpected_cycles"], [])


class RealGraphCoverageTests(unittest.TestCase):
    """If the committed real graph exists, confirm the population's
    expected_roots are all present and no UNEXPECTED_CYCLE was recorded --
    the same two claims the aggregate gate makes, re-checked here without
    shelling out."""

    def test_committed_graph_if_present(self):
        import json

        rows_path = REPO_ROOT / "artifacts" / "declaration-graph" / "graph" / "mathlib-group-defs-v1.rows.json"
        pop_dir = REPO_ROOT / "artifacts" / "declaration-graph" / "populations"
        if not rows_path.exists():
            self.skipTest("committed graph not present in this checkout")
        errors = CDG.validate_graph(rows_path, pop_dir)
        self.assertEqual(errors, [], f"committed graph failed validation: {errors}")


if __name__ == "__main__":
    unittest.main()
