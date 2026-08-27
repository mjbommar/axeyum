"""Focused tests for `scripts/gen-import-backlog.py` (ADR-0601 SS3).

Each test targets one guard/behaviour; `scripts/tests/mutation_controls.py
import-backlog` deletes guards one at a time and requires each deletion to
kill exactly one test.
"""

from __future__ import annotations

import importlib.util
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-import-backlog.py"
SPEC = importlib.util.spec_from_file_location("gen_import_backlog", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


NODES = {
    "predicate-logic": {"layer": 0, "title": "Predicate Logic"},
    "integers": {"layer": 1, "title": "Integers"},
}


def fact(fid: str, **overrides) -> dict:
    base = {
        "id": fid,
        "statement": f"statement for {fid}",
        "epistemic_status": "open",
        "external_status": "proved",
        "depends_on": [],
        "concept_refs": [],
    }
    base.update(overrides)
    return base


class CurriculumMappingTests(unittest.TestCase):
    def test_exact_match_on_stripped_ref_maps_to_node(self) -> None:
        f = fact(
            "F:x",
            concept_refs=[
                {"graph": "math-education", "ref": "C:predicate-logic", "relation": "about"}
            ],
        )
        self.assertEqual(MODULE.map_curriculum_node(f, NODES), "predicate-logic")

    def test_non_matching_ref_does_not_map(self) -> None:
        f = fact(
            "F:x",
            concept_refs=[
                {"graph": "math-education", "ref": "C:fallacy", "relation": "about"}
            ],
        )
        self.assertIsNone(MODULE.map_curriculum_node(f, NODES))

    def test_wrong_graph_does_not_map_even_with_matching_id(self) -> None:
        # A fuzzy/substring matcher would find "predicate-logic" here too --
        # this is the control that would catch that regression.
        f = fact(
            "F:x",
            concept_refs=[
                {"graph": "some-other-graph", "ref": "C:predicate-logic", "relation": "about"}
            ],
        )
        self.assertIsNone(MODULE.map_curriculum_node(f, NODES))

    def test_first_matching_ref_wins_deterministically(self) -> None:
        f = fact(
            "F:x",
            concept_refs=[
                {"graph": "math-education", "ref": "C:predicate-logic"},
                {"graph": "math-education", "ref": "C:integers"},
            ],
        )
        self.assertEqual(MODULE.map_curriculum_node(f, NODES), "predicate-logic")

    def test_string_concept_ref_entries_do_not_crash(self) -> None:
        # `concept_refs` entries are sometimes bare strings on this ledger
        # (e.g. "constructed-reals"), not {"graph": ..., "ref": ...} dicts.
        f = fact("F:x", concept_refs=["constructed-reals"])
        self.assertIsNone(MODULE.map_curriculum_node(f, NODES))


class DependencyReadyTests(unittest.TestCase):
    def test_empty_depends_on_is_vacuously_ready(self) -> None:
        facts = {"F:x": fact("F:x", depends_on=[])}
        self.assertTrue(MODULE.dependency_ready(facts["F:x"], facts))

    def test_all_deps_settled_is_ready(self) -> None:
        facts = {
            "F:x": fact("F:x", depends_on=["F:dep"]),
            "F:dep": fact("F:dep", epistemic_status="proved"),
        }
        self.assertTrue(MODULE.dependency_ready(facts["F:x"], facts))

    def test_any_dep_open_is_not_ready(self) -> None:
        facts = {
            "F:x": fact("F:x", depends_on=["F:dep"]),
            "F:dep": fact("F:dep", epistemic_status="open"),
        }
        self.assertFalse(MODULE.dependency_ready(facts["F:x"], facts))

    def test_missing_dep_is_not_ready(self) -> None:
        facts = {"F:x": fact("F:x", depends_on=["F:ghost"])}
        self.assertFalse(MODULE.dependency_ready(facts["F:x"], facts))


class BuildRowsOrderingTests(unittest.TestCase):
    """The ordering IS the design content (module docstring / ADR-0601 SS3):
    dependency-ready before blocked, curriculum-reachable before unmapped
    within that, then (layer, node id), then fact id.
    """

    def test_only_backlog_facts_are_included(self) -> None:
        facts = {
            "F:backlog": fact("F:backlog"),
            "F:not-open": fact("F:not-open", epistemic_status="proved"),
            "F:not-external-proved": fact("F:not-external-proved", external_status="open"),
        }
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual([r["id"] for r in rows], ["F:backlog"])

    def test_dependency_ready_sorts_before_blocked(self) -> None:
        facts = {
            "F:blocked": fact("F:blocked", depends_on=["F:missing"]),
            "F:ready": fact("F:ready"),
        }
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual([r["id"] for r in rows], ["F:ready", "F:blocked"])

    def test_curriculum_mapped_sorts_before_unmapped_within_readiness_tier(self) -> None:
        facts = {
            "F:unmapped": fact("F:unmapped"),
            "F:mapped": fact(
                "F:mapped",
                concept_refs=[{"graph": "math-education", "ref": "C:integers"}],
            ),
        }
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual([r["id"] for r in rows], ["F:mapped", "F:unmapped"])

    def test_mapped_rows_order_by_curriculum_layer_then_node_id(self) -> None:
        facts = {
            "F:layer1": fact(
                "F:layer1",
                concept_refs=[{"graph": "math-education", "ref": "C:integers"}],
            ),
            "F:layer0": fact(
                "F:layer0",
                concept_refs=[{"graph": "math-education", "ref": "C:predicate-logic"}],
            ),
        }
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual([r["id"] for r in rows], ["F:layer0", "F:layer1"])

    def test_ties_break_on_fact_id_ascending(self) -> None:
        facts = {"F:b": fact("F:b"), "F:a": fact("F:a")}
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual([r["id"] for r in rows], ["F:a", "F:b"])

    def test_depends_on_is_reported_sorted(self) -> None:
        facts = {
            "F:x": fact("F:x", depends_on=["F:z", "F:a"]),
            "F:z": fact("F:z", epistemic_status="proved"),
            "F:a": fact("F:a", epistemic_status="proved"),
        }
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual(rows[0]["depends_on"], ["F:a", "F:z"])


class RenderDeterminismTests(unittest.TestCase):
    def test_render_is_byte_identical_across_calls(self) -> None:
        facts = {"F:x": fact("F:x"), "F:y": fact("F:y")}
        rows = MODULE.build_rows(facts, NODES)
        self.assertEqual(MODULE.render(rows), MODULE.render(rows))

    def test_render_has_no_generation_timestamp(self) -> None:
        # Determinism is a public API promise (CLAUDE.md): a Date.now-style
        # field would make every regeneration a spurious diff.
        rows = MODULE.build_rows({"F:x": fact("F:x")}, NODES)
        document = json.loads(MODULE.render(rows))
        self.assertNotIn("generated_at", document)
        self.assertNotIn("timestamp", document)

    def test_render_count_matches_row_count(self) -> None:
        facts = {"F:x": fact("F:x"), "F:y": fact("F:y")}
        rows = MODULE.build_rows(facts, NODES)
        document = json.loads(MODULE.render(rows))
        self.assertEqual(document["count"], len(rows))
        self.assertEqual(len(document["rows"]), len(rows))


class LoadCurriculumNodesTests(unittest.TestCase):
    def test_missing_curriculum_file_raises_backlog_error(self) -> None:
        original = MODULE.CURRICULUM
        MODULE.CURRICULUM = ROOT / "does" / "not" / "exist.toml"
        try:
            with self.assertRaises(MODULE.BacklogError):
                MODULE.load_curriculum_nodes()
        finally:
            MODULE.CURRICULUM = original

    def test_real_curriculum_file_parses_and_contains_known_nodes(self) -> None:
        nodes = MODULE.load_curriculum_nodes()
        self.assertIn("propositional-logic", nodes)
        self.assertEqual(nodes["propositional-logic"]["layer"], 0)


if __name__ == "__main__":
    unittest.main()
