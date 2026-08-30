#!/usr/bin/env python3
"""In-process assertions for `scripts/lib/graph_join.py` and
`scripts/check-graph-join.py` (L1 phase G2). The guard-deletion kill table
lives in `test-graph-join-mutations.sh`; this file checks the good/bad
fixtures behave as documented and exercises the join logic directly against
the REAL committed declaration graph and fact ledger (not just fixtures),
so a regression in the actual join is caught here too.

Usage: python3 scripts/tests/test-graph-join.py
"""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "tests"))
import graph_join as gj  # noqa: E402
import graph_join_mutations as fx  # noqa: E402


def _load_checker_module():
    spec = importlib.util.spec_from_file_location(
        "_check_graph_join", REPO_ROOT / "scripts" / "check-graph-join.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CGJ = _load_checker_module()


class GuardFixtureTests(unittest.TestCase):
    """Each guard's own bad fixture must fail; the good fixture must pass
    every guard. Mirrors declaration-graph's `FixtureBehaviorTests`."""

    def test_good_fixtures_pass_every_guard(self):
        self.assertEqual(CGJ.check_empty_population(fx.good_rows()), [])
        self.assertEqual(CGJ.check_empty_facts(fx.good_facts_by_id()), [])
        self.assertEqual(CGJ.check_accounting(fx.good_join()), [])
        self.assertEqual(CGJ.check_stale_artifact(fx.good_join(), fx.good_join()), [])
        self.assertEqual(
            CGJ.check_positive_control(fx.good_join(), fx.good_facts_by_id()), []
        )
        depends_derived = gj._load_depends_derived_module()
        self.assertEqual(
            CGJ.check_bare_name_basis(fx.good_join(), fx.good_facts_by_id(), depends_derived), []
        )

    def test_bad_empty_population(self):
        failures = CGJ.check_empty_population(fx.bad_empty_population_rows())
        self.assertEqual(len(failures), 1)
        self.assertIn("EMPTY_POPULATION", failures[0])

    def test_bad_empty_facts(self):
        failures = CGJ.check_empty_facts(fx.bad_empty_facts())
        self.assertEqual(len(failures), 1)
        self.assertIn("EMPTY_FACTS", failures[0])

    def test_bad_accounting(self):
        failures = CGJ.check_accounting(fx.bad_accounting_join())
        self.assertTrue(any("ACCOUNTING" in f for f in failures))

    def test_bad_stale_artifact(self):
        committed, fresh = fx.bad_stale_artifact_pair()
        failures = CGJ.check_stale_artifact(committed, fresh)
        self.assertEqual(len(failures), 1)
        self.assertIn("STALE_ARTIFACT", failures[0])

    def test_bad_positive_control(self):
        failures = CGJ.check_positive_control(fx.bad_positive_control_join(), fx.good_facts_by_id())
        self.assertTrue(any("POSITIVE_CONTROL" in f for f in failures))

    def test_bad_bare_name_basis(self):
        join, facts = fx.bad_bare_name_basis_join_and_facts()
        depends_derived = gj._load_depends_derived_module()
        failures = CGJ.check_bare_name_basis(join, facts, depends_derived)
        self.assertTrue(any("BARE_NAME_BASIS" in f for f in failures))
        self.assertTrue(any("Semigroup.mul_assoc" in f for f in failures))


class NoNameSimilarityTests(unittest.TestCase):
    """The specific requirement G2's exit criterion names: a bare name
    match must never, by itself, resolve `fact_ids` or `kernel_declarations`."""

    def test_title_match_is_exact_not_substring(self):
        facts = {
            "F:decoy": {
                "id": "F:decoy",
                "title": "Mathlib v4.30 source proposition Nat.add_comm_prime",
            }
        }
        result = gj.resolve_fact_ids(["Nat.add_comm"], facts)
        self.assertNotIn("Nat.add_comm", result.resolved)
        self.assertIn("Nat.add_comm", result.unresolved)

    def test_name_coincidence_is_recorded_but_not_resolved(self):
        depends_derived = gj._load_depends_derived_module()
        facts = {
            "F:elsewhere": {
                "id": "F:elsewhere",
                "title": "Some unrelated fact",
                "epistemic_status": "proved",
                "proof_route": "kernel-lean",
                "formal": {"kernel_theorem": "Semigroup.mul_assoc"},
            }
        }
        candidates = gj.name_coincidence_candidates(
            ["Semigroup.mul_assoc"], set(), facts, depends_derived
        )
        self.assertIn("Semigroup.mul_assoc", candidates)
        # And confirm resolve_fact_ids independently did NOT resolve it.
        fact_ids = gj.resolve_fact_ids(["Semigroup.mul_assoc"], facts)
        self.assertNotIn("Semigroup.mul_assoc", fact_ids.resolved)

    def test_fin_root_not_matched_to_nat_fin(self):
        result = gj.resolve_vocabulary(["Fin"])
        self.assertIn("Fin", result.unresolved)
        self.assertIn("Nat.Fin", result.unresolved["Fin"].get("note", ""))


class RealDataRegressionTests(unittest.TestCase):
    """Exercise the join against the REAL committed declaration graph and
    fact ledger -- fixtures alone cannot catch a regression in the actual
    446-declaration population."""

    @classmethod
    def setUpClass(cls):
        cls.join = gj.compute_join(gj.DEFAULT_POPULATION_ID)

    def test_population_matches_declaration_graph(self):
        self.assertEqual(self.join["declaration_population_count"], 446)

    def test_control_theorem_resolves_through_every_stage(self):
        fact_ids = self.join["dimensions"]["fact_ids"]["resolved"]
        self.assertIn("Nat.add_comm", fact_ids)
        kd = self.join["dimensions"]["kernel_declarations"]["resolved"]
        self.assertIn("Nat.add_comm", kd)
        self.assertEqual(kd["Nat.add_comm"]["kernel_theorem"], "Nat.add_comm")
        tf = self.join["dimensions"]["trust_footprints"]["resolved"]
        self.assertEqual(tf["Nat.add_comm"]["axiom_footprint"], [])

    def test_accounting_holds_on_every_dimension(self):
        for dim_name, dim in self.join["dimensions"].items():
            total = dim["resolved_count"] + dim["unresolved_count"]
            self.assertEqual(
                total, dim["population_count"], f"accounting broken for {dim_name}"
            )

    def test_unresolved_is_the_overwhelming_majority_and_that_is_expected(self):
        fact_ids = self.join["dimensions"]["fact_ids"]
        self.assertGreater(fact_ids["unresolved_count"], fact_ids["resolved_count"])
        self.assertGreaterEqual(fact_ids["resolved_count"], 1)

    def test_destination_node_resolves_for_this_population(self):
        dest = self.join["dimensions"]["destination_nodes"]["resolved"]
        self.assertIn(gj.DEFAULT_POPULATION_ID, dest)
        self.assertEqual(dest[gj.DEFAULT_POPULATION_ID]["destination_id"], "curriculum_groups")


if __name__ == "__main__":
    unittest.main()
