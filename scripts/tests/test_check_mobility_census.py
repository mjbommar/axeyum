#!/usr/bin/env python3
"""Controls for `scripts/check-mobility-census.py`.

One test per rule, each over a copy of the COMMITTED census corrupted in exactly
one place.  A fixture that violated several rules at once could not tell you
which guard caught it, and -- because this suite is registered in
`scripts/tests/mutation_controls.py` under ``mobility-census`` -- would let a
guard be deleted while more than one test died, which the harness reports as an
ambiguous result rather than coverage.

The two subprocess tests are deliberately blunt: one asserts the committed
census passes, the other that a document violating *many* rules fails.  Neither
can be killed by removing a single guard, which is what keeps them out of the
1:1 mapping above.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-mobility-census.py"
CENSUS = ROOT / "artifacts/autogenesis/mobility-census-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"

_spec = importlib.util.spec_from_file_location("check_mobility_census", SCRIPT)
assert _spec is not None and _spec.loader is not None
checker = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(checker)


def load() -> dict:
    return json.loads(CENSUS.read_text(encoding="utf-8"))


def statuses() -> dict[str, str]:
    return checker.ledger_statuses()


def held_out() -> set[str]:
    return checker.held_out_ids(json.loads(NURSERY.read_text(encoding="utf-8")))


def free_row(document: dict) -> dict:
    """A fact row no cluster and no tactic names, safe to rename in a fixture."""
    named = {
        fact_id
        for cluster in document["zero_match_clusters"]
        for fact_id in cluster["fact_ids"]
    }
    named |= {
        fact_id for row in document["tactics"] for fact_id in row["matched_fact_ids"]
    }
    for row in document["facts"]:
        if row["fact_id"] not in named:
            return row
    raise AssertionError("every fact row is referenced; no free row for the fixtures")


def evaluable_row(document: dict) -> dict:
    for row in document["facts"]:
        if row["evaluable"]:
            return row
    raise AssertionError("the committed census has no evaluable fact row")


def settled_fact_id() -> str:
    for fact_id, status in sorted(statuses().items()):
        if status != "open":
            return fact_id
    raise AssertionError("the ledger holds no settled fact")


class ShapeRules(unittest.TestCase):
    def test_schema_version_must_be_one(self) -> None:
        document = load()
        document["schema_version"] = 2
        self.assertTrue(checker.check_shape(document))

    def test_kind_must_be_the_census_kind(self) -> None:
        document = load()
        document["kind"] = "axeyum-something-else"
        self.assertTrue(checker.check_shape(document))

    def test_a_missing_top_level_key_is_rejected(self) -> None:
        document = load()
        del document["holdout_policy"]
        self.assertTrue(checker.check_shape(document))


class PinRules(unittest.TestCase):
    def test_a_pin_that_does_not_match_its_file_is_rejected(self) -> None:
        document = load()
        document["catalog_sha256"] = "0" * 64
        self.assertTrue(checker.check_pins(document))


class CatalogCoverageRules(unittest.TestCase):
    def test_a_catalog_tactic_the_census_never_evaluated_is_rejected(self) -> None:
        document = load()
        document["tactics"] = document["tactics"][1:]
        problems = checker.check_catalog_coverage(document)
        self.assertTrue([p for p in problems if "never evaluated it" in p])

    def test_a_tactic_the_catalog_does_not_declare_is_rejected(self) -> None:
        document = load()
        invented = copy.deepcopy(document["tactics"][0])
        invented["id"] = "T:invented-by-the-census"
        document["tactics"].append(invented)
        problems = checker.check_catalog_coverage(document)
        self.assertTrue([p for p in problems if "does not declare" in p])


class HeldOutRules(unittest.TestCase):
    def test_a_held_out_id_anywhere_in_the_document_is_rejected(self) -> None:
        ids = held_out()
        document = load()
        free_row(document)["fact_id"] = sorted(ids)[0]
        self.assertTrue(checker.check_no_held_out(document, ids))

    def test_a_nursery_with_no_held_out_rows_fails_closed(self) -> None:
        with self.assertRaises(checker.CensusError):
            checker.held_out_ids({"entries": [{"fact_id": "F:a", "partition": "train"}]})

    def test_the_committed_census_names_no_held_out_fact(self) -> None:
        self.assertEqual(checker.check_no_held_out(load(), held_out()), [])


class FactIdRules(unittest.TestCase):
    def test_a_fact_id_absent_from_the_ledger_is_rejected(self) -> None:
        document = load()
        free_row(document)["fact_id"] = "F:no-such-fact-in-the-ledger"
        problems = checker.check_fact_ids(document, statuses())
        self.assertTrue([p for p in problems if "not in artifacts/facts/" in p])

    def test_a_settled_fact_in_a_census_of_open_facts_is_rejected(self) -> None:
        document = load()
        free_row(document)["fact_id"] = settled_fact_id()
        problems = checker.check_fact_ids(document, statuses())
        self.assertTrue([p for p in problems if "the census is over OPEN facts" in p])

    def test_a_duplicated_fact_row_is_rejected(self) -> None:
        document = load()
        row = free_row(document)
        other = next(r for r in document["facts"] if r["fact_id"] != row["fact_id"])
        row["fact_id"] = other["fact_id"]
        problems = checker.check_fact_ids(document, statuses())
        self.assertTrue([p for p in problems if "appears twice" in p])

    def test_a_cluster_naming_an_unknown_fact_is_rejected(self) -> None:
        document = load()
        document["zero_match_clusters"].append(
            {"reasons": ["r"], "size": 1, "fact_ids": ["F:not-a-row"]}
        )
        problems = checker.check_fact_ids(document, statuses())
        self.assertTrue([p for p in problems if "which has no fact row" in p])

    def test_a_tactic_naming_an_unknown_matched_fact_is_rejected(self) -> None:
        document = load()
        document["tactics"][0]["matched_fact_ids"].append("F:not-a-row")
        problems = checker.check_fact_ids(document, statuses())
        self.assertTrue([p for p in problems if "with no fact row" in p])

    def test_an_empty_ledger_fails_closed(self) -> None:
        original = checker.FACTS
        with tempfile.TemporaryDirectory() as scratch:
            checker.FACTS = Path(scratch)
            try:
                with self.assertRaises(checker.CensusError):
                    checker.ledger_statuses()
            finally:
                checker.FACTS = original


class CountRules(unittest.TestCase):
    def test_evaluable_plus_unevaluable_must_equal_open_facts(self) -> None:
        document = load()
        document["totals"]["evaluable"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "!= open_facts" in p])

    def test_pairs_must_be_facts_times_tactics(self) -> None:
        document = load()
        document["totals"]["pairs"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if p.startswith("pairs ")])

    def test_the_three_verdict_counts_must_sum_to_pairs(self) -> None:
        document = load()
        document["totals"]["matched_pairs"] += 1
        document["totals"]["unmatched_pairs"] -= 1
        document["totals"]["matched_pairs"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "matched + unmatched + unevaluable pairs" in p])

    def test_written_fact_rows_must_match_the_list(self) -> None:
        document = load()
        document["totals"]["written_fact_rows"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "!= " in p and "fact rows" in p])

    def test_written_plus_held_out_must_account_for_every_open_fact(self) -> None:
        document = load()
        document["totals"]["held_out_excluded"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "neither written" in p])

    def test_mobility_must_equal_the_matched_count(self) -> None:
        document = load()
        evaluable_row(document)["mobility"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "mobility" in p])

    def test_an_unevaluable_row_may_not_report_matches(self) -> None:
        document = load()
        for row in document["facts"]:
            if not row["evaluable"]:
                tactic_id = sorted(row["unevaluable"])[0]
                row["matched"] = [tactic_id]
                del row["unevaluable"][tactic_id]
                row["mobility"] = 1
                break
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "still reports matched tactics" in p])

    def test_a_tactic_may_not_carry_two_verdicts_at_once(self) -> None:
        document = load()
        row = evaluable_row(document)
        tactic_id = sorted(row["unmatched"])[0]
        row["unevaluable"][tactic_id] = "duplicated"
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "two verdicts at once" in p])

    def test_every_fact_carries_one_verdict_per_tactic(self) -> None:
        document = load()
        row = evaluable_row(document)
        del row["unmatched"][sorted(row["unmatched"])[0]]
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "verdicts against" in p])

    def test_tactic_matched_counts_must_agree_with_the_fact_rows(self) -> None:
        document = load()
        for row in document["tactics"]:
            if row["matched_fact_ids"]:
                row["matched_fact_ids"] = row["matched_fact_ids"][:-1]
                break
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "fact rows match it" in p])

    def test_a_shape_count_above_the_matched_count_is_rejected(self) -> None:
        document = load()
        for row in document["tactics"]:
            if row["matched_facts"]:
                row["distinct_goal_shapes_matched"] = row["matched_facts"] + 5
                break
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "cannot be a count of shapes matched" in p])

    def test_a_matching_tactic_must_report_at_least_one_shape(self) -> None:
        document = load()
        for row in document["tactics"]:
            if row["matched_facts"]:
                row["distinct_goal_shapes_matched"] = 0
                break
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "reports zero shapes" in p])

    def test_a_fact_may_appear_in_only_one_cluster(self) -> None:
        document = load()
        clusters = document["zero_match_clusters"]
        clusters.append(copy.deepcopy(clusters[0]))
        document["totals"]["clusters"] = len(clusters)
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "two zero-match clusters" in p])

    def test_the_clusters_must_cover_the_zero_match_set(self) -> None:
        document = load()
        document["zero_match_clusters"] = document["zero_match_clusters"][1:]
        document["totals"]["clusters"] = len(document["zero_match_clusters"])
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "are clustered against" in p])

    def test_totals_clusters_must_agree_with_the_cluster_list(self) -> None:
        document = load()
        document["totals"]["clusters"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "totals.clusters disagrees" in p])

    def test_a_cluster_size_must_match_its_fact_list(self) -> None:
        document = load()
        document["zero_match_clusters"][0]["size"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "size disagrees" in p])

    def test_a_cluster_must_name_the_reasons_that_made_it(self) -> None:
        document = load()
        document["zero_match_clusters"][0]["reasons"] = []
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "would name no capability" in p])

    def test_the_partition_table_must_sum_to_the_totals(self) -> None:
        document = load()
        first = sorted(document["partitions"])[0]
        document["partitions"][first]["open"] += 1
        problems = checker.check_counts(document)
        self.assertTrue([p for p in problems if "partitions sum" in p])


class EvaluableRule(unittest.TestCase):
    def test_a_census_that_evaluated_nothing_is_void(self) -> None:
        document = load()
        document["totals"]["evaluable"] = 0
        self.assertTrue(checker.check_evaluable(document))

    def test_the_committed_census_evaluated_something(self) -> None:
        self.assertEqual(checker.check_evaluable(load()), [])


class MustDeclineRules(unittest.TestCase):
    def test_a_missing_sampling_block_is_rejected(self) -> None:
        document = load()
        del document["must_decline_sampling"]
        self.assertTrue(checker.check_must_decline(document))

    def test_a_sampling_block_missing_a_counter_is_rejected(self) -> None:
        document = load()
        del document["must_decline_sampling"]["evaluated"]
        problems = checker.check_must_decline(document)
        self.assertTrue([p for p in problems if "is missing 'evaluated'" in p])

    def test_an_empty_must_decline_population_is_rejected(self) -> None:
        document = load()
        document["must_decline_sampling"]["rows"] = 0
        document["must_decline_sampling"]["evaluated"] = 0
        document["must_decline_sampling"]["unevaluable"] = 0
        problems = checker.check_must_decline(document)
        self.assertTrue([p for p in problems if "no subject" in p])

    def test_sampling_counters_must_sum_to_rows(self) -> None:
        document = load()
        document["must_decline_sampling"]["evaluated"] += 1
        problems = checker.check_must_decline(document)
        self.assertTrue([p for p in problems if "do not sum to rows" in p])

    def test_a_suspect_without_a_fact_behind_it_is_rejected(self) -> None:
        document = load()
        document["must_decline_sampling"]["suspects"] = ["T:refl-closure"]
        document["must_decline_sampling"]["suspect_facts"] = []
        problems = checker.check_must_decline(document)
        self.assertTrue([p for p in problems if "cannot be investigated" in p])

    def test_a_suspect_voids_the_census(self) -> None:
        document = load()
        document["must_decline_sampling"]["suspects"] = ["T:refl-closure"]
        document["must_decline_sampling"]["suspect_facts"] = ["F:ml430-mutation-x"]
        problems = checker.check_must_decline(document)
        self.assertTrue([p for p in problems if "recomputed" in p])


class ExitStatus(unittest.TestCase):
    """The exit status must depend on the finding, not on completion."""

    def run_on(self, path: Path) -> int:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--census", str(path)],
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            check=False,
        ).returncode

    def test_the_committed_census_passes(self) -> None:
        self.assertEqual(self.run_on(CENSUS), 0)

    def test_a_document_violating_many_rules_fails(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / "census.json"
            path.write_text("{}", encoding="utf-8")
            self.assertEqual(self.run_on(path), 1)

    def test_an_unreadable_census_is_a_distinct_status(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / "census.json"
            path.write_text("not json at all", encoding="utf-8")
            self.assertEqual(self.run_on(path), 2)


if __name__ == "__main__":
    unittest.main()
