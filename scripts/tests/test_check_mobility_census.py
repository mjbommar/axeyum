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

    def test_a_settled_fact_row_is_not_a_fact_id_violation(self) -> None:
        """Graduation is lifecycle. `check_fact_ids` used to reject it, and on
        2026-08-30 that produced 126 identical lines over one census -- the
        gate failing because the flywheel worked. `check_population` audits the
        claim instead; this pins that the id rule no longer double-reports it.
        """
        document = load()
        free_row(document)["fact_id"] = settled_fact_id()
        problems = checker.check_fact_ids(document, statuses())
        self.assertEqual([p for p in problems if "OPEN facts" in p], [])

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


def build_fact_history(scratch: Path) -> tuple[Path, str, str]:
    """A throwaway repo holding one fact, committed `open` then `proved`.

    The graduation audit re-reads a fact's status at the census's pinned commit,
    so its controls need real git history. They must NOT borrow this
    repository's: `scripts/tests/mutation_controls.py` mutates a `copytree` of
    the tree, which carries no `.git`, so every such control would report
    `no-git` and every guard below would survive its own mutant -- coverage
    that was never measured, which is the exact failure this suite exists to
    prevent.
    """
    root = scratch / "repo"
    (root / "artifacts/facts").mkdir(parents=True)
    hooks = scratch / "nohooks"
    hooks.mkdir()

    def git(*args: str) -> str:
        return subprocess.run(
            ["git", "-C", str(root), *args], capture_output=True, text=True, check=True
        ).stdout.strip()

    subprocess.run(["git", "init", "-q", str(root)], capture_output=True, check=True)
    # An empty hooks path: this repository's own `commit-msg` hook refuses a
    # commit with no `Agent:` trailer, and a fixture must not depend on that.
    git("config", "core.hooksPath", str(hooks))
    git("config", "user.email", "controls@example.invalid")
    git("config", "user.name", "mobility-census controls")
    path = root / "artifacts/facts/F-fixture.json"
    shas = []
    for status in ("open", "proved"):
        path.write_text(
            json.dumps({"id": "F:fixture", "epistemic_status": status}), encoding="utf-8"
        )
        git("add", "-A")
        git("commit", "-q", "-m", status)
        shas.append(git("rev-parse", "HEAD"))
    return root, shas[0], shas[1]


def fixture_census(commit: str, fact_ids: list[str]) -> dict:
    """The slice of a census that `check_population` reads."""
    return {"git_commit": commit, "facts": [{"fact_id": f} for f in fact_ids]}


def all_settled(document: dict) -> dict[str, str]:
    """Synthetic ledger: every censused fact closed. The fixtures below open
    exactly the rows each rule needs, so no rule fires by accident."""
    return {row["fact_id"]: "proved" for row in document["facts"]}


class PopulationRules(unittest.TestCase):
    """Graduation is counted; a row that was ALREADY settled when the census ran
    is not. `open_facts` is the denominator of the census's headline ratio, so
    padding it with closed facts inflates the very number the census publishes.
    """

    def in_fixture(self, pin: str, fact_ids: list[str], ledger: dict[str, str]):
        original = checker.ROOT
        with tempfile.TemporaryDirectory() as scratch:
            root, sha_open, sha_proved = build_fact_history(Path(scratch))
            checker.ROOT = root
            commit = {"open": sha_open, "proved": sha_proved}.get(pin, pin)
            try:
                return checker.check_population(fixture_census(commit, fact_ids), ledger)
            finally:
                checker.ROOT = original

    def test_a_graduated_row_is_not_a_violation(self) -> None:
        """`F:fixture` was open at the pinned commit and is proved now: it
        GRADUATED. No violation, and the audit must have actually run --
        otherwise this guard is the old blanket rule under a new name."""
        problems, live, graduated, audit = self.in_fixture(
            "open", ["F:fixture"], {"F:fixture": "proved"}
        )
        self.assertEqual(problems, [])
        self.assertEqual(audit, "ok")
        self.assertEqual((live, graduated), (0, 1))

    def test_a_still_open_row_is_counted_live(self) -> None:
        problems, live, graduated, _audit = self.in_fixture(
            "open", ["F:fixture"], {"F:fixture": "open"}
        )
        self.assertEqual(problems, [])
        self.assertEqual((live, graduated), (1, 0))

    def test_a_row_already_settled_when_the_census_ran_is_rejected(self) -> None:
        """Same row, pinned one commit later -- where it was ALREADY proved.
        Counting it inflates `open_facts`, the census's headline denominator."""
        problems, _live, _graduated, audit = self.in_fixture(
            "proved", ["F:fixture"], {"F:fixture": "proved"}
        )
        self.assertEqual(audit, "ok")
        self.assertTrue([p for p in problems if "was already proved at" in p])

    def test_a_row_with_no_fact_file_at_the_pinned_commit_is_rejected(self) -> None:
        problems, *_ = self.in_fixture(
            "open", ["F:never-existed"], {"F:never-existed": "open"}
        )
        self.assertTrue([p for p in problems if "had no fact file at" in p])

    def test_an_unreachable_pinned_commit_is_rejected_not_skipped(self) -> None:
        problems, _live, _graduated, audit = self.in_fixture(
            "0" * 40, ["F:fixture"], {"F:fixture": "open"}
        )
        self.assertEqual(audit, "unreachable")
        self.assertTrue([p for p in problems if "is not reachable in this checkout" in p])

    def test_a_tree_with_no_git_reports_the_skip_rather_than_a_clean_audit(self) -> None:
        """`git archive` snapshots (`scripts/lane-snapshot.sh`) carry no `.git`,
        and this gate runs in them. The audit is skipped there -- but the state
        must reach the status line, so a run that COULD NOT audit never reads as
        a run that audited and found nothing.
        """
        original = checker.ROOT
        with tempfile.TemporaryDirectory() as scratch:
            checker.ROOT = Path(scratch)
            try:
                state, historical = checker.statuses_at_commit("HEAD", ["F:anything"])
                problems, _live, _graduated, audit = checker.check_population(
                    load(), statuses()
                )
            finally:
                checker.ROOT = original
        self.assertEqual((state, historical), ("no-git", {}))
        self.assertEqual(audit, "no-git")
        self.assertEqual(problems, [])

    def test_a_census_pinning_no_commit_is_rejected(self) -> None:
        document = load()
        document["git_commit"] = ""
        problems, _live, _graduated, audit = checker.check_population(document, statuses())
        self.assertEqual(audit, "absent")
        self.assertTrue([p for p in problems if "pins no git_commit" in p])


class FreshnessRules(unittest.TestCase):
    """Is the census still a description of the OPEN backlog? Every quantity is
    recomputed from the ledger, the nursery and the frozen-export index, so the
    fixtures pass those in directly rather than editing the census.
    """

    def test_a_census_whose_every_export_has_closed_has_no_subject(self) -> None:
        document = load()
        problems, live_evaluable, live_exportable = checker.check_freshness(
            document, all_settled(document), set(), {"F:an-export-whose-fact-closed"}
        )
        self.assertEqual((live_evaluable, live_exportable), (0, 0))
        self.assertTrue([p for p in problems if "has no subject left" in p])

    def test_open_exports_the_census_never_evaluated_demand_a_regeneration(self) -> None:
        document = load()
        row = free_row(document)
        row["evaluable"] = False
        ledger = all_settled(document)
        ledger[row["fact_id"]] = "open"
        problems, live_evaluable, live_exportable = checker.check_freshness(
            document, ledger, set(), {row["fact_id"]}
        )
        self.assertEqual((live_evaluable, live_exportable), (0, 1))
        self.assertTrue([p for p in problems if "evaluated none of them" in p])

    def test_an_open_exportable_fact_with_no_census_row_is_rejected(self) -> None:
        document = load()
        row = free_row(document)
        row["evaluable"] = True
        ledger = all_settled(document)
        ledger[row["fact_id"]] = "open"
        ledger["F:open-exportable-with-no-row"] = "open"
        problems, live_evaluable, _ = checker.check_freshness(
            document, ledger, set(), {row["fact_id"], "F:open-exportable-with-no-row"}
        )
        self.assertEqual(live_evaluable, 1, "a live evaluable row must exist or an earlier rule fires")
        self.assertTrue([p for p in problems if "went unmeasured" in p])

    def test_a_held_out_open_export_is_never_demanded_as_a_row(self) -> None:
        """The rule above must not fire for a held-out fact. `totals` counts
        held-out facts as integers and the document never names one; a checker
        demanding a row for one would be demanding the leak that
        `check_no_held_out` exists to refuse.
        """
        document = load()
        row = free_row(document)
        row["evaluable"] = True
        ledger = all_settled(document)
        ledger[row["fact_id"]] = "open"
        ledger["F:held-out-and-open"] = "open"
        problems, *_ = checker.check_freshness(
            document,
            ledger,
            {"F:held-out-and-open"},
            {row["fact_id"], "F:held-out-and-open"},
        )
        self.assertEqual([p for p in problems if "F:held-out-and-open" in p], [])

    def test_a_zero_match_cluster_of_settled_facts_is_rejected(self) -> None:
        document = load()
        row = free_row(document)
        row["evaluable"] = True
        ledger = all_settled(document)
        ledger[row["fact_id"]] = "open"
        problems, *_ = checker.check_freshness(
            document, ledger, set(), {row["fact_id"]}
        )
        self.assertTrue([p for p in problems if "names no capability" in p])

    def test_a_cluster_with_a_still_open_fact_is_accepted(self) -> None:
        """The counterpart: the rule above must not fire on a live backlog, or
        it rejects every census rather than every stale one."""
        document = load()
        row = free_row(document)
        row["evaluable"] = True
        ledger = all_settled(document)
        ledger[row["fact_id"]] = "open"
        for cluster in document["zero_match_clusters"]:
            for fact_id in cluster["fact_ids"]:
                ledger[fact_id] = "open"
        problems, *_ = checker.check_freshness(
            document, ledger, set(), {row["fact_id"]}
        )
        self.assertEqual([p for p in problems if "names no capability" in p], [])

    def _exportable_with(self, index: dict) -> None:
        original = checker.EXPORT_INDEX
        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / "index.json"
            path.write_text(json.dumps(index), encoding="utf-8")
            checker.EXPORT_INDEX = path
            try:
                checker.exportable_fact_ids()
            finally:
                checker.EXPORT_INDEX = original

    def test_an_export_index_with_no_entries_fails_closed(self) -> None:
        # The message is asserted, not just the exception: the two guards in
        # `exportable_fact_ids` both reject this input, so matching only the
        # type would let either be deleted with this test still green.
        with self.assertRaisesRegex(checker.CensusError, "has no entries"):
            self._exportable_with({"entries": []})

    def test_an_export_index_whose_entries_name_no_fact_ids_fails_closed(self) -> None:
        with self.assertRaisesRegex(checker.CensusError, "names no fact ids"):
            self._exportable_with({"entries": [{"producer_tool": "none"}]})


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

    #: The staleness the committed census is KNOWN to carry, as of 2026-08-30.
    #: Every frozen statement export names a fact that has since been proved, so
    #: the census has no subject and regenerating it cannot give it one -- see
    #: `docs/plan/status/323-mobility-census.md`.
    #:
    #: These are violation KINDS, not sentences, and that is deliberate on both
    #: sides. It keeps the test blunt -- deleting any single freshness guard
    #: makes a sibling freshness rule fire instead, which still matches, so no
    #: one mutant kills this test and it stays out of the 1:1 mapping in
    #: `scripts/tests/mutation_controls.py` (matching sentences made the
    #: `no subject` mutant kill two tests). And it keeps the ratchet: a
    #: `graduation-audit:` line, a bad counter or a leaked held-out id is a kind
    #: that is NOT here, and fails this immediately.
    KNOWN_STALENESS = (
        "nursery_sha256 is",
        "freshness:",
    )

    def test_the_committed_census_fails_only_for_known_staleness(self) -> None:
        """A ratchet in both directions.

        It fails if a NEW kind of violation appears, and it fails when the
        census is finally regenerated against live exports and goes green --
        at which point the right edit is to assert 0 again and delete
        `KNOWN_STALENESS`. Asserting `== 0` today would be asserting something
        false; asserting nothing would let the census rot unwatched.
        """
        proc = subprocess.run(
            [sys.executable, str(SCRIPT), "--census", str(CENSUS)],
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(proc.returncode, 1, proc.stderr)
        reported = [
            line.strip() for line in proc.stderr.splitlines() if line.startswith("  ")
        ]
        self.assertTrue(reported, "a failing run must name what it found")
        unexpected = [
            line
            for line in reported
            if not any(known in line for known in self.KNOWN_STALENESS)
        ]
        self.assertEqual(unexpected, [])

    def test_the_run_reports_recomputed_metrics_beside_the_claimed_ones(self) -> None:
        """The claimed totals and the recomputed `live_*` pair must BOTH be on
        the status line. Their gap is the staleness; one number would hide which
        side of it moved."""
        proc = subprocess.run(
            [sys.executable, str(SCRIPT), "--census", str(CENSUS)],
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        line = next(
            row for row in proc.stdout.splitlines() if row.startswith("MOBILITY_CENSUS|")
        )
        for field in ("live=", "graduated=", "live_evaluable=", "live_exportable=", "audit="):
            self.assertIn(field, line)
        self.assertNotIn("audit=not-reached", line)

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
