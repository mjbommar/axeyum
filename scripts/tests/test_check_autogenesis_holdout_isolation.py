#!/usr/bin/env python3
"""Mutation controls for the held-out isolation gate.

Mutation-verified 2026-08-22 and re-verified 2026-08-24, seven guards deleted
one at a time. The property
that holds is not "exactly one test dies" -- two guards are pinned by two tests
each -- but the stronger one that actually matters: **every guard has a nonempty
killed-set, and no two guards share a killed-set member.** Each guard is
therefore uniquely identified by which tests die, so none can be deleted while
the suite stays green, and none is hiding behind another's check.

    settled-check          -> {a_settled_held_out_fact_is_a_violation}
    reference-check        -> {a_reference_at_an_unexpected_json_path_is_still_caught}
    embedded-text-check    -> {an_episode_sidecar_naming_a_held_out_fact_is_a_violation}
    vacuity-check          -> {an_empty_held_out_population_is_an_error_not_a_pass}
    missing-manifest       -> {a_missing_manifest_is_an_error_not_a_pass}
    unreadable-manifest    -> {an_unreadable_manifest_is_an_error_not_a_pass}
    population-exemption   -> {the_population_files_are_exempt,
                               the_committed_repository_passes}

Re-measured 2026-08-24 when slice A4 extended the walk to `artifacts/episodes/`.
Two things changed and both are worth stating. The reference guard's killed-set
SHRANK, because the new embedded-text guard independently catches a held-out id
sitting in a JSON value of its own; what still uniquely pins the exact guard is
that it reports the JSON PATH, which the text scan cannot. And the new guard is
not a duplicate: an episode transcript is prose, so a model writing
"I will work on F:..." puts the id inside a value that is not equal to it, and
the exact walk returns clean. The first version of the episode scan did exactly
that and passed.

The two-test sets are facets of one guard, not two guards behind one check: the
reference guard is exercised at an ordinary and an invented JSON path, and the
exemption guard is exercised in the fixture layout and in the real one.

Six more guards landed 2026-09-01 with ADR-1480's evaluation-record amendment,
mutation-verified the same way. **Every one has a test that ONLY it kills**, so
none can be deleted while the suite is green and none hides behind another:

    recorded-row-must-be-named      -> {a_settled_held_out_fact_is_a_violation,
                                        a_settled_held_out_fact_NOT_named_by_
                                          the_record_is_still_a_violation}
    record-state-must-be-scored     -> {a_record_that_is_not_scored_licenses_nothing}
    record-must-carry-protocol-commit
                                    -> {a_record_without_a_protocol_commit_
                                          licenses_nothing}
    record-may-not-score-an-unsettled-row
                                    -> {a_record_may_not_claim_a_row_it_did_
                                          not_settle}
    record-may-not-name-a-non-held-out-row
                                    -> {a_record_may_not_name_a_row_outside_
                                          the_held_out_population}
    unreadable-record-is-an-error   -> {an_unreadable_record_is_an_error_not_
                                          a_silent_skip}

`a_defective_record_does_not_license_the_spend` is killed by three of them and
that is deliberate rather than a gap: it checks the CONSEQUENCE the three defect
shapes share -- a record the reader rejects must not still let the fact
through -- while each shape is pinned separately above. The three narrow tests
assert only their own complaint precisely so the WIDE mutation does not kill
them; folding both halves into one test each made all three die under the wide
mutation and left nothing uniquely pinning them, which is what the first
measurement showed before they were split.

The guard that matters most in this group is the SECOND one in the list of
tests, not the first. "A record lets a score through" is the amendment working;
"every other route is still refused" is the amendment not having quietly become
"any held-out fact may be proved", which would pass every real run forever.

The discriminating cases matter more than the failing ones. A gate that flags
every fact id would "catch" the breach and be useless, so `test_a_train_fact_
reference_is_not_a_violation` is what makes the partition check meaningful, and
`test_the_population_files_are_exempt` is what stops the manifest that defines
the population from flagging itself.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-holdout-isolation.py"
SPEC = importlib.util.spec_from_file_location("holdout_isolation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
guard = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(guard)

HELD = "F:ml430-held-example-0000dead"
TRAIN = "F:ml430-train-example-0000beef"
HELD_V2 = "F:ml430-extension-held-out-example-0000cafe"
TRAIN_V2 = "F:ml430-extension-train-example-0000f00d"


def committed_held_out_ids(nursery_path: pathlib.Path,
                           extension_path: pathlib.Path) -> set[str]:
    """Held-out fact ids read directly from the two nursery manifests, by
    plain JSON parsing -- deliberately NOT via `guard.held_out_facts()`.
    Comparing the gate's reported count against ITS OWN function would test
    only that the function agrees with itself; this is an independent
    recount so `test_the_committed_repository_passes` can catch a real
    miscount (e.g. a partition-name typo, a dedup bug) rather than a stale
    literal drifting out from under a live population (`held_out=206` pinned
    while the live count moved to 226 by draw 19 -- CLAUDE.md's "every X
    derives from the authority, not a literal" rule, applied here)."""
    ids: set[str] = set()
    for path in (nursery_path, extension_path):
        doc = json.loads(path.read_text(encoding="utf-8"))
        for entry in doc.get("entries", []):
            if isinstance(entry, dict) and entry.get("partition") == "held-out":
                fact_id = entry.get("fact_id")
                if isinstance(fact_id, str):
                    ids.add(fact_id)
    return ids


class HoldoutIsolationTests(unittest.TestCase):
    def setUp(self) -> None:
        self._saved = (guard.NURSERY, guard.EXTENSION, guard.FACTS,
                       guard.ARTIFACTS)
        self._tmp = tempfile.TemporaryDirectory()
        root = pathlib.Path(self._tmp.name)
        self.artifacts = root / "autogenesis"
        self.facts = root / "facts"
        self.artifacts.mkdir()
        self.facts.mkdir()
        self.nursery = root / "nursery-v1.json"
        self.nursery.write_text(
            json.dumps(
                {
                    "entries": [
                        {"fact_id": HELD, "partition": "held-out"},
                        {"fact_id": TRAIN, "partition": "train"},
                    ]
                }
            )
        )
        # The 2026-08-29 refill preregisters 30 held-out rows in a SECOND
        # manifest. A gate reading only v1 reports PASS while leaving every one
        # of them unprotected, so the fixture carries both.
        self.extension = root / "nursery-v2-extension.json"
        self.extension.write_text(
            json.dumps(
                {
                    "entries": [
                        {"fact_id": HELD_V2, "partition": "held-out"},
                        {"fact_id": TRAIN_V2, "partition": "train"},
                    ]
                }
            )
        )
        guard.NURSERY, guard.EXTENSION, guard.FACTS, guard.ARTIFACTS = (
            self.nursery,
            self.extension,
            self.facts,
            self.artifacts,
        )

    def tearDown(self) -> None:
        (guard.NURSERY, guard.EXTENSION, guard.FACTS,
         guard.ARTIFACTS) = self._saved
        self._tmp.cleanup()

    def run_guard(self) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = guard.main()
        return code, out.getvalue(), err.getvalue()

    def write_fact(self, fact_id: str, status: str) -> None:
        path = self.facts / (fact_id.replace("F:", "F-") + ".json")
        path.write_text(json.dumps({"id": fact_id, "epistemic_status": status}))

    # --- the clean state -------------------------------------------------
    def test_a_clean_population_passes(self) -> None:
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)
        self.assertIn("held_out=2", out)

    # --- the count is live, not frozen at whatever the fixture started with
    def test_the_held_out_count_moves_when_a_manifest_gains_a_row(self) -> None:
        """Companion to `test_the_committed_repository_passes` below, which
        re-derives its expected count from the committed manifests instead of
        a literal (a stale literal -- `held_out=206` against a live 226 after
        draw 19 -- is exactly the defect this test exists to rule out). A
        re-derivation that always agrees with a frozen fixture would be as
        blind as the literal it replaced, so this drives the SAME manifest
        shape to a different count and checks the gate's output moves with
        it, entirely independent of the committed repository."""
        code, out, _ = self.run_guard()
        self.assertIn("held_out=2", out)  # HELD (v1) + HELD_V2 (extension)

        extra = "F:ml430-extra-held-out-example-0000feed"
        doc = json.loads(self.extension.read_text())
        doc["entries"].append({"fact_id": extra, "partition": "held-out"})
        self.extension.write_text(json.dumps(doc))

        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)
        self.assertIn("held_out=3", out)

    def test_the_committed_repository_passes(self) -> None:
        (guard.NURSERY, guard.EXTENSION, guard.FACTS,
         guard.ARTIFACTS) = self._saved
        code, out, err = self.run_guard()
        self.assertEqual(code, 0, err)
        self.assertIn("verdict=PASS", out)
        # HISTORY (superseded 2026-09-02, dev-partition-all-manifests). This
        # assertion pinned a LITERAL held-out count and required this comment
        # to be extended by hand on every legitimate move -- 57 through 20+
        # recorded steps up to 206 (draw 18, `0c13e80f8`), each with its own
        # paragraph proving whether the move was an ordinary draw (a whole
        # new family, no v1 row touched) or licensed by an
        # `mathlib-nursery-split-policy-v1.json` amendment (ADR-0542). That
        # discipline caught a real incident -- the pin sat RED on `main` for a
        # full day after draw 18 because nobody had run this test -- but it
        # also means an ordinary draw needs a manual edit here, and by draw 19
        # (206 -> 226, `882ae1a52`) nobody had made it: this test was red on
        # `main` again when this fix landed. Full move-by-move provenance
        # through 206 is preserved in git blame on this line.
        #
        # The property worth keeping is "the gate's reported count matches
        # what the committed manifests actually hold", not "the count equals
        # a number someone typed into this file weeks ago" -- CLAUDE.md's
        # "every X test must derive its X from the authority, not a literal"
        # rule, applied here. So the expected count is now RE-DERIVED at test
        # time, by an INDEPENDENT walk of the two committed manifests
        # (`committed_held_out_ids`, module-level above -- never through
        # `guard.held_out_facts()`, which is the function under test; an
        # equality against that would check only that it agrees with itself).
        # `test_the_held_out_count_moves_when_a_manifest_gains_a_row` proves
        # this re-derivation is live rather than frozen at today's number.
        #
        # The policy checks the old comment's paragraphs were manually
        # re-deriving (whole-family draw vs. licensed amendment, unspent
        # rows, no v1 drift) are NOT abandoned -- they are `check-partition-
        # edges.py`, `check-holdout-adjacency.py`,
        # `check-holdout-closed-evaluation.py`, and the amendment ledger
        # itself (`mathlib-nursery-split-policy-v1.json`), each already gated
        # separately and each re-run in this lane's report. This assertion's
        # job was only ever "the gate counted right", and that is what it
        # checks now, on every run, without going stale.
        expected = committed_held_out_ids(guard.NURSERY, guard.EXTENSION)
        self.assertGreater(
            len(expected), 0,
            "the held-out population must not be empty -- an empty "
            "population would make every guard in this suite pass "
            "vacuously, which is the failure mode the fail-closed checks in "
            "held_out_facts() exist to rule out",
        )
        self.assertIn(
            f"held_out={len(expected)}",
            out,
            "The gate's reported held-out count does not match an "
            "INDEPENDENT recount taken directly from the two committed "
            "nursery manifests (committed_held_out_ids, not "
            "guard.held_out_facts()) -- the gate's own counting logic has "
            "drifted from the data it is supposed to be counting.",
        )

    # --- guard 1: a held-out fact must not be settled ---------------------
    def test_a_settled_held_out_fact_is_a_violation(self) -> None:
        self.write_fact(HELD, "proved")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("settled-held-out-fact", err)

    def test_an_open_held_out_fact_is_not_a_violation(self) -> None:
        self.write_fact(HELD, "open")
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)

    # --- guard 1b: a RECORDED score is permitted, and only a recorded one ---
    #
    # ADR-1480 amended guard 1 so the one deliberate spend the population exists
    # for can be booked. These controls exist because that amendment widens a
    # gate, and a widened gate is exactly the shape that quietly stops failing:
    # the case that matters is not "a record lets a score through" but "every
    # OTHER route is still refused", which the four negative cases below pin
    # separately.

    def write_record(self, **overrides: object) -> None:
        record = {
            "kind": "axeyum-holdout-evaluation-record",
            "state": "scored",
            "protocol_commit": "0123456789abcdef",
            "outcomes": [{"fact_id": HELD, "outcome": "CLOSED"}],
        }
        record.update(overrides)
        (self.artifacts / "holdout-evaluation-v1.json").write_text(
            json.dumps(record))

    def test_a_settled_held_out_fact_named_by_a_record_is_permitted(self) -> None:
        """The whole point of the amendment: a booked spend is not a breach."""
        self.write_fact(HELD, "proved")
        self.write_record()
        code, out, err = self.run_guard()
        self.assertEqual(code, 0, err)
        self.assertIn("verdict=PASS", out)
        self.assertIn("recorded_scores=1", out)
        # and it is counted as a RECORDED score, not swept into `settled`
        self.assertIn("settled=0", out)

    def test_a_settled_held_out_fact_NOT_named_by_the_record_is_still_a_violation(self) -> None:
        """The half that matters. A record for one row must not license another.

        Without this the amendment would degrade to "any held-out fact may be
        proved once any record exists", which passes every real run forever.
        """
        self.write_fact(HELD, "proved")
        self.write_fact(HELD_V2, "proved")
        self.write_record()  # names HELD only
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn(HELD_V2, err)
        self.assertIn("no evaluation record scores it", err)

    def test_a_record_that_is_not_scored_licenses_nothing(self) -> None:
        """A draft record must not pre-authorise a spend.

        Asserts ONLY its own complaint. The "and the spend is still refused"
        half lives in `test_a_defective_record_does_not_license_the_spend`,
        deliberately: folding both into one test would make this case die under
        the WIDE mutation too, and then nothing would uniquely pin the
        state guard.
        """
        self.write_fact(HELD, "proved")
        self.write_record(state="draft")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("evaluation-record-not-scored", err)

    def test_a_record_without_a_protocol_commit_licenses_nothing(self) -> None:
        """The protocol commit is what makes the evaluation blind.

        A record that cannot point at a commit fixing the protocol BEFORE the
        outcomes is a story told afterwards, and a story is not a measurement.
        """
        self.write_fact(HELD, "proved")
        self.write_record(protocol_commit="")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("evaluation-record-without-protocol-commit", err)

    def test_a_defective_record_does_not_license_the_spend(self) -> None:
        """A record the reader rejects must not still let the fact through.

        The three defect shapes are checked in one place because they share
        this consequence, and each is pinned separately above.
        """
        for overrides in ({"state": "draft"},
                          {"protocol_commit": ""},
                          {"outcomes": []}):
            with self.subTest(**overrides):
                self.write_fact(HELD, "proved")
                self.write_record(**overrides)
                code, out, err = self.run_guard()
                self.assertEqual(code, 1)
                self.assertIn("settled-held-out-fact", err)

    def test_a_record_may_not_claim_a_row_it_did_not_settle(self) -> None:
        """Otherwise a record could reserve rows instead of accounting for them.

        A record naming a row that is still `open` is claiming a score that did
        not happen, which is the direction this whole ledger exists to prevent.
        """
        self.write_fact(HELD, "open")
        self.write_record()
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("evaluation-record-scores-unsettled-row", err)

    def test_a_record_may_not_name_a_row_outside_the_held_out_population(self) -> None:
        self.write_fact(HELD, "proved")
        self.write_record(outcomes=[{"fact_id": HELD, "outcome": "CLOSED"},
                                    {"fact_id": TRAIN, "outcome": "CLOSED"}])
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("evaluation-record-names-non-held-out-row", err)

    def test_an_unreadable_record_is_an_error_not_a_silent_skip(self) -> None:
        """A record that cannot be parsed must not quietly license its rows."""
        self.write_fact(HELD, "proved")
        (self.artifacts / "holdout-evaluation-v1.json").write_text("{ not json")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("unreadable-evaluation-record", err)

    def test_the_record_itself_may_name_its_own_rows(self) -> None:
        """It necessarily does, for the reason the population files do.

        The discriminating half: an artifact that is NOT a record still may
        not, which `test_a_reference_from_any_artifact_is_a_violation` pins.
        """
        self.write_fact(HELD, "proved")
        self.write_record()
        code, out, err = self.run_guard()
        self.assertEqual(code, 0, err)
        self.assertNotIn("held-out-reference", err)

    # --- guard 2: nothing outside the population may name a held-out fact --
    def test_a_reference_from_any_artifact_is_a_violation(self) -> None:
        (self.artifacts / "some-plan-v1.json").write_text(
            json.dumps({"target": {"fact_id": HELD}})
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("held-out-reference", err)

    def test_a_reference_at_an_unexpected_json_path_is_still_caught(self) -> None:
        """The generic walk exists because operations carry fact ids at three
        paths; a field-specific guard was bypassable the day it was written."""
        (self.artifacts / "odd-v1.json").write_text(
            json.dumps({"deeply": [{"nested": {"invented_field": HELD}}]})
        )
        code, _, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("invented_field", err)

    def test_a_reference_in_an_artifact_SUBDIRECTORY_is_a_violation(self) -> None:
        """The scan is `rglob`, not `glob`.

        `artifacts/autogenesis/producer-contracts/` did not exist when the
        non-recursive glob was written, so its 2 JSON files were unscanned --
        and a producer contract is prospective dispatch, where naming a held-out
        fact is exactly the breach this gate exists for. Without this case a
        revert to `glob` is unkillable, because every other reference fixture
        sits at the top level.
        """
        nested = self.artifacts / "producer-contracts"
        nested.mkdir()
        (nested / "some-contract-v1.json").write_text(
            json.dumps({"applicability": {"fact_ids": [HELD]}})
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("held-out-reference", err)

    def test_a_train_fact_reference_is_not_a_violation(self) -> None:
        (self.artifacts / "some-plan-v1.json").write_text(
            json.dumps({"target": {"fact_id": TRAIN}})
        )
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)

    def test_the_population_files_are_exempt(self) -> None:
        """Removing the exemption kills this AND
        `test_the_committed_repository_passes`, which is correct rather than a
        stacked guard: in the real layout `nursery-v1.json` lives inside the
        scanned directory and names all 57 held-out facts, so the manifest that
        defines the population would flag itself. The base fixture keeps the
        manifest outside the scanned directory precisely so that this control
        stays sharp for every other guard."""
        (self.artifacts / "mathlib-nat-int-fact-catalog-v1.json").write_text(
            json.dumps({"facts": [{"fact_id": HELD}]})
        )
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)

    # --- guard 2b: the episode tree (slice A4) ----------------------------
    #
    # Ten agent episodes were committed on 2026-08-24 while this gate scanned
    # only `artifacts/autogenesis/`. That they were clean was measured by hand,
    # which is the arrangement this file exists to replace.

    def episodes(self) -> pathlib.Path:
        """Point the gate at a scratch episode tree, restored afterwards."""
        saved = guard.EPISODES
        directory = pathlib.Path(self._tmp.name) / "episodes" / "2026-08-24"
        directory.mkdir(parents=True)
        guard.EPISODES = pathlib.Path(self._tmp.name) / "episodes"
        self.addCleanup(lambda: setattr(guard, "EPISODES", saved))
        return directory

    def test_an_episode_naming_a_held_out_fact_is_a_violation(self) -> None:
        directory = self.episodes()
        (directory / "episode-a4-example.json").write_text(
            json.dumps({"selection": {"fact_id": HELD}})
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("held-out-reference", err)
        self.assertIn("episode-a4-example.json", err)

    def test_an_episode_sidecar_naming_a_held_out_fact_is_a_violation(self) -> None:
        """`*.json.snapshot` is where a transcript and a proposal live, and it is
        the suffix a walk restricted to `*.json` would skip entirely."""
        directory = self.episodes()
        (directory / "messages.json.snapshot").write_text(
            json.dumps([{"parts": [{"content": f"I will work on {HELD}"}]}])
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("messages.json.snapshot", err)

    def test_an_episode_naming_a_train_fact_is_not_a_violation(self) -> None:
        """The discriminating control: a gate that flagged every fact id would
        'catch' the breach and be useless."""
        directory = self.episodes()
        (directory / "episode-a4-example.json").write_text(
            json.dumps({"selection": {"fact_id": TRAIN}})
        )
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)

    def test_the_frontier_census_snapshot_is_exempt_by_name(self) -> None:
        """It is `fact-frontier.py --json`: a census of the WHOLE open ledger,
        re-derived entry for entry by `--verify`, so it necessarily enumerates
        every held-out id. A filtered copy would fail the very rule that makes
        it evidence. Exempted BY NAME, not by directory -- an episode document
        beside it is still scanned, which the tests above show."""
        directory = self.episodes()
        (directory / "frontier.json.snapshot").write_text(
            json.dumps({"entries": [{"fact_id": HELD}, {"fact_id": TRAIN}]})
        )
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)
        self.assertIn("frontier.json.snapshot", str(guard.POPULATION_FILES | {"x"}) or "")

    # --- guard 3: fail closed --------------------------------------------
    def test_an_empty_held_out_population_is_an_error_not_a_pass(self) -> None:
        self.nursery.write_text(
            json.dumps({"entries": [{"fact_id": TRAIN, "partition": "train"}]})
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("pass vacuously", err)

    def test_an_extension_only_held_out_fact_is_protected(self) -> None:
        """The refill's 30 held-out rows live only in the extension manifest.

        Reading v1 alone reports PASS over a population it never looked at,
        which is the same shape as the 2026-08-21 incident this gate exists to
        prevent -- a blind population nothing was watching.
        """
        (self.artifacts / "some-plan-v1.json").write_text(
            json.dumps({"target": {"fact_id": HELD_V2}})
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn(HELD_V2, err)

    def test_an_extension_train_fact_reference_is_not_a_violation(self) -> None:
        (self.artifacts / "some-plan-v1.json").write_text(
            json.dumps({"target": {"fact_id": TRAIN_V2}})
        )
        code, out, _ = self.run_guard()
        self.assertEqual(code, 0)
        self.assertIn("verdict=PASS", out)

    def test_an_extension_with_no_held_out_rows_is_an_error(self) -> None:
        self.extension.write_text(
            json.dumps({"entries": [{"fact_id": TRAIN_V2, "partition": "train"}]})
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("pass vacuously", err)

    def test_a_missing_extension_is_an_error_not_a_pass(self) -> None:
        self.extension.unlink()
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("missing", err)

    def test_a_missing_manifest_is_an_error_not_a_pass(self) -> None:
        self.nursery.unlink()
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("missing", err)

    def test_an_unreadable_manifest_is_an_error_not_a_pass(self) -> None:
        self.nursery.write_text("{not json")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("unreadable", err)


if __name__ == "__main__":
    unittest.main()
