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


class HoldoutIsolationTests(unittest.TestCase):
    def setUp(self) -> None:
        self._saved = (guard.NURSERY, guard.FACTS, guard.ARTIFACTS)
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
        guard.NURSERY, guard.FACTS, guard.ARTIFACTS = (
            self.nursery,
            self.facts,
            self.artifacts,
        )

    def tearDown(self) -> None:
        guard.NURSERY, guard.FACTS, guard.ARTIFACTS = self._saved
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
        self.assertIn("held_out=1", out)

    def test_the_committed_repository_passes(self) -> None:
        guard.NURSERY, guard.FACTS, guard.ARTIFACTS = self._saved
        code, out, err = self.run_guard()
        self.assertEqual(code, 0, err)
        self.assertIn("verdict=PASS", out)
        # The repaired partition, pinned: a silent re-expansion of held-out
        # would mean the amendment was reverted. 57 -> 37 on 2026-08-25 when
        # `natural-binomial` moved to development (see docs/autogenesis/
        # 263-holdout-contamination-by-ordinary-development.md and the second
        # amendment in mathlib-nursery-split-policy-v1.json).
        self.assertIn("held_out=37", out)

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
