#!/usr/bin/env python3
"""Functional tests for scripts/check-lean-adapter.py's guard functions, run
directly against small in-process fixtures (not the mutation kill table --
that is test-lean-adapter-mutations.sh).

Also confirms the committed real artifacts under artifacts/lean-adapter/ are
internally the shape the checker expects, as a fast sanity check independent
of running the whole gate script.
"""
from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "tests"))


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


cla = _load("check_lean_adapter", REPO_ROOT / "scripts" / "check-lean-adapter.py")
fx = _load("lean_adapter_mutations", REPO_ROOT / "scripts" / "tests" / "lean_adapter_mutations.py")


class GuardFunctionTests(unittest.TestCase):
    def test_good_fixture_passes_every_guard(self):
        failures = cla.run_all_guards(fx.good_goal_pack(), fx.good_result(), fx.good_live_identity())
        self.assertEqual(failures, [])

    def test_absence_fires_on_a_dropped_required_category(self):
        failures = cla.check_absence(fx.good_goal_pack(), fx.bad_absence_result())
        self.assertTrue(any("ABSENCE" in f for f in failures))

    def test_lean_actually_ran_requires_at_least_one_real_invocation(self):
        failures = cla.check_lean_actually_ran(fx.bad_lean_actually_ran_result())
        self.assertTrue(any("LEAN_ACTUALLY_RAN" in f for f in failures))

    def test_success_accepted_rejects_a_declined_success(self):
        failures = cla.check_success_accepted(fx.bad_success_accepted_result())
        self.assertTrue(any("SUCCESS_ACCEPTED" in f for f in failures))

    def test_mutations_rejected_catches_a_credited_forgery(self):
        failures = cla.check_mutations_rejected(fx.bad_mutations_rejected_result())
        self.assertTrue(any("MUTATIONS_REJECTED" in f for f in failures))

    def test_declines_typed_nonvacuous_catches_a_wrong_reason_string(self):
        failures = cla.check_declines_typed_nonvacuous(fx.bad_declines_typed_nonvacuous_result())
        self.assertTrue(any("DECLINES_TYPED_NONVACUOUS" in f for f in failures))

    def test_expected_matches_observed_catches_an_internal_disagreement(self):
        failures = cla.check_expected_matches_observed(fx.bad_expected_matches_observed_result())
        self.assertTrue(any("EXPECTED_MATCHES_OBSERVED" in f for f in failures))

    def test_environment_toolchain_stale_requires_a_live_authority(self):
        # None live_identity (no census file found) must be a FAILURE, never
        # a silent pass -- an absent authority is not evidence of freshness.
        failures = cla.check_environment_toolchain_stale(fx.good_result(), None)
        self.assertTrue(any("ENVIRONMENT_TOOLCHAIN_STALE" in f for f in failures))

    def test_environment_toolchain_stale_catches_a_drifted_commit(self):
        failures = cla.check_environment_toolchain_stale(
            fx.bad_environment_toolchain_stale_result(), fx.good_live_identity()
        )
        self.assertTrue(any("ENVIRONMENT_TOOLCHAIN_STALE" in f for f in failures))


class CommittedArtifactShapeTests(unittest.TestCase):
    """Sanity checks over the REAL committed artifacts -- not a mutation
    test, just confirming the shape this gate depends on actually exists on
    disk before the full checker script is invoked."""

    def test_goal_pack_and_result_files_exist(self):
        goal_pack_dir = REPO_ROOT / "artifacts" / "lean-adapter" / "goal-pack"
        results_dir = REPO_ROOT / "artifacts" / "lean-adapter" / "results"
        self.assertTrue(list(goal_pack_dir.glob("*.json")), "no goal pack files committed")
        self.assertTrue(list(results_dir.glob("*.result.json")), "no result files committed")

    def test_real_result_passes_the_full_guard_set_against_the_live_toolchain(self):
        result_path = (
            REPO_ROOT / "artifacts" / "lean-adapter" / "results" / "thin-adapter-v1.result.json"
        )
        goal_pack_path = (
            REPO_ROOT / "artifacts" / "lean-adapter" / "goal-pack" / "thin-adapter-v1.json"
        )
        result = json.loads(result_path.read_text(encoding="utf-8"))
        goal_pack = json.loads(goal_pack_path.read_text(encoding="utf-8"))
        live_identity = cla.live_checked_interchange_identity(
            REPO_ROOT / "artifacts" / "checked-interchange" / "census"
        )
        self.assertIsNotNone(
            live_identity, "no checked-interchange census file with a lean_version/lean_commit found"
        )
        failures = cla.run_all_guards(goal_pack, result, live_identity)
        self.assertEqual(failures, [], f"real committed artifacts failed: {failures}")

    def test_the_real_result_covers_every_required_category_exactly_once(self):
        result_path = (
            REPO_ROOT / "artifacts" / "lean-adapter" / "results" / "thin-adapter-v1.result.json"
        )
        goal_pack_path = (
            REPO_ROOT / "artifacts" / "lean-adapter" / "goal-pack" / "thin-adapter-v1.json"
        )
        result = json.loads(result_path.read_text(encoding="utf-8"))
        goal_pack = json.loads(goal_pack_path.read_text(encoding="utf-8"))
        categories = [o["category"] for o in result["outcomes"]]
        self.assertEqual(sorted(categories), sorted(set(categories)), "a category is duplicated")
        self.assertEqual(set(categories), set(goal_pack["required_categories"]))


if __name__ == "__main__":
    unittest.main()
