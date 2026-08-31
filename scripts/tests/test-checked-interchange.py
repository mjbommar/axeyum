#!/usr/bin/env python3
"""Functional tests for scripts/check-checked-interchange.py's guard
functions, run directly against small in-process fixtures (not the mutation
kill table -- that is test-checked-interchange-mutations.sh).

Also confirms the committed real artifacts under artifacts/checked-interchange/
are internally the shape the checker expects, as a fast sanity check
independent of running the whole gate script.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "tests"))

import importlib.util


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


cci = _load("check_checked_interchange", REPO_ROOT / "scripts" / "check-checked-interchange.py")
fx = _load("checked_interchange_mutations", REPO_ROOT / "scripts" / "tests" / "checked_interchange_mutations.py")


class GuardFunctionTests(unittest.TestCase):
    def test_good_fixture_passes_every_guard(self):
        population = fx.good_population()
        census = fx.good_census()
        live = fx.good_live_credited_roots()
        failures = cci.run_all_guards(population, census, live)
        self.assertEqual(failures, [])

    def test_missing_fires_on_dropped_root(self):
        failures = cci.check_missing(fx.good_population(), fx.bad_missing_census())
        self.assertTrue(any("MISSING" in f for f in failures))

    def test_stale_population_requires_a_live_authority(self):
        # None live_credited_roots (no join file found) must be a FAILURE,
        # never a silent pass -- an absent authority is not evidence of
        # freshness.
        failures = cci.check_stale_population(fx.good_population(), None)
        self.assertTrue(any("STALE_POPULATION" in f for f in failures))

    def test_bare_name_accept_rejects_a_name_only_identity(self):
        failures = cci.check_bare_name_accept(fx.bad_bare_name_accept_census())
        self.assertTrue(any("BARE_NAME_ACCEPT" in f for f in failures))

    def test_bare_type_accept_rejects_a_type_mismatch_masquerading_as_accepted(self):
        failures = cci.check_bare_type_accept(fx.bad_bare_type_accept_census())
        self.assertTrue(any("BARE_TYPE_ACCEPT" in f for f in failures))

    def test_decline_probe_vacuous_catches_a_probe_that_never_declines(self):
        failures = cci.check_decline_probe_vacuous(fx.bad_decline_probe_vacuous_census())
        self.assertTrue(any("DECLINE_PROBE_VACUOUS" in f for f in failures))


class CommittedArtifactShapeTests(unittest.TestCase):
    """Sanity checks over the REAL committed artifacts -- not a mutation
    test, just confirming the shape this gate depends on actually exists on
    disk before the full checker script is invoked."""

    def test_population_and_census_files_exist(self):
        population_dir = REPO_ROOT / "artifacts" / "checked-interchange" / "populations"
        census_dir = REPO_ROOT / "artifacts" / "checked-interchange" / "census"
        self.assertTrue(list(population_dir.glob("*.json")), "no population files committed")
        self.assertTrue(list(census_dir.glob("*.census.json")), "no census files committed")

    def test_real_census_passes_the_full_guard_set_against_the_live_join(self):
        import json

        census_path = (
            REPO_ROOT
            / "artifacts"
            / "checked-interchange"
            / "census"
            / "credited-roots-v1.census.json"
        )
        population_path = (
            REPO_ROOT
            / "artifacts"
            / "checked-interchange"
            / "populations"
            / "credited-roots-v1.json"
        )
        census = json.loads(census_path.read_text(encoding="utf-8"))
        population = json.loads(population_path.read_text(encoding="utf-8"))
        live = cci.live_join_credited_roots(REPO_ROOT / "artifacts" / "graph-join")
        self.assertIsNotNone(live, "no graph-join artifact with a trust_footprints dimension found")
        failures = cci.run_all_guards(population, census, live)
        self.assertEqual(failures, [], f"real committed artifacts failed: {failures}")


if __name__ == "__main__":
    unittest.main()
