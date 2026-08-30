#!/usr/bin/env python3
"""Unit tests for scripts/check-effort-taxonomy.py, one test per guard.

Each test calls its guard FUNCTION directly (not run_all_guards), on a
minimal fixture built in-process, so that neutering exactly one guard
function in the checker (mutation testing) kills exactly the one test named
after it and no other -- there is no fixture-sharing between tests to cause
cross-contamination.

Run: python3 scripts/tests/test-effort-taxonomy.py
Mutation-verify: for each guard_* function in check-effort-taxonomy.py,
replace its body with `return Violation()` (or, for guard_generated_fresh,
with `return Violation()` too) one at a time, rerun this file, and confirm
exactly one test fails. See the kill table in
docs/plan/status/l3-d0-effort-taxonomy.md.
"""

from __future__ import annotations

import importlib.util as ilu
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATH = ROOT / "scripts" / "check-effort-taxonomy.py"

_spec = ilu.spec_from_file_location("check_effort_taxonomy", CHECKER_PATH)
checker = ilu.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(checker)


def minimal_taxonomy(categories=None, floor=20):
    categories = categories or {"proof_assembly": "writing proof terms"}
    return {
        "floor": floor,
        "category_order": list(categories.keys()),
        "categories": categories,
    }


def minimal_episode(**overrides):
    ep = {
        "id": "ep1",
        "source": "docs/plan/status/README.md",  # a file that genuinely exists
        "lane": "some-lane",
        "primary_category": "proof_assembly",
        "secondary_categories": [],
        "kind": "completed",
        "domain": "mathematical",
        "basis": "self-report",
        "corroboration": {"type": "none", "refs": []},
        "summary": "did a thing",
    }
    ep.update(overrides)
    return ep


class TestG1Floor(unittest.TestCase):
    def test_below_floor_is_flagged(self):
        taxonomy = minimal_taxonomy(floor=5)
        episodes = [minimal_episode(id="only-one")]
        v = checker.guard_floor(taxonomy, episodes)
        self.assertTrue(v, "below-floor episode count must be flagged")
        self.assertIn("G1", v[0])

    def test_at_floor_is_clean(self):
        taxonomy = minimal_taxonomy(floor=2)
        episodes = [minimal_episode(id="a"), minimal_episode(id="b")]
        v = checker.guard_floor(taxonomy, episodes)
        self.assertFalse(v, "meeting the floor must not be flagged")


class TestG2CategoriesDefined(unittest.TestCase):
    def test_used_but_undefined_category_is_flagged(self):
        taxonomy = minimal_taxonomy(categories={"proof_assembly": "x"})
        episodes = [minimal_episode(primary_category="ghost_category")]
        v = checker.guard_categories_defined(taxonomy, episodes)
        self.assertTrue(v)
        self.assertIn("ghost_category", v[0])

    def test_secondary_category_must_also_be_defined(self):
        taxonomy = minimal_taxonomy(categories={"proof_assembly": "x"})
        episodes = [minimal_episode(secondary_categories=["also_ghost"])]
        v = checker.guard_categories_defined(taxonomy, episodes)
        self.assertTrue(v)

    def test_defined_category_is_clean(self):
        taxonomy = minimal_taxonomy(categories={"proof_assembly": "x"})
        episodes = [minimal_episode()]
        v = checker.guard_categories_defined(taxonomy, episodes)
        self.assertFalse(v)


class TestG3RequiredFields(unittest.TestCase):
    def test_missing_field_is_flagged(self):
        ep = minimal_episode()
        del ep["summary"]
        v = checker.guard_required_fields([ep])
        self.assertTrue(v)

    def test_empty_field_is_flagged(self):
        ep = minimal_episode(lane="   ")
        v = checker.guard_required_fields([ep])
        self.assertTrue(v)

    def test_bad_kind_enum_is_flagged(self):
        ep = minimal_episode(kind="vibes")
        v = checker.guard_required_fields([ep])
        self.assertTrue(any("kind" in line for line in v))

    def test_well_formed_episode_is_clean(self):
        v = checker.guard_required_fields([minimal_episode()])
        self.assertFalse(v)


class TestG4BasisCorroborationShape(unittest.TestCase):
    def test_self_report_with_corroboration_is_flagged(self):
        ep = minimal_episode(
            basis="self-report",
            corroboration={"type": "commit", "refs": ["deadbeef"]},
        )
        v = checker.guard_basis_corroboration_shape([ep])
        self.assertTrue(v)

    def test_corroborated_with_empty_refs_is_flagged(self):
        ep = minimal_episode(
            basis="corroborated", corroboration={"type": "commit", "refs": []}
        )
        v = checker.guard_basis_corroboration_shape([ep])
        self.assertTrue(v)

    def test_consistent_shapes_are_clean(self):
        v = checker.guard_basis_corroboration_shape([minimal_episode()])
        self.assertFalse(v)


class TestG5CorroborationReverified(unittest.TestCase):
    def test_dangling_refs_of_every_type_are_flagged(self):
        episodes = [
            minimal_episode(
                id="bad-commit",
                basis="corroborated",
                corroboration={"type": "commit", "refs": ["0" * 40]},
            ),
            minimal_episode(
                id="bad-adr",
                basis="corroborated",
                corroboration={"type": "adr", "refs": ["9999"]},
            ),
            minimal_episode(
                id="bad-file",
                basis="corroborated",
                corroboration={
                    "type": "file",
                    "refs": ["this/path/does/not/exist.rs"],
                },
            ),
        ]
        v = checker.guard_corroboration_reverified(episodes)
        self.assertEqual(len(v), 3, f"expected exactly 3 violations, got: {v}")

    def test_real_refs_are_clean(self):
        episodes = [
            minimal_episode(
                basis="corroborated",
                corroboration={"type": "file", "refs": ["docs/plan/status/README.md"]},
            )
        ]
        v = checker.guard_corroboration_reverified(episodes)
        self.assertFalse(v)


class TestG6SourceExists(unittest.TestCase):
    def test_dangling_source_is_flagged(self):
        ep = minimal_episode(source="docs/plan/status/does-not-exist-xyz.md")
        v = checker.guard_source_exists([ep])
        self.assertTrue(v)

    def test_real_source_is_clean(self):
        v = checker.guard_source_exists([minimal_episode()])
        self.assertFalse(v)


class TestG7Coverage(unittest.TestCase):
    def test_all_completed_is_flagged_for_missing_declined(self):
        episodes = [
            minimal_episode(id="a", kind="completed", domain="mathematical"),
            minimal_episode(id="b", kind="completed", domain="infrastructural"),
        ]
        v = checker.guard_coverage(episodes)
        self.assertTrue(any("declined" in line for line in v))

    def test_all_mathematical_is_flagged_for_missing_infrastructural(self):
        episodes = [
            minimal_episode(id="a", kind="completed", domain="mathematical"),
            minimal_episode(id="b", kind="declined", domain="mathematical"),
        ]
        v = checker.guard_coverage(episodes)
        self.assertTrue(any("infrastructural" in line for line in v))

    def test_full_coverage_is_clean(self):
        episodes = [
            minimal_episode(id="a", kind="completed", domain="mathematical"),
            minimal_episode(id="b", kind="declined", domain="infrastructural"),
        ]
        v = checker.guard_coverage(episodes)
        self.assertFalse(v)


class TestG8NoDuplicateIds(unittest.TestCase):
    def test_duplicate_id_is_flagged(self):
        episodes = [minimal_episode(id="dup"), minimal_episode(id="dup")]
        v = checker.guard_no_duplicate_ids(episodes)
        self.assertTrue(v)

    def test_unique_ids_are_clean(self):
        episodes = [minimal_episode(id="a"), minimal_episode(id="b")]
        v = checker.guard_no_duplicate_ids(episodes)
        self.assertFalse(v)


class TestG9GeneratedFresh(unittest.TestCase):
    """Corrupts the real committed distribution.json briefly, in-process,
    and restores it in finally -- this is the one guard that has to look at
    the real generated artifact rather than a scratch fixture, since
    gen-effort-taxonomy.py --check has no --taxonomy/--episodes override."""

    def test_stale_artifact_is_flagged(self):
        dist_path = checker._gen.DISTRIBUTION_PATH
        original = dist_path.read_text()
        try:
            dist_path.write_text('{"deliberately": "wrong"}\n')
            v = checker.guard_generated_fresh(checker.TAXONOMY_PATH, checker.EPISODES_PATH)
            self.assertTrue(v, "corrupting distribution.json must be caught")
        finally:
            dist_path.write_text(original)

    def test_real_artifact_is_fresh(self):
        v = checker.guard_generated_fresh(checker.TAXONOMY_PATH, checker.EPISODES_PATH)
        self.assertFalse(v, "the committed distribution.json/report.md must already be fresh")


class TestPositivePath(unittest.TestCase):
    """The real, committed taxonomy.json + episodes.json must pass every
    guard at once -- this is the control that proves the guards, run
    together, do not reject the actual deliverable."""

    def test_real_inputs_pass_every_guard(self):
        taxonomy = json.loads(checker.TAXONOMY_PATH.read_text())
        episodes = json.loads(checker.EPISODES_PATH.read_text())
        violations = checker.run_all_guards(taxonomy, episodes)
        self.assertEqual(violations, [], f"real inputs should be clean: {violations}")


if __name__ == "__main__":
    unittest.main()
