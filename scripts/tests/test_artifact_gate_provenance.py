#!/usr/bin/env python3
"""Controls for `scripts/check-artifact-gate-provenance.py`.

One test per guard, each built to die when *its own* guard is removed and no
other. That disjointness is the property CLAUDE.md records as having failed
before: six of seven guards in one suite were removable with everything still
green, because they all rejected through one shared check.

Every test builds a synthetic repository in a temp directory -- its own
`scripts/`, `scripts/archive/` and `artifacts/`. Pointing the subject at the
live tree would make these controls drift as scripts land, and worse, a fixture
that passes because of today's repository state is a control that stops
controlling on a day nobody is watching.

The two vacuity floors are exercised one at a time, with the *other* floor
lowered out of the way. Both floors fire on an empty tree, so a single
empty-tree test would let either floor be deleted while staying green -- the
exact "guard nobody can remove" shape this suite exists to prevent.
"""

from __future__ import annotations

import importlib.util
import pathlib
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts/check-artifact-gate-provenance.py"


def load_subject():
    spec = importlib.util.spec_from_file_location(
        "check_artifact_gate_provenance", SUBJECT
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class Fixture:
    """A synthetic repository the subject can be pointed at."""

    def __init__(self, tmp: pathlib.Path):
        self.root = tmp
        (tmp / "scripts").mkdir()
        (tmp / "scripts" / "archive").mkdir()
        (tmp / "artifacts").mkdir()

    def live_script(self, name: str, body: str = "# a live gate\n") -> None:
        (self.root / "scripts" / name).write_text(body, encoding="utf-8")

    def archived_script(self, name: str, body: str = "# an archived gate\n") -> None:
        (self.root / "scripts" / "archive" / name).write_text(body, encoding="utf-8")

    def artifact(self, relpath: str, text: str) -> None:
        path = self.root / "artifacts" / relpath
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def guards(failures) -> set[str]:
    return {guard for guard, _ in failures}


class ArtifactGateProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.subject = load_subject()
        self._tmp = tempfile.TemporaryDirectory()
        self.fx = Fixture(pathlib.Path(self._tmp.name))
        self.addCleanup(self._tmp.cleanup)

    def run_check(self, floors: bool = False):
        return self.subject.check(root=self.fx.root, floors=floors)

    # ---- positive control -------------------------------------------------
    # If this ever fails, every negative below is meaningless: they would be
    # "failing" for a reason unrelated to the guard they name.

    def test_a_well_formed_tree_passes(self):
        self.fx.live_script("check-alpha.py")
        self.fx.archived_script("check-retired.py")
        self.fx.artifact("plan.json", '{"gate": "scripts/check-alpha.py"}')
        self.fx.artifact("receipt.json", '{"gate": "check-alpha.py"}')
        failures, citations, siblings, _, _ = self.run_check()
        self.assertEqual(failures, [])
        self.assertEqual(citations, 2, "the scan must actually see both citations")
        self.assertEqual(siblings, 0)

    # ---- dangling ---------------------------------------------------------

    def test_a_citation_naming_no_script_anywhere_fails(self):
        self.fx.live_script("check-alpha.py")
        self.fx.artifact("receipt.json", '{"gate": "check-vanished.py"}')
        failures, _, _, _, _ = self.run_check()
        self.assertEqual(guards(failures), {"dangling"})
        self.assertIn("check-vanished.py", failures[0][1])

    # ---- archived ---------------------------------------------------------
    # The citation is a BARE name, so no directory is spelled and the
    # path-mismatch guard cannot also fire. That is what keeps this test
    # attributable to the `archived` guard alone.

    def test_a_citation_of_an_archived_script_fails(self):
        self.fx.archived_script("check-retired.py")
        self.fx.artifact("receipt.json", '{"gate": "check-retired.py"}')
        failures, _, _, _, _ = self.run_check()
        self.assertEqual(guards(failures), {"archived"})
        self.assertIn("check-retired.py", failures[0][1])

    # ---- path-mismatch ----------------------------------------------------
    # The script is LIVE, so `dangling` and `archived` both pass; only the
    # spelled directory is wrong. This is the case `98d17aeef` created 111
    # times in the other direction -- artifacts spelling `scripts/X` for an X
    # that had moved into the archive.

    def test_a_citation_spelling_the_wrong_directory_fails(self):
        self.fx.live_script("check-alpha.py")
        self.fx.artifact("receipt.json", '{"gate": "scripts/archive/check-alpha.py"}')
        failures, _, _, _, _ = self.run_check()
        self.assertEqual(guards(failures), {"path-mismatch"})

    # ---- escape -----------------------------------------------------------

    def test_an_absolute_citation_fails(self):
        self.fx.live_script("check-alpha.py")
        self.fx.artifact("receipt.json", '{"gate": "/scripts/check-alpha.py"}')
        failures, _, _, _, _ = self.run_check()
        self.assertEqual(guards(failures), {"escape"})

    # A regression, not a guard: the first draft of the escape guard rejected
    # any `..` and redded four real artifacts whose relative links resolve
    # perfectly well. A markdown artifact three levels down cites its gate the
    # only way a markdown link can.

    def test_a_relative_markdown_link_is_not_an_escape(self):
        self.fx.live_script("check-alpha.py")
        self.fx.artifact(
            "claims/rado/SEMANTICS.md",
            "checked by [the gate](../../../scripts/check-alpha.py)\n",
        )
        failures, citations, _, _, _ = self.run_check()
        self.assertEqual(failures, [])
        self.assertEqual(citations, 1)

    # ---- sibling ----------------------------------------------------------
    # The second class of caller the original census could not see: a capsule
    # checker invokes its construction-result checker by path.

    def test_a_live_script_invoking_an_archived_sibling_fails(self):
        self.fx.live_script(
            "check-capsule.py", 'RESULT = ROOT / "scripts/check-retired.py"\n'
        )
        self.fx.archived_script("check-retired.py")
        failures, _, siblings, _, _ = self.run_check()
        self.assertEqual(guards(failures), {"sibling"})
        self.assertEqual(siblings, 1)

    def test_a_live_script_invoking_a_live_sibling_passes(self):
        self.fx.live_script(
            "check-capsule.py", 'RESULT = ROOT / "scripts/check-alpha.py"\n'
        )
        self.fx.live_script("check-alpha.py")
        failures, _, siblings, _, _ = self.run_check()
        self.assertEqual(failures, [])
        self.assertEqual(siblings, 1)

    # ---- vacuity ----------------------------------------------------------
    # Each floor is tested with the other lowered to zero, so exactly one can
    # fire. A shared empty-tree test would let either be deleted silently.

    def test_a_scan_reaching_no_artifacts_fails_the_artifact_floor(self):
        self.fx.live_script("check-alpha.py")
        with mock.patch.object(self.subject, "MIN_ARTIFACT_CITATIONS", 5), \
             mock.patch.object(self.subject, "MIN_SIBLING_REFERENCES", 0):
            failures, citations, _, _, _ = self.run_check(floors=True)
        self.assertEqual(guards(failures), {"vacuity"})
        self.assertEqual(citations, 0)
        self.assertIn("artifact citations", failures[0][1])

    def test_a_scan_reaching_no_scripts_fails_the_sibling_floor(self):
        self.fx.live_script("check-alpha.py")
        self.fx.artifact("receipt.json", '{"gate": "check-alpha.py"}')
        with mock.patch.object(self.subject, "MIN_ARTIFACT_CITATIONS", 0), \
             mock.patch.object(self.subject, "MIN_SIBLING_REFERENCES", 5):
            failures, _, siblings, _, _ = self.run_check(floors=True)
        self.assertEqual(guards(failures), {"vacuity"})
        self.assertEqual(siblings, 0)
        self.assertIn("sibling references", failures[0][1])

    # ---- the live tree ----------------------------------------------------
    # The gate is only worth having if it is green on the repository it gates,
    # and only meaningful if it looked at a real amount of it.

    def test_the_live_repository_passes_with_a_nonzero_scan(self):
        failures, citations, siblings, live, archived = self.subject.check()
        self.assertEqual(failures, [], "the live tree has broken gate citations")
        self.assertGreaterEqual(citations, self.subject.MIN_ARTIFACT_CITATIONS)
        self.assertGreaterEqual(siblings, self.subject.MIN_SIBLING_REFERENCES)
        self.assertGreater(live, 0)
        self.assertGreater(archived, 0)


if __name__ == "__main__":
    unittest.main()
