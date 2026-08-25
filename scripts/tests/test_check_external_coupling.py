#!/usr/bin/env python3
"""Controls for `scripts/check-external-coupling.py`.

One test per guard, each driving its own rejection path over a synthetic
document -- deliberately NOT one shared validity check with several callers,
which is the shape that once made six of seven guards in another suite
removable with everything still green.

The committed tree is clean, which is exactly the situation in which a gate is
indistinguishable from a no-op. So the positive direction is pinned too:
`HistoricalViolationTests` runs the gate over the REAL artifacts as they stood
at `56eaab2cc`, before this change, and requires it to find the coupling. If
that class ever goes quiet, the gate has stopped working and a green tree will
not tell you.

Registered in `scripts/tests/mutation_controls.py` under `external-coupling`.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-external-coupling.py"

_spec = importlib.util.spec_from_file_location("check_external_coupling", SCRIPT)
assert _spec is not None and _spec.loader is not None
GATE = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(GATE)


def findings(doc) -> list[str]:
    found, _seen = GATE.scan_document(doc, "<test>")
    return found


class R1ExternalVocabulary(unittest.TestCase):
    def test_the_external_vocabulary_is_rejected_wherever_it_appears(self) -> None:
        """One test, every value and every position -- the three cases share one
        guard, so three tests would all die together and the mutation harness
        would report the guard as over-covered rather than as covered once.

        The schema case is not decoration: after the overlay's DATA was clean,
        its schema still offered `external-repository`, `external-artifact` and
        `external-pinned` in enums, which is an invitation to put them back."""
        cases = {
            "source kind": {"sources": [{"id": "s", "kind": "external-repository"}]},
            "namespace resolution": {"namespaces": [{"resolution": "external-pinned"}]},
            "schema enum": {"properties": {"kind": {"enum": ["local", "external-artifact"]}}},
        }
        missed = [
            label for label, doc in cases.items()
            if not any("declares a dependency" in f for f in findings(doc))
        ]
        self.assertEqual(missed, [], "the vocabulary guard did not fire for these")


class R2EscapingPath(unittest.TestCase):
    def test_an_escaping_path_is_rejected(self) -> None:
        """Both positions, one guard. The second matters more: the overlay hid
        its escapes in `provenance.sources` -- a list of free-form strings --
        not in anything named like a path field, so a rule that only inspected
        path-shaped KEYS would have missed 24 of them."""
        cases = {
            "a path field": {"sources": [{"path_hint": "../math-education"}]},
            "inside a provenance list": {
                "provenance": {"sources": ["../sibling/graph/x.md"]}
            },
        }
        missed = [
            label for label, doc in cases.items()
            if not any("`..` segment" in f for f in findings(doc))
        ]
        self.assertEqual(missed, [], "the escaping-path guard did not fire for these")

    def test_a_local_path_containing_two_dots_is_not_rejected(self) -> None:
        """`..` must mean a path SEGMENT, not any two adjacent dots -- otherwise
        every version string and ellipsis in the tree is a finding."""
        found = findings({"note": "the range 1..10", "path": "artifacts/v1.2..json"})
        self.assertEqual(found, [])


class R3RevisionRegistry(unittest.TestCase):
    def test_an_unregistered_revision_key_is_rejected_and_named(self) -> None:
        """`graph_pin` is the real one: it sat on all 104 claims. The message
        must NAME the key, or the reader has 1,885 files to search."""
        found = findings({"provenance": {"graph_pin": "a" * 40}})
        self.assertTrue(any("unregistered key" in f for f in found), found)
        self.assertTrue(any("`graph_pin`" in f for f in found), found)

    def test_a_registered_local_key_is_accepted(self) -> None:
        self.assertEqual(findings({"provenance": {"axeyum_commit": "a" * 40}}), [])

    def test_a_registered_foreign_import_is_accepted(self) -> None:
        """R3 forbids an UNDECLARED pin, not a foreign one. Mathlib is pinned
        on purpose; the `imported-kernel-lean` route depends on it."""
        self.assertEqual(findings({"pin": {"mathlib_commit": "b" * 40}}), [])

    def test_every_registered_key_names_a_repository(self) -> None:
        for key, repo in GATE.REVISION_KEYS.items():
            self.assertTrue(repo and isinstance(repo, str), key)


class R4SourceEscape(unittest.TestCase):
    """R4 is the rule the first draft of this gate got wrong.

    That draft scanned `scripts/` only. The single largest piece of coupling in
    the repository was `python/axeyum/knowledge/math_education.py` -- 777 lines
    whose first constant was `Path("..") / "math-education"` and whose whole
    purpose was reading a sibling checkout -- and the gate reported
    `findings=0` over it, twice: once for the missing root, once for the
    missing needle. Both halves are pinned here.
    """

    def scan_with(self, name: str, source: str) -> list[str]:
        """Run the source rule over a scratch tree holding one file."""
        original = GATE.SOURCE_ROOTS
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            (root / name).write_text(source)
            try:
                GATE.SOURCE_ROOTS = ((root, "**/*.py"),)
                found, _files = GATE.scan_source()
            finally:
                GATE.SOURCE_ROOTS = original
        return found

    def test_every_escape_expression_is_caught(self) -> None:
        cases = {
            "parent of the checkout": "SIBLING = ROOT.parent / 'other'\n",
            "a home directory": 'P = os.path.expanduser("~/projects/other")\n',
            "a dotdot path component": 'HINT = Path("..") / "other"\n',
            "a dotdot join": 'HINT = base / ".."\n',
        }
        missed = [
            label for label, src in cases.items()
            if not any("ADR-0553 R4" in f for f in self.scan_with("m.py", src))
        ]
        self.assertEqual(missed, [], "the source-escape guard did not fire for these")

    def test_the_deleted_integration_module_would_be_caught(self) -> None:
        """The positive control that matters: not a synthetic line, the actual
        777-line module, read from the commit that still had it."""
        blob = subprocess.run(
            ["git", "show", "HEAD:python/axeyum/knowledge/math_education.py"],
            capture_output=True, text=True, cwd=str(ROOT), check=False,
        )
        if blob.returncode != 0:
            self.skipTest("the module is no longer reachable from HEAD")
        found = self.scan_with("math_education.py", blob.stdout)
        self.assertTrue(any("ADR-0553 R4" in f for f in found), found)

    def test_a_relative_markdown_link_is_not_an_escape(self) -> None:
        """`scripts/` alone holds 13 `"../"` strings, every one a doc link or an
        upstream case id. A rule that flagged those would be deleted within a
        week, and R4 with it."""
        source = 'LINK = f"../notes/{name}.md"\nCASE = "../doc/examples/compiler"\n'
        self.assertEqual(self.scan_with("m.py", source), [])

    def test_a_docstring_naming_a_removed_escape_is_not_a_finding(self) -> None:
        """`check-reachability-census.py` documents the default path it used to
        carry. Naming what was removed is how the next reader learns; only code
        below the docstring is scanned."""
        source = '"""We used to default to expanduser("~/x") -- ADR-0553."""\nX = 1\n'
        self.assertEqual(self.scan_with("m.py", source), [])

    def test_test_directories_are_skipped(self) -> None:
        original = GATE.SOURCE_ROOTS
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            (root / "tests").mkdir()
            (root / "tests" / "t.py").write_text('HINT = Path("..") / "x"\n')
            try:
                GATE.SOURCE_ROOTS = ((root, "**/*.py"),)
                found, files = GATE.scan_source()
            finally:
                GATE.SOURCE_ROOTS = original
        self.assertEqual((found, files), ([], 0))


class VacuityTests(unittest.TestCase):
    """A scan that examined nothing must FAIL, never pass."""

    def test_no_artifacts_scanned_is_a_finding(self) -> None:
        found = GATE.vacuity(files=0, strings=1, script_files=1)
        self.assertTrue(any("scanned 0 JSON artifacts" in f for f in found), found)

    def test_no_strings_examined_is_a_finding(self) -> None:
        """Distinct from the above: files can match while the walker fails to
        reach any leaf, and that reads as a clean tree."""
        found = GATE.vacuity(files=9, strings=0, script_files=1)
        self.assertTrue(any("examined 0 string values" in f for f in found), found)

    def test_no_scripts_scanned_is_a_finding(self) -> None:
        found = GATE.vacuity(files=1, strings=1, script_files=0)
        self.assertTrue(any("scanned 0 python files" in f for f in found), found)

    def test_a_healthy_scan_is_not_a_finding(self) -> None:
        self.assertEqual(GATE.vacuity(files=1, strings=1, script_files=1), [])

    def test_the_directory_scan_really_can_come_back_empty(self) -> None:
        """The vacuity guards are only worth anything if the counts they read
        can actually be zero. Point the gate at nothing and watch it happen."""
        original = GATE.ARTIFACTS
        try:
            GATE.ARTIFACTS = ROOT / "no-such-directory"
            _found, files, strings = GATE.scan_artifacts()
        finally:
            GATE.ARTIFACTS = original
        self.assertEqual((files, strings), (0, 0))


def git_available() -> bool:
    return (ROOT / ".git").exists()


class HistoricalViolationTests(unittest.TestCase):
    """The positive control: the gate must fire on what actually happened.

    A gate proven only against a clean tree is proven against nothing. These
    are the REAL artifacts at `56eaab2cc`, the state this change removed, read
    from git so they cannot rot as the working tree moves.

    THESE TESTS DO NOT RUN UNDER THE MUTATION HARNESS, and that is stated here
    rather than discovered later. `mutation_controls.py` copies the tree with
    `ignore_patterns(".git", ...)`, so `git show` fails in its scratch root and
    every test in this class skips -- the same shape `test_validate_tactic_catalog.py`
    documents, where a live-sibling test SKIPs and its guard reads as covered.

    It is safe here, and only because of a property worth stating explicitly:
    EVERY GUARD ALREADY HAS ITS OWN HERMETIC CONTROL (`R1ExternalVocabulary`,
    `R2EscapingPath`, `R3RevisionRegistry`, `R4SourceEscape` build their inputs
    in memory or under `tempfile`). Nothing in this class is the sole cover for
    anything, so the skip costs evidence, not coverage. `test_the_historical_
    controls_are_not_silently_skipped` keeps that honest: where `.git` exists,
    the base commit must be reachable, so "always skipped everywhere" cannot
    become the steady state without a test going red.
    """

    BASE = "56eaab2cc"

    def at_base(self, path: str):
        blob = subprocess.run(
            ["git", "show", f"{self.BASE}:{path}"],
            capture_output=True, text=True, cwd=str(ROOT), check=False,
        )
        if blob.returncode != 0:
            self.skipTest(f"{self.BASE} not reachable in this checkout")
        return json.loads(blob.stdout)

    def test_the_historical_controls_are_not_silently_skipped(self) -> None:
        """In a real checkout the base commit MUST be reachable.

        Without this, the class degrades to a permanent no-op the moment the
        commit falls out of history, and a suite that skips everything reports
        the same green as a suite that checks everything."""
        if not git_available():
            self.skipTest("no .git here -- expected under the mutation harness")
        blob = subprocess.run(
            ["git", "cat-file", "-e", f"{self.BASE}^{{commit}}"],
            capture_output=True, text=True, cwd=str(ROOT), check=False,
        )
        self.assertEqual(
            blob.returncode, 0,
            f"{self.BASE} is gone from history; re-pin these controls to a "
            "commit that still carries the coupling, or vendor the documents",
        )

    def test_the_overlay_as_it_stood_is_rejected(self) -> None:
        found = findings(self.at_base("artifacts/autogenesis/knowledge-overlay-v1.json"))
        self.assertTrue(any("external-repository" in f for f in found), found)
        self.assertTrue(any("external-pinned" in f for f in found), found)
        self.assertTrue(any("`..` segment" in f for f in found), found)
        self.assertGreaterEqual(len(found), 50)

    def test_the_crosswalk_as_it_stood_is_rejected(self) -> None:
        found = findings(
            self.at_base("artifacts/autogenesis/family-concept-crosswalk-v1.json")
        )
        self.assertTrue(any("math-education/graph/concepts" in f for f in found), found)

    def test_a_claim_as_it_stood_is_rejected_for_its_graph_pin(self) -> None:
        found = findings(self.at_base("artifacts/claims/rado/rado-r3-a1-b1/claim.json"))
        self.assertTrue(any("`graph_pin`" in f for f in found), found)

    def test_the_tactic_catalog_as_it_stood_is_rejected(self) -> None:
        found = findings(self.at_base("artifacts/autogenesis/tactic-catalog-v1.json"))
        self.assertEqual(len(found), 9, "one per tactic's uses_technique revision")


class CommandLineTests(unittest.TestCase):
    """The exit status must depend on the finding, not on the run completing."""

    def run_gate(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *args],
            capture_output=True, text=True, cwd=str(ROOT), check=False,
        )

    def test_the_committed_tree_exits_zero_and_reports_what_it_scanned(self) -> None:
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stderr)
        line = done.stdout.strip().splitlines()[-1]
        self.assertTrue(line.startswith("EXTERNAL_COUPLING|"), line)
        fields = dict(part.split("=", 1) for part in line.split("|")[1:])
        self.assertGreater(int(fields["artifacts"]), 1000)
        self.assertGreater(int(fields["strings"]), 10000)
        self.assertGreater(int(fields["scripts"]), 100)
        self.assertEqual(int(fields["findings"]), 0)

    def test_the_exit_status_depends_on_the_finding(self) -> None:
        """Not on the run completing. 40 of 162 checker runs audited in this
        repository exited 0 on completion alone.

        The finding is INJECTED rather than provoked through a rule. Driving
        this through a real `..` violation made mutating R2 kill this test as
        well, so one guard reported two dead controls and the exit-status line
        had no control of its own."""
        original = GATE.scan_artifacts
        try:
            GATE.scan_artifacts = lambda: (["<injected finding>"], 1, 1)
            status = GATE.main([])
        finally:
            GATE.scan_artifacts = original
        self.assertEqual(status, 1)

    def test_a_run_with_nothing_to_report_exits_zero(self) -> None:
        """The other direction, or the test above passes on `return 1`."""
        self.assertEqual(self.run_gate().returncode, 0)


if __name__ == "__main__":
    unittest.main()
