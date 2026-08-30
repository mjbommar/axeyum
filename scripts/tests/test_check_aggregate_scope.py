#!/usr/bin/env python3
"""Failure-path controls for ``scripts/check-aggregate-scope.sh``.

The 2026-08-30 session audit's second survivor.  Replacing the gate's

    if [ -s "$new" ]; then

with ``if false; then`` left the whole registered suite green —
``AGGREGATE_SCOPE_CONTROLS|guards=5|negative_controls=2|PASS``, exit 0.  All
five registered controls test the **normalizer**; none tested the gate's own
decision to fail.  A gate whose failure path nothing exercises reports
divergence as prose and gates nothing.

``scripts/tests/test-check-aggregate-scope.sh`` keeps the normalizer job and is
unchanged apart from one added case (the quote-aware wrapper strip, below).
These scenarios drive the gate END TO END on a **synthetic** tree: two stub
enumerations and a stub expectation file, via
``AXEYUM_AGGREGATE_SCOPE_ROOT``.  Hermetic because the real tree takes 412 + 468
steps to enumerate and — more importantly — because the zero-side refusal
cannot be reached on it at all.

One live normalizer bug was fixed in the same change and is pinned here:
``strip_wrappers`` *tested* for a leading assignment with a quote-aware regex
and *stripped* it with ``line.split(" ", 1)``, which cuts at the first space —
inside the quotes::

    RUSTDOCFLAGS="-D warnings" cargo doc …   ->   warnings" cargo doc …

so one ``cargo doc`` step appeared on both sides under two spellings and was
baselined as two accepted divergences that do not exist.  Measured against
every subject: the divergence count goes 66 -> 64, both step counts are
unchanged, and the diff of the recorded sets is exactly that pair.

Registered as ``aggregate-scope-failure``::

    python3 -m unittest scripts.tests.test_check_aggregate_scope
    python3 scripts/tests/mutation_controls.py aggregate-scope-failure
"""

from __future__ import annotations

import os
import pathlib
import re
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
GATE = ROOT / "scripts/check-aggregate-scope.sh"

HEADER = "# Accepted divergence between ./scripts/check.sh and `just check`.\n"


def strip_wrappers():
    """The SHIPPED normalizer, extracted from the gate rather than copied.

    Extraction failure is a failure: a control suite that cannot find its
    subject must not report success.
    """
    src = GATE.read_text()
    match = re.search(r"normalize\(\)\s*\{\s*\n\s*python3 -c '(.*?)'\n", src, re.S)
    if not match:
        raise AssertionError(
            "could not find normalize()'s python body in "
            "scripts/check-aggregate-scope.sh"
        )
    namespace: dict = {}
    exec(match.group(1), namespace)  # noqa: S102 - the subject under test
    if "strip_wrappers" not in namespace:
        raise AssertionError("no strip_wrappers() in the extracted body")
    return namespace["strip_wrappers"]


class AggregateScopeNormalizer(unittest.TestCase):
    """The one normalizer guard added with the failure-path work."""

    def test_a_quoted_environment_assignment_is_stripped_whole(self) -> None:
        norm = strip_wrappers()
        self.assertEqual(
            norm('RUSTDOCFLAGS="-D warnings" cargo doc --workspace'),
            norm("cargo doc --workspace"),
        )

    def test_several_assignments_including_a_quoted_one_are_stripped(self) -> None:
        norm = strip_wrappers()
        self.assertEqual(norm('FOO="a b c" BAR=1 cmd --flag'), norm("cmd --flag"))

    def test_a_quoted_assignment_does_not_erase_the_command(self) -> None:
        """The negative direction: a strip that consumed too much would make
        two genuinely different steps normalize to the same key, and the gate
        would report zero divergences for ever."""
        norm = strip_wrappers()
        self.assertNotEqual(
            norm('FOO="x" cargo doc --workspace'),
            norm('FOO="x" cargo doc --no-deps'),
        )


class AggregateScopeFailurePath(unittest.TestCase):
    """One scenario per exit path of the gate itself."""

    def setUp(self) -> None:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name) / "tree"
        (self.root / "scripts").mkdir(parents=True)

    # -- tree construction --------------------------------------------------

    def sides(self, sh: list[str], just: list[str]) -> None:
        """Write the two stub enumerations.

        `check.sh` prints TAB-separated `<n>\\t<step>` under
        `AXEYUM_CHECK_LIST=1`, which the gate consumes with `cut -f2-`.
        `just -n check` prints the recipe body to STDERR, which is why the gate
        reads it with `2>&1` -- a detail worth reproducing exactly.
        """
        # The steps go in a data file rather than into the stub's source: a
        # step containing double quotes -- which is the whole point of the
        # quoted-wrapper scenario -- cannot survive being interpolated into a
        # shell string, and the first draft of this helper mangled it into
        # `RUSTDOCFLAGS=-D` and reported a divergence that was its own fault.
        (self.root / "scripts/steps.tsv").write_text("".join(f"1\t{s}\n" for s in sh))
        (self.root / "scripts/check.sh").write_text(
            "#!/usr/bin/env bash\ncat scripts/steps.tsv\n"
        )
        (self.root / "scripts/check.sh").chmod(0o755)
        recipe = "".join(f"    {s}\n" for s in just)
        (self.root / "justfile").write_text("check:\n" + recipe)

    def expect(self, lines: list[str]) -> None:
        (self.root / "scripts/check-aggregate-scope.expected").write_text(
            HEADER + "".join(line + "\n" for line in lines)
        )

    def run_gate(self, *args: str) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        env["AXEYUM_AGGREGATE_SCOPE_ROOT"] = str(self.root)
        return subprocess.run(
            ["bash", str(GATE), *args], cwd=ROOT, env=env,
            capture_output=True, text=True, timeout=300,
        )

    # -- the accept case ----------------------------------------------------

    def test_two_agreeing_sides_pass(self) -> None:
        """The positive control. Every scenario below asserts a nonzero exit,
        and without this one they are all satisfied by a gate that never
        passes."""
        self.sides(["python3 scripts/a.py"], ["python3 scripts/a.py"])
        self.expect([])
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("0 step(s) exist on one side only", done.stdout)

    def test_a_recorded_divergence_passes(self) -> None:
        self.sides(["python3 scripts/a.py", "python3 scripts/b.py"],
                   ["python3 scripts/a.py"])
        self.expect(["check.sh-only: python3 scripts/b.py"])
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("all 1 difference(s) are recorded", done.stdout)

    # -- THE SURVIVOR: the fail-on-new-divergence guard ----------------------

    def test_an_UNRECORDED_divergence_fails(self) -> None:
        """`if [ -s "$new" ]` replaced by `if false` left every registered
        control green. This is the scenario that kills it."""
        self.sides(["python3 scripts/a.py", "python3 scripts/b.py"],
                   ["python3 scripts/a.py"])
        self.expect([])
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("not recorded as accepted", done.stderr)
        self.assertIn("python3 scripts/b.py", done.stderr)

    def test_the_new_divergence_is_NAMED_on_stderr(self) -> None:
        """A count without the step names cannot be acted on, and this gate has
        already sat red because its output was unusable."""
        self.sides(["python3 scripts/a.py"], ["python3 scripts/z.py"])
        self.expect([])
        done = self.run_gate()
        self.assertEqual(done.returncode, 1)
        self.assertIn("check.sh-only: python3 scripts/a.py", done.stderr)
        self.assertIn("just-only:     python3 scripts/z.py", done.stderr)

    def test_a_divergence_on_the_JUST_side_alone_also_fails(self) -> None:
        """Both `comm` arms must reach the failure. A guard reading only one
        direction passes the scenario above."""
        self.sides(["python3 scripts/a.py"],
                   ["python3 scripts/a.py", "python3 scripts/b.py"])
        self.expect([])
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("just-only:     python3 scripts/b.py", done.stderr)

    # -- the other exit paths ------------------------------------------------

    def test_a_side_that_enumerates_ZERO_steps_is_refused(self) -> None:
        """Not a pass and not an ordinary failure: exit 2, because a broken
        enumeration says nothing about the gates. Unreachable on the real tree,
        which is exactly why it needs a synthetic one."""
        self.sides([], ["python3 scripts/a.py"])
        self.expect([])
        done = self.run_gate()
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("enumerated ZERO steps", done.stderr)

    def test_a_missing_expectation_file_is_refused(self) -> None:
        self.sides(["python3 scripts/a.py"], ["python3 scripts/a.py"])
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("run with --update to record", done.stderr)

    def test_a_resolved_difference_is_reported_but_does_not_fail(self) -> None:
        """The two gates agreeing again is good news. It is printed so the
        expectation can be trimmed, and it must not be a red gate."""
        self.sides(["python3 scripts/a.py"], ["python3 scripts/a.py"])
        self.expect(["check.sh-only: python3 scripts/gone.py"])
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("no longer", done.stdout)

    def test_update_records_the_current_divergence_and_then_passes(self) -> None:
        self.sides(["python3 scripts/a.py", "python3 scripts/b.py"],
                   ["python3 scripts/a.py"])
        first = self.run_gate("--update")
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        second = self.run_gate()
        self.assertEqual(second.returncode, 0, second.stdout + second.stderr)

    # -- the normalizer, exercised through the real gate ---------------------

    def test_a_quoted_env_wrapper_is_not_a_divergence_END_TO_END(self) -> None:
        """The live bug, at the level a reader of the gate cares about: one
        side writing `RUSTDOCFLAGS="-D warnings" cargo doc` and the other
        writing `cargo doc` is ONE step, not two divergences. Before the fix
        this scenario reported two."""
        self.sides(['RUSTDOCFLAGS="-D warnings" cargo doc --workspace'],
                   ["cargo doc --workspace"])
        self.expect([])
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("0 step(s) exist on one side only", done.stdout)


if __name__ == "__main__":
    unittest.main()
