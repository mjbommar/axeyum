#!/usr/bin/env python3
"""Scope controls for ``scripts/check-shell-antipatterns.sh``.

The 2026-08-30 session audit's fifth survivor: this gate was **correct and
under-scoped**.  Its detector was verified in both directions by
``scripts/tests/test-check-shell-antipatterns.sh`` — which keeps that job, and
also asserts the gate is green on the real tree — but the scan set was
``git ls-files '*.sh'``, so the two tracked shell scripts *without* that
extension were never read, and both violated:

* ``hooks/commit-msg:36`` — ``head -1 "$f" | grep -qiE '^(merge|revert|…)'``
* ``hooks/pre-push:249`` — ``printf '%s\\n' "$out" | grep -qE '^running [1-9]'``

The second is the nonzero-test-count guard this repository leans on hardest,
built from the exact idiom that reads a SIGPIPE as "no match".  Both are fixed;
``hooks/`` is now scanned.

**Scope is the thing that reverts silently**, which is why it needs controls of
its own: narrowing the enumeration back to ``*.sh`` leaves every number in the
gate's summary line unchanged and every detector control green.

Every scenario here is **hermetic** — ``AXEYUM_SHELL_ANTIPATTERN_ROOT`` points
the shipped script at a throwaway git repository the test builds, so each guard
can be driven to failure on a tree where the real one would never reach it.
That also makes the suite runnable inside ``mutation_controls.py``'s scratch
copy, which excludes ``.git`` and therefore cannot answer ``git ls-files`` at
all.  Registered as ``shell-antipatterns-scope``::

    python3 -m unittest scripts.tests.test_check_shell_antipatterns_scope
    python3 scripts/tests/mutation_controls.py shell-antipatterns-scope
"""

from __future__ import annotations

import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
GATE = ROOT / "scripts/check-shell-antipatterns.sh"

# The files whose absence from the scan set was the finding.
MOTIVATING = ("hooks/pre-push", "hooks/commit-msg")

CLEAN_HOOK = """#!/usr/bin/env bash
set -euo pipefail
if [ "$(printf '%s\\n' "$1" | grep -cE '^ok')" -gt 0 ]; then
  exit 0
fi
"""

# An ordinary `*.sh` with one genuine violation, matching the baseline below.
VIOLATING_SH = """#!/usr/bin/env bash
set -uo pipefail
cmd | grep -q pattern
"""

# Executable, no `.sh`, no shebang: must NOT be scanned. Its `| grep -q` is
# what makes the negative meaningful -- if the probe scanned it, the gate would
# report a NEW file and go red.
EXECUTABLE_NOT_SHELL = """#!/usr/bin/env python3
# set -o pipefail
# cmd | grep -q pattern
"""

# NOT executable but carries a shell shebang. The mode filter must skip it; its
# violation is the tell.
UNEXECUTABLE_WITH_SHEBANG = """#!/usr/bin/env bash
set -uo pipefail
cmd | grep -q pattern
"""

# A sourced fragment: `.sh`, not executable, no shebang. Scanned because of the
# extension, never because of the probe.
FRAGMENT_SH = """# sourced, not executed
set -uo pipefail
"""


class ShellAntipatternScope(unittest.TestCase):
    """One scenario per scope guard, on a synthetic tree."""

    def setUp(self) -> None:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name) / "tree"
        (self.root / "scripts").mkdir(parents=True)
        self.git("init", "-q")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")

        self.write("hooks/pre-push", CLEAN_HOOK, mode=0o755)
        self.write("hooks/commit-msg", CLEAN_HOOK, mode=0o755)
        self.write("scripts/a.sh", VIOLATING_SH, mode=0o755)
        self.write("scripts/frag.sh", FRAGMENT_SH, mode=0o644)
        self.write("tools/gen.py", EXECUTABLE_NOT_SHELL, mode=0o755)
        self.write("docs/example.txt", UNEXECUTABLE_WITH_SHEBANG, mode=0o644)
        self.write("scripts/check-shell-antipatterns.baseline", "scripts/a.sh 1\n")
        self.git("add", "-A")
        self.git("commit", "-qm", "base")

    # -- tree construction --------------------------------------------------

    def _env(self, **overrides: str) -> dict[str, str]:
        env = dict(os.environ)
        # A lane exports GIT_INDEX_FILE (CLAUDE.md's per-process index remedy);
        # inherited here it points at the REAL checkout's index.
        for var in ("GIT_INDEX_FILE", "GIT_DIR", "GIT_WORK_TREE", "GIT_CONFIG"):
            env.pop(var, None)
        env["AXEYUM_SHELL_ANTIPATTERN_ROOT"] = str(self.root)
        # The synthetic tree has six files, so the real floor of 100 would fire
        # in every scenario. Scenarios that TEST the floor raise it instead.
        env.setdefault("AXEYUM_SHELL_ANTIPATTERN_MIN_SCAN", "1")
        env.update(overrides)
        return env

    def git(self, *args: str) -> None:
        subprocess.run(("git", *args), cwd=self.root, check=True, env=self._env(),
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def write(self, rel: str, text: str, *, mode: int = 0o644) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        path.chmod(mode)

    def run_gate(self, *args: str, **overrides: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["bash", str(GATE), *args], cwd=ROOT, env=self._env(**overrides),
            capture_output=True, text=True, timeout=300,
        )

    def scanned(self, **overrides: str) -> list[str]:
        done = self.run_gate("--list-scanned", **overrides)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        return [line for line in done.stdout.splitlines() if line.strip()]

    # -- the accept case ----------------------------------------------------

    def test_the_synthetic_tree_is_green(self) -> None:
        """The positive control. Every scenario below asserts a FAILURE or an
        absence, and without this one they are satisfied by a gate that never
        passes and a scan set that is always empty."""
        done = self.run_gate()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("|grep_q_in_pipeline=1|", done.stdout)

    # -- guard: what the enumeration reaches --------------------------------

    def test_extensionless_executables_with_a_shell_shebang_are_scanned(self) -> None:
        """The finding. `git ls-files '*.sh'` never reached either hook."""
        found = set(self.scanned())
        for path in MOTIVATING:
            self.assertIn(path, found)

    def test_sh_files_are_scanned_whatever_their_mode(self) -> None:
        """A sourced fragment has no shebang and is not executable, so only the
        extension puts it in the set. A probe rewritten to look at mode alone
        would pass the test above and drop every fragment in the tree."""
        self.assertIn("scripts/frag.sh", self.scanned())

    def test_an_executable_that_is_not_shell_is_not_scanned(self) -> None:
        """A python script is executable and is not shell. Its commented
        `| grep -q` would be reported as a NEW violating file if the probe
        stopped reading the shebang."""
        self.assertNotIn("tools/gen.py", self.scanned())

    def test_a_shell_shebang_in_a_non_executable_file_is_not_scanned(self) -> None:
        """Documentation quotes shell constantly. The mode filter is what keeps
        a prose file out, and this fixture violates so its inclusion is loud."""
        self.assertNotIn("docs/example.txt", self.scanned())

    # -- guard: the enumeration itself is sane ------------------------------

    def test_a_collapsed_scan_set_is_refused(self) -> None:
        """A scan set below the floor means the enumeration broke, not that the
        tree became clean -- the failure every count-based gate here has had at
        least once."""
        done = self.run_gate(AXEYUM_SHELL_ANTIPATTERN_MIN_SCAN="1000")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("the scan set collapsed", done.stderr)

    def test_a_required_file_missing_from_the_scan_set_is_refused(self) -> None:
        """A file that should be scanned and is not means the probe regressed.
        The count cannot see this: dropping the hooks and gaining two unrelated
        scripts leaves it unchanged."""
        done = self.run_gate(AXEYUM_SHELL_ANTIPATTERN_REQUIRED="hooks/no-such-hook-abcdef")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("the shebang probe has regressed", done.stderr)

    def test_both_overrides_at_their_synthetic_defaults_are_green(self) -> None:
        """The negative control for the two overrides: without it, the two
        scenarios above could be passing because the gate is red for a reason
        that has nothing to do with what they set."""
        done = self.run_gate(
            AXEYUM_SHELL_ANTIPATTERN_MIN_SCAN="1",
            AXEYUM_SHELL_ANTIPATTERN_REQUIRED=" ".join(MOTIVATING),
        )
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    # -- the detector still works over the widened set ----------------------

    def test_a_violating_hook_is_actually_REPORTED_not_merely_scanned(self) -> None:
        """Widening the scan set is worth nothing if the detector never runs
        over the new files. `hooks/pre-push` is not in the synthetic baseline,
        so a `grep -q` pipeline in it must fail the gate as a NEW file."""
        self.write("hooks/pre-push", VIOLATING_SH, mode=0o755)
        self.git("add", "-A")
        self.git("commit", "-qm", "violate")
        done = self.run_gate()
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("hooks/pre-push", done.stderr)
        self.assertIn("NEW file", done.stderr)


if __name__ == "__main__":
    unittest.main()
