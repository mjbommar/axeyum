"""Unit tests for scripts/gen-declaration-spec.py's validation guards
(L3 phase D1, ADR-0965). Registered as the `declaration-spec` suite in
`scripts/tests/mutation_controls.py`; each test here is the control for
exactly one guard mutation in that registration.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / "scripts" / "gen-declaration-spec.py"
SPECS_DIR = ROOT / "artifacts" / "declaration-spec"
FIXTURES_DIR = SPECS_DIR / "negative-fixtures"
SNAPSHOT = SPECS_DIR / "generated" / "kernel-names-snapshot.txt"
PILOT = SPECS_DIR / "nat-squarefree.json"


def run_gen(only_path: Path | None, specs_dir: Path | None = None) -> subprocess.CompletedProcess:
    cmd = [sys.executable, str(GEN), "--check"]
    if only_path is not None:
        cmd += ["--only", str(only_path)]
    if specs_dir is not None:
        cmd += ["--specs-dir", str(specs_dir)]
    if SNAPSHOT.exists():
        cmd += ["--snapshot", str(SNAPSHOT)]
    else:
        cmd += ["--skip-cross-prelude"]
    return subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT)


class PilotSpecPasses(unittest.TestCase):
    """Positive control: the pilot spec itself must always validate clean."""

    def test_pilot_spec_passes(self):
        result = run_gen(PILOT)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("verdict=PASS", result.stdout)


class DuplicateNameInCorpusGuard(unittest.TestCase):
    def test_fires(self):
        result = run_gen(FIXTURES_DIR / "dup-name-in-corpus.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GUARD:DUPLICATE_NAME", result.stdout)


class CrossPreludeDuplicateGuard(unittest.TestCase):
    def test_fires(self):
        if not SNAPSHOT.exists():
            self.skipTest("no kernel name snapshot -- run check-declaration-spec.py first")
        result = run_gen(FIXTURES_DIR / "dup-name-cross-prelude.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GUARD:CROSS_PRELUDE_DUPLICATE", result.stdout)


class MissingPhaseGuard(unittest.TestCase):
    def test_fires(self):
        result = run_gen(FIXTURES_DIR / "missing-phase.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GUARD:MISSING_PHASE", result.stdout)


class DependencyCycleGuard(unittest.TestCase):
    def test_fires(self):
        result = run_gen(FIXTURES_DIR / "dependency-cycle.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GUARD:DEPENDENCY_CYCLE", result.stdout)


class PhaseOrderGuard(unittest.TestCase):
    """`dependency-cycle.json` trips both DEPENDENCY_CYCLE and PHASE_ORDER
    (see the fixture's own `_comment`); asserting on PHASE_ORDER specifically
    isolates this guard from the cycle-detector even though both read the
    same fixture."""

    def test_fires(self):
        result = run_gen(FIXTURES_DIR / "dependency-cycle.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GUARD:PHASE_ORDER", result.stdout)


class DepMismatchGuard(unittest.TestCase):
    def test_fires(self):
        result = run_gen(FIXTURES_DIR / "dep-mismatch.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GUARD:DEP_MISMATCH", result.stdout)


class EmptyCorpusGuard(unittest.TestCase):
    """Asserts the EXACT message text, not just a nonzero exit code: a
    second, unrelated guard (`checked_declarations == 0`) also returns 1 for
    an all-empty corpus, so exit-code alone cannot distinguish this guard
    from that one. The message text can."""

    def test_fires(self):
        with tempfile.TemporaryDirectory() as d:
            result = run_gen(None, specs_dir=Path(d))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("no spec files found", result.stderr)


if __name__ == "__main__":
    unittest.main()
