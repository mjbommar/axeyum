#!/usr/bin/env python3
"""Controls for S0's census: each guard, deleted, must kill exactly one case.

WHY THIS FILE EXISTS. `scripts/gen-safety-matrix.py` carries its own
`POSITIVE_CONTROLS`, which is the right shape -- an empty result is not a
negative result. What it did not carry is a check that those controls can
FAIL. ADR-0795 measured two that could not:

  1. `exact_statement` moved to a probe id that is in no manifest and no
     ledger. That catches a pin set containing something impossible and
     nothing else, so `"exact_statement": True` written as a constant, and a
     pin set read from `artifacts/facts` instead of the manifest, BOTH exited
     0 with the column still reading 2121/2121.
  2. `circularity` had no control at all, and 24 of its 38 rows were credited
     by `kernel_declaration_projection`, which walks no dependency closure.

Every case below is a mutation whose kill was measured, not assumed, and the
mutations are applied to a COPY of the tree: a mutant on disk in a shared
checkout breaks every other lane's read of the file, and the failures it
causes look like their bug (CLAUDE.md).

Run directly, or through `scripts/run-python-controls.py`, which discovers
`scripts/tests/test_*.py` from the filesystem so this needs no registration.
"""

from __future__ import annotations

import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = "scripts/gen-safety-matrix.py"

# Only what the census reads. Copying `crates/` would make each case minutes.
NEEDED = (
    "scripts",
    "artifacts/facts",
    "artifacts/ontology",
    "artifacts/safety-matrix",
)


class SafetyMatrixControls(unittest.TestCase):
    """Each mutation must be rejected, and by the control that names it."""

    @classmethod
    def setUpClass(cls) -> None:
        cls._tmp = tempfile.TemporaryDirectory(prefix="axeyum-safety-matrix-")
        cls.work = pathlib.Path(cls._tmp.name) / "tree"
        for rel in NEEDED:
            src = ROOT / rel
            if not src.exists():
                raise unittest.SkipTest(f"{rel} absent from the checkout")
            shutil.copytree(src, cls.work / rel)
        cls.subject = cls.work / SUBJECT
        cls.pristine = cls.subject.read_text(encoding="utf-8")
        # Write the artifacts once from the UNMUTATED source, so every case
        # below fails on a control rather than on stale-artifact drift.
        base = cls._run(cls.work, check=False)
        if base.returncode != 0:
            raise AssertionError(
                "the unmutated census does not pass in the scratch tree; "
                f"stdout={base.stdout!r} stderr={base.stderr!r}"
            )

    @classmethod
    def tearDownClass(cls) -> None:
        cls._tmp.cleanup()

    @staticmethod
    def _run(work: pathlib.Path, check: bool) -> subprocess.CompletedProcess:
        argv = [sys.executable, SUBJECT] + (["--check"] if check else [])
        return subprocess.run(
            argv, cwd=work, capture_output=True, text=True, timeout=300
        )

    def _mutate(self, old: str, new: str) -> subprocess.CompletedProcess:
        text = self.pristine
        self.assertIn(
            old, text,
            "anchor absent -- the mutation was NOT APPLIED, which is not a "
            "measurement. Re-derive the anchor against the current subject.",
        )
        self.assertEqual(
            text.count(old), 1,
            "ambiguous anchor: it matches more than once, so nobody can say "
            "which copy was mutated.",
        )
        self.subject.write_text(text.replace(old, new), encoding="utf-8")
        try:
            # `__pycache__` keys on (mtime whole seconds, size); equal-size
            # mutants written back to back reuse the PREVIOUS mutant's
            # bytecode. Subprocess + rmtree is the cheap fix.
            for cache in self.work.rglob("__pycache__"):
                shutil.rmtree(cache, ignore_errors=True)
            return self._run(self.work, check=True)
        finally:
            self.subject.write_text(self.pristine, encoding="utf-8")

    # -- the baseline. Without it "the mutants all fail" says nothing. -------

    def test_the_unmutated_census_passes(self) -> None:
        proc = self._run(self.work, check=True)
        self.assertEqual(
            proc.returncode, 0,
            f"clean tree must pass: {proc.stdout!r} {proc.stderr!r}",
        )
        self.assertIn("SAFETY_MATRIX|PASS", proc.stdout)

    # -- circularity: the column that was 63% false positives ---------------

    def test_a_non_closure_tool_must_not_credit_circularity(self) -> None:
        """`kernel_declaration_projection` walks no closure. ADR-0795."""
        proc = self._mutate(
            're.compile(r"(footprint_closure_audit)")',
            're.compile(r"(footprint_closure_audit|kernel_declaration_projection)")',
        )
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("F:complex-factorquotient.circularity", proc.stderr)

    def test_circularity_must_still_credit_a_real_closure_walk(self) -> None:
        """The other polarity: a column nobody can earn is not a measurement."""
        proc = self._mutate(
            're.compile(r"(footprint_closure_audit)")',
            're.compile(r"(zzz_this_matches_no_committed_command)")',
        )
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("F:cpoint-cauchy-schwarz.circularity", proc.stderr)

    # -- exact_statement: both failures the unpinnable probe cannot see ------

    def test_a_constant_exact_statement_is_rejected(self) -> None:
        """`UNPINNABLE_PROBE` never reaches `classify`, so it misses this."""
        proc = self._mutate(
            '"exact_statement": fact["id"] in pinned,',
            '"exact_statement": True,',
        )
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("is in no manifest", proc.stderr)

    def test_a_pin_set_read_from_the_ledger_is_rejected(self) -> None:
        """The dangerous one: 100% coverage reported from no manifest at all.

        Neither the unpinnable probe nor the synthetic row sees it -- a set
        read from `artifacts/facts` contains no impossible id, and the
        synthetic fact is not in the ledger either. What fires is that the
        manifest pins SETTLED facts, so an `open` or `refuted` id in the set
        proves it came from somewhere else.
        """
        proc = self._mutate(
            '    data = json.loads(STATEMENT_PINS.read_text())\n'
            '    return {row["fact_id"] for row in data.get("pins", []) '
            'if "fact_id" in row}',
            '    return {json.loads(p.read_text())["id"] '
            'for p in sorted(FACTS.glob("*.json"))}',
        )
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("UNSETTLED fact id", proc.stderr)

    # -- the census's own fail-closed paths ---------------------------------

    def test_an_empty_pin_manifest_is_an_error_not_a_zero(self) -> None:
        proc = self._mutate(
            "def statement_pinned_ids() -> set[str]:",
            "def statement_pinned_ids() -> set[str]:\n    return set()",
        )
        self.assertEqual(proc.returncode, 2, proc.stdout)
        self.assertIn("statement pin manifest empty", proc.stderr)

    # -- the two axes must not be merged back together ----------------------

    def test_coverage_is_excluded_from_protection_count(self) -> None:
        """A fact is not better protected because somebody else measured it.

        `exact_statement` is centrally enforced for 2121/2121 (ADR-0763).
        Folding it into `protection_count` would raise every row by one and
        make the census read as though per-fact evidence had improved.
        """
        proc = self._mutate(
            'row["protection_count"] = sum(1 for c in COLUMNS if row[c])',
            'row["protection_count"] = sum(\n'
            '        1 for c in COLUMNS + COVERAGE_COLUMNS if row[c])',
        )
        self.assertEqual(
            proc.returncode, 1,
            "merging coverage into the evidence count changed no committed "
            "artifact, so nothing in the census distinguishes the two axes: "
            f"{proc.stdout!r} {proc.stderr!r}",
        )
        self.assertIn("DRIFT", proc.stderr)


if __name__ == "__main__":
    unittest.main()
