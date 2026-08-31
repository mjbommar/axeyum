#!/usr/bin/env python3
"""Controls for the bucket-cohesion guards in
`scripts/measure-curriculum-kernel-coverage.py` (ADR-1215).

WHAT THESE ARE FOR. The classifier attributes every kernel declaration to a
curriculum node by an ordered NAME pattern table whose last entries
(`naturals` / `integers` / `rationals` / `reals` / `complex`) are catch-alls.
A declaration attributed to NOTHING is caught by the residual counter; a
declaration attributed to the WRONG bucket is not, because it is attributed,
counted, and plausible. That happened twice in two days:

- ADR-1140: `linear-algebra`'s pattern named the instances `det2|det3`, so
  ADR-1120's general-`n` determinant fell into `rationals`.
- ADR-1205: `number-theory`'s only Gauss alternative was the instance
  `gauss_fold_injective`, so the whole ADR-1130/ADR-1150 quadratic-residue
  family fell into `naturals`/`integers`.

The two RED cases below reconstruct exactly those two pattern tables, from
`git show`n history, against a slice of the REAL projection -- not a synthetic
fixture -- and require the guard to fire and to NAME the affected
declarations. `test_current_table_is_green_on_the_same_slice` is the control
that makes each RED case mean something: the same slice, the same guard, the
shipped table, no findings.

The fixture is `scripts/tests/fixtures/curriculum-projection-slice.tsv`, the
124 real `Rat.det*` / `Rat.mat*` / `Nat.gauss*` / `Int.gauss*` /
`*.leastResidue*` rows the two incidents concern, cut from a
`kernel_declaration_projection` run on 2026-08-31.

Note these tests deliberately call `assign` / `stem_groups` /
`cohesion_findings` rather than `main`: `parse_rows`'s `PROJECTION_FLOOR`
refuses a short input, which is correct for the gate and would make every
fixture here unusable.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "scripts/tests/fixtures/curriculum-projection-slice.tsv"

_spec = importlib.util.spec_from_file_location(
    "measure_curriculum_kernel_coverage",
    ROOT / "scripts/measure-curriculum-kernel-coverage.py")
mck = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(mck)


# The `linear-algebra` row exactly as it stood at `d2bb38a1e^`, before
# ADR-1140 widened `det2|det3` to bare `det` and added the `mat(Skip|Minor|
# Inv2)` / `altSign` / `sumRange_matSkip` alternatives.
PRE_1140_LINEAR_ALGEBRA = (
    r"^Rat\.(det2|det3|dotN|mat(Id|Mul|Transpose)|cramer|inv2_|mul_adj2_)")

# The `number-theory` row exactly as it stood at `bd382566b^`, before
# ADR-1205 added `gauss[A-Z]` / `gauss_neg_count` / `gauss_fold_` /
# `gauss_residue` / `leastResidue` / `secondSupplementaryLaw` /
# `is_quadratic_residue` / `pow_neg_one_of` / `half_ceil_parity`.
PRE_1205_NUMBER_THEORY = (
    r"^(Nat|Int)\.(prime|Prime|totient|fib|Fib|fastFib|perfect|Perfect|"
    r"Squarefree|squarefree|wilson|Wilson|euler|Euler|"
    r"sumOfDivisors|sumDivisors|sigma|nth|minFac|factorization|"
    r"legendre|quadratic|sum_two_squares|"
    r"exists_prime|pow_prime|not_prime|succ_pred_prime|"
    r"dvd_of_forall_prime|coprime_fermatNumber|least_divisor|least_residue|"
    r"pow_mul_prime|pow_two_ne_pow_two_mul_prime|pow_of_pow_add_prime|"
    r"self_inverse_mod_prime|factorial_interior_modeq|factorial_sq_modeq|"
    r"add_pow_modeq_prime|gauss_fold_injective)")


def read_fixture() -> dict[str, tuple[str, str]]:
    rows: dict[str, tuple[str, str]] = {}
    for line in FIXTURE.read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if len(fields) < 3:
            continue
        rows.setdefault(fields[2], (fields[0], fields[1]))
    return rows


def with_pattern(node_id: str, pattern: str) -> list[tuple[str, str]]:
    """The shipped table with ONE node's pattern replaced."""
    replaced = [(nid, pattern if nid == node_id else pat)
                for nid, pat in mck.BUCKETS]
    assert any(nid == node_id for nid, _ in replaced), node_id
    return replaced


def findings_for(buckets, rows, splits=None, families=None) -> list[str]:
    groups = mck.stem_groups(mck.assign(rows, buckets))
    if splits is None or families is None:
        # Pin taken from the SHIPPED table on the same rows: what a correct
        # tree records, which is what a regression has to disagree with.
        shipped = mck.stem_groups(mck.assign(rows, mck.BUCKETS))
        splits = {k: tuple(sorted(v)) for k, v in shipped.items()
                  if len(v) > 1}
        families = {}
        for k, v in shipped.items():
            if len(v) == 1:
                node = next(iter(v))
                if node in mck.CATCHALL_NODES and len(v[node]) >= mck.FAMILY_FLOOR:
                    families[k] = node
    return mck.cohesion_findings(groups, splits, families)


class FixtureTests(unittest.TestCase):
    def test_fixture_is_real_and_nonempty(self):
        rows = read_fixture()
        self.assertGreater(len(rows), 100, "fixture truncated")
        # A positive control on the fixture's own content: if these names ever
        # stop being present the two RED cases below would go green for a
        # reason that has nothing to do with the guard.
        for name in ("Rat.det", "Rat.det2", "Rat.matSkip",
                     "Nat.gaussFold", "Nat.leastResidue"):
            self.assertIn(name, rows, f"{name} absent from the fixture")


class Adr1140Tests(unittest.TestCase):
    """The general-`n` determinant falling into `rationals`."""

    def test_red(self):
        rows = read_fixture()
        findings = findings_for(
            with_pattern("linear-algebra", PRE_1140_LINEAR_ALGEBRA), rows)
        self.assertTrue(findings, "the pre-ADR-1140 table produced NO finding")
        blob = "\n".join(findings)
        self.assertIn("Rat.det", blob)
        self.assertIn("rationals", blob)
        self.assertIn("linear-algebra", blob)
        # It must name declarations, not merely a count.
        self.assertIn("Rat.det_", blob)

    def test_the_mis_attributed_declarations_are_the_ones_adr_1140_names(self):
        rows = read_fixture()
        broken = mck.assign(rows, with_pattern("linear-algebra",
                                               PRE_1140_LINEAR_ALGEBRA))
        moved = sorted(n for n, node in broken.items()
                       if node == "rationals"
                       and mck.assign(rows, mck.BUCKETS).get(n)
                       == "linear-algebra")
        self.assertGreaterEqual(
            len(moved), 20,
            f"ADR-1140 measured 22 mis-attributed; found {len(moved)}: {moved}")
        self.assertIn("Rat.det", moved)
        self.assertIn("Rat.sumRange_matSkip", moved)


class Adr1205Tests(unittest.TestCase):
    """The quadratic-residue family falling into `naturals`/`integers`."""

    def test_red(self):
        rows = read_fixture()
        findings = findings_for(
            with_pattern("number-theory", PRE_1205_NUMBER_THEORY), rows)
        self.assertTrue(findings, "the pre-ADR-1205 table produced NO finding")
        blob = "\n".join(findings)
        self.assertIn("gauss", blob)
        self.assertIn("number-theory", blob)
        self.assertTrue("naturals" in blob or "integers" in blob, blob)

    def test_the_mis_attributed_declarations_are_the_ones_adr_1205_names(self):
        rows = read_fixture()
        good = mck.assign(rows, mck.BUCKETS)
        broken = mck.assign(rows, with_pattern("number-theory",
                                               PRE_1205_NUMBER_THEORY))
        moved = sorted(n for n, node in broken.items()
                       if node in mck.CATCHALL_NODES
                       and good.get(n) == "number-theory")
        self.assertGreaterEqual(
            len(moved), 25,
            f"ADR-1205 measured 29-32 mis-attributed; found {len(moved)}")
        self.assertIn("Nat.gaussFold", moved)
        self.assertIn("Nat.leastResidue", moved)


class ControlTests(unittest.TestCase):
    def test_current_table_is_green_on_the_same_slice(self):
        """The control both RED cases depend on. Without it, a guard that
        fires on EVERYTHING would pass the two tests above."""
        rows = read_fixture()
        self.assertEqual([], findings_for(mck.BUCKETS, rows))

    def test_growth_inside_a_pinned_split_does_not_fire(self):
        """The false-positive bound. Adding declarations to nodes a stem
        already occupies must be free, or ordinary work reddens the gate and
        the guard is disabled within a week."""
        rows = read_fixture()
        shipped = mck.stem_groups(mck.assign(rows, mck.BUCKETS))
        splits = {k: tuple(sorted(v)) for k, v in shipped.items() if len(v) > 1}
        families = {k: next(iter(v)) for k, v in shipped.items()
                    if len(v) == 1 and next(iter(v)) in mck.CATCHALL_NODES
                    and len(v[next(iter(v))]) >= mck.FAMILY_FLOOR}
        grown = dict(rows)
        grown["Rat.det_of_something_new"] = ("rat", "theorem")
        grown["Nat.gauss_fold_new_corollary"] = ("nat", "theorem")
        grown["Nat.gaussNewLemma"] = ("nat", "theorem")
        self.assertEqual(
            [], findings_for(mck.BUCKETS, grown, splits, families))

    def test_a_new_split_fires(self):
        """G1's own control: a stem that gains a node it did not have."""
        rows = {"Rat.det": ("rat", "definition"),
                "Rat.det_zero": ("rat", "theorem")}
        buckets = [("linear-algebra", r"^Rat\.det$"), ("rationals", r"^Rat\.")]
        findings = mck.cohesion_findings(
            mck.stem_groups(mck.assign(rows, buckets)), {}, {})
        self.assertEqual(1, len(findings), findings)
        self.assertIn("G1 SPLIT", findings[0])

    def test_a_new_pure_catchall_family_fires(self):
        """G2's own control: the case G1 structurally cannot see -- a family
        with NO partial match, so it never splits."""
        rows = {f"Nat.widget_{i}": ("nat", "theorem")
                for i in range(mck.FAMILY_FLOOR)}
        buckets = [("naturals", r"^Nat\.")]
        findings = mck.cohesion_findings(
            mck.stem_groups(mck.assign(rows, buckets)), {}, {})
        self.assertEqual(1, len(findings), findings)
        self.assertIn("G2 FAMILY", findings[0])

    def test_below_the_family_floor_does_not_fire(self):
        """The false-positive bound on G2, with the sizes written OUT rather
        than derived from `FAMILY_FLOOR`. A test that reads the constant it is
        testing adapts to any value and measures nothing -- the floor could be
        moved to 1, reddening every one-declaration family in a carrier
        bucket, and this would still pass."""
        buckets = [("naturals", r"^Nat\.")]

        def findings(n):
            rows = {f"Nat.widget_{i}": ("nat", "theorem") for i in range(n)}
            return mck.cohesion_findings(
                mck.stem_groups(mck.assign(rows, buckets)), {}, {})

        self.assertEqual(8, mck.FAMILY_FLOOR,
                         "the sizes below are written for a floor of 8")
        for n in (1, 2, 3, 7):
            self.assertEqual([], findings(n), f"{n} declarations fired G2")
        self.assertEqual(1, len(findings(8)), "8 declarations did NOT fire G2")

    def test_a_stale_split_pin_fires(self):
        """G3's own control: without it the pin rots into a list of things
        that used to be true and G1/G2 weaken with nothing reporting it.
        Split and family halves are separate tests deliberately -- two
        mutations naming ONE dead test cannot tell you both halves are
        covered."""
        findings = mck.cohesion_findings(
            {}, {("Rat", "gone"): ("linear-algebra", "rationals")}, {})
        self.assertEqual(1, len(findings), findings)
        self.assertIn("G3 STALE split pin", findings[0])

    def test_a_stale_family_pin_fires(self):
        findings = mck.cohesion_findings(
            {}, {}, {("Nat", "vanished"): "naturals"})
        self.assertEqual(1, len(findings), findings)
        self.assertIn("G3 STALE family pin", findings[0])

    def test_stem_folds_camelcase_into_the_snake_case_family(self):
        """`Nat.gaussFold` and `Nat.gauss_neg_count_succ` are ONE family. This
        kernel spells a single mathematical family both ways -- measured over
        447 `CReal` names, 315 carry an underscore and 225 an internal
        capital -- so a guard keyed on the raw spelling sees two families and
        compares neither, and ADR-1205 never fires."""
        self.assertEqual(("Nat", "gauss"), mck.name_stem("Nat.gaussFold"))
        self.assertEqual(("Nat", "gauss"),
                         mck.name_stem("Nat.gauss_neg_count_succ"))
        self.assertEqual(("Nat", "gauss"),
                         mck.name_stem("Nat.gaussLemmaSignCount"))

    def test_stem_strips_trailing_digits(self):
        """`det2`, `det3` and `det` are ONE family, or ADR-1140's exact shape
        -- a pattern naming the NUMBERED instances while the general
        construction grows past them -- never produces a split at all."""
        self.assertEqual(("Rat", "det"), mck.name_stem("Rat.det2"))
        self.assertEqual(("Rat", "det"), mck.name_stem("Rat.det3"))
        self.assertEqual(("Rat", "det"), mck.name_stem("Rat.det"))
        self.assertEqual(("Rat", "det"), mck.name_stem("Rat.det_eq_det2"))


class PinRoundTripTests(unittest.TestCase):
    def test_render_then_read_is_a_fixed_point(self):
        rows = read_fixture()
        groups = mck.stem_groups(mck.assign(rows, mck.BUCKETS))
        import tempfile, os
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "pin.tsv")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(mck.render_pin(groups))
            splits, families = mck.read_pin(path)
            self.assertEqual([], mck.cohesion_findings(groups, splits, families))

    def test_committed_pin_parses_and_is_nonempty(self):
        splits, families = mck.read_pin(
            str(ROOT / mck.DEFAULT_PIN))
        self.assertGreater(len(splits) + len(families), 40,
                           "the committed pin is empty or truncated -- the "
                           "guards would then report every real family")

    def test_missing_pin_reads_as_empty_not_as_error(self):
        splits, families = mck.read_pin("/nonexistent/pin.tsv")
        self.assertEqual(({}, {}), (splits, families))


class ProjectionInputTests(unittest.TestCase):
    """The guards are only as good as the projection they read. A SHORT index
    makes a newly-landed family look like it was always in the catch-all --
    the same failure the guards exist to catch, arriving through the input."""

    def _run(self, *args):
        import subprocess
        return subprocess.run(
            ["python3", str(ROOT / "scripts/measure-curriculum-kernel-coverage.py"),
             *args],
            capture_output=True, text=True, cwd=ROOT, check=False)

    def test_a_short_projection_is_refused(self):
        proc = self._run(str(FIXTURE))
        self.assertNotEqual(0, proc.returncode,
                            "a 124-row projection was accepted as the authority")
        self.assertIn("STALE or truncated", proc.stdout + proc.stderr)

    def test_require_pin_refuses_a_missing_pin(self):
        proc = self._run(str(FIXTURE), "--require-pin",
                         "--cohesion-pin", "/nonexistent/pin.tsv")
        self.assertNotEqual(0, proc.returncode)
        # Assert the REASON. Without this the test passes on the projection
        # floor's refusal instead, and `--require-pin` is never exercised.
        self.assertIn("--require-pin", proc.stdout + proc.stderr)
        self.assertNotIn("STALE or truncated", proc.stdout + proc.stderr)

    def test_the_script_still_runs_and_prints_a_table(self):
        """Positive control for the two refusals above: without it, a script
        that refused EVERYTHING would pass them both."""
        proc = self._run("--help")
        self.assertEqual(0, proc.returncode, proc.stderr)
        self.assertIn("--cohesion-pin", proc.stdout)


class RunProjectionTests(unittest.TestCase):
    """`--run-projection` is what `scripts/check.sh` registers, so its failure
    modes have to be exercised somewhere that is not the gate itself."""

    def _fake_cargo(self, body: str) -> str:
        import os, stat, tempfile
        d = tempfile.mkdtemp()
        path = os.path.join(d, "cargo")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("#!/bin/sh\n" + body)
        os.chmod(path, os.stat(path).st_mode | stat.S_IEXEC)
        self.addCleanup(lambda: __import__("shutil").rmtree(d, ignore_errors=True))
        return path

    def test_it_passes_release_and_returns_stdout(self):
        cargo = self._fake_cargo(
            'printf \'%s\\n\' "$*" > "$0.args"\n'
            'printf "nat\\ttheorem\\tNat.probe\\n"\n')
        out = mck.run_projection(cargo)
        self.assertIn("Nat.probe", out)
        with open(cargo + ".args", encoding="utf-8") as fh:
            args = fh.read()
        # `--release` is MANDATORY: in debug this example SIGABRTs on a stack
        # overflow, which reads as a broken tool rather than a finding.
        self.assertIn("--release", args)
        self.assertIn("kernel_declaration_projection", args)

    def test_a_failing_tool_is_not_reported_as_a_finding(self):
        cargo = self._fake_cargo("echo boom >&2\nexit 101\n")
        with self.assertRaises(SystemExit) as caught:
            mck.run_projection(cargo)
        self.assertIn("the tool itself failed", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
