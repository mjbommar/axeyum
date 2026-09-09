"""Controls for the drat-trim exit contract (roadmap item 0.3).

drat-trim reports SUCCESS to the shell on out-of-memory, on malformed input,
and on timeout. `references/drat-trim/drat-trim.c` has **seventeen** `exit (0)`
sites -- note the space, which is why grepping for `exit(0)` finds none of them
-- including every `c MEMOUT:` path, `:1065` ("did not find p cnf line in input
file"), and `printf ("s TIMEOUT\\n"), exit (0);` at `:905`.

So the verdict is the `s ` line and never `$?`. Two halves are pinned here:

  * `drat_trim_verdict` classifies the literal strings drat-trim emits. These
    run everywhere, with no binary.
  * `TheRealBinaryBehavesAsDocumented` runs the actual checker on three tiny
    fixtures, INCLUDING the malformed-input case that exits 0 without a
    verdict. It is skipped when `references/drat-trim/drat-trim` is absent --
    which is honest here, because the class above already fails if the
    classifier is wrong; what is skipped is only the claim about the binary.

Delete the `"s NOT VERIFIED" in stdout` arm of `drat_trim_verdict` and
`test_a_rejection_is_not_a_pass` still passes (both map to a non-`verified`
verdict), but `test_the_rejection_is_named` dies -- which is the point of
naming the verdicts rather than returning a bool.
"""

from __future__ import annotations

import importlib.util
import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_claim_certificates", ROOT / "scripts" / "check-claim-certificates.py"
)
assert SPEC and SPEC.loader
CC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CC)


def drat_trim_bin() -> pathlib.Path | None:
    """`AXEYUM_DRAT_TRIM_BIN`, else the conventional reference build path.

    Same resolution order as
    `crates/axeyum-cnf/tests/propositional_interpolant_certified.rs`, so the
    two entry points cannot disagree about which checker they measured.
    """
    override = os.environ.get("AXEYUM_DRAT_TRIM_BIN")
    if override:
        p = pathlib.Path(override)
        return p if p.is_file() else None
    p = ROOT / "references" / "drat-trim" / "drat-trim"
    return p if p.is_file() else None


DRAT_TRIM = drat_trim_bin()

# An unsatisfiable formula and a correct refutation of it, small enough to
# read. `1 2 / 1 -2 / -1 2 / -1 -2` has no model; the proof derives the unit
# `1`, then `-1`, then the empty clause.
UNSAT_CNF = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
GOOD_DRAT = "1 0\n-1 0\n0\n"
# The same proof pointed at a SATISFIABLE formula. Nothing refutes it, so a
# checker that reads the proof must refuse.
SAT_CNF = "p cnf 2 2\n1 2 0\n-1 2 0\n"
# Malformed: no `p cnf` header. drat-trim prints an ERROR line and EXITS 0.
MALFORMED_CNF = "this is not a cnf\n"


class TheVerdictComesFromTheOutputNotTheExitStatus(unittest.TestCase):
    def test_only_an_exact_s_verified_is_a_pass(self) -> None:
        self.assertEqual(CC.drat_trim_verdict("s VERIFIED\n"), "verified")
        self.assertEqual(
            CC.drat_trim_verdict(
                "c parsing input formula with 2 variables and 4 clauses\n"
                "s VERIFIED\nc verification time: 0.034 seconds\n"
            ),
            "verified",
        )

    def test_a_rejection_is_not_a_pass(self) -> None:
        for out in ("s NOT VERIFIED\n", "s TIMEOUT\n", "", "c MEMOUT: ...\n"):
            self.assertNotEqual(CC.drat_trim_verdict(out), "verified", out)

    def test_the_rejection_is_named(self) -> None:
        # A bare bool would make all four of these indistinguishable in the
        # failure message, and "the checker said no" reads very differently
        # from "the checker ran out of memory and exited 0".
        self.assertEqual(CC.drat_trim_verdict("s NOT VERIFIED\n"), "not-verified")
        self.assertEqual(CC.drat_trim_verdict("s TIMEOUT\n"), "timeout")
        self.assertEqual(
            CC.drat_trim_verdict("c ERROR: did not find p cnf line in input file\n"),
            "no-verdict",
        )
        self.assertEqual(
            CC.drat_trim_verdict("c MEMOUT: reallocation of proof list failed\n"),
            "no-verdict",
        )

    def test_s_not_verified_is_not_read_as_s_verified(self) -> None:
        # `"s NOT VERIFIED".find("s VERIFIED")` is -1, so the substring test is
        # safe here -- unlike Carcara's `valid`/`invalid` pair. Pinned because
        # the two checkers' output shapes are easy to conflate when copying the
        # discipline from one to the other.
        self.assertNotIn("s VERIFIED", "s NOT VERIFIED")


@unittest.skipUnless(
    DRAT_TRIM is not None,
    "no drat-trim binary (set AXEYUM_DRAT_TRIM_BIN, or scripts/fetch-references.sh)",
)
class TheRealBinaryBehavesAsDocumented(unittest.TestCase):
    """The end-to-end half. Measured 2026-09-09 against the 2026 build."""

    def run_drat_trim(self, cnf: str, drat: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as d:
            cnf_path = pathlib.Path(d) / "f.cnf"
            drat_path = pathlib.Path(d) / "f.drat"
            cnf_path.write_text(cnf)
            drat_path.write_text(drat)
            r = subprocess.run(
                [str(DRAT_TRIM), str(cnf_path), str(drat_path)],
                capture_output=True, text=True, timeout=120,
            )
            return r.returncode, r.stdout

    def test_a_correct_refutation_verifies(self) -> None:
        code, out = self.run_drat_trim(UNSAT_CNF, GOOD_DRAT)
        self.assertEqual(CC.drat_trim_verdict(out), "verified", out)
        self.assertEqual(code, 0)

    def test_a_refutation_of_a_satisfiable_formula_is_refused(self) -> None:
        code, out = self.run_drat_trim(SAT_CNF, GOOD_DRAT)
        self.assertEqual(CC.drat_trim_verdict(out), "not-verified", out)
        self.assertEqual(code, 1)

    def test_malformed_input_exits_zero_with_no_verdict(self) -> None:
        # THE WHOLE POINT OF ITEM 0.3. A recipe that trusted `$?` passes this.
        code, out = self.run_drat_trim(MALFORMED_CNF, GOOD_DRAT)
        self.assertEqual(code, 0, "if drat-trim now exits nonzero on malformed "
                                  "input, this control has gone vacuous; find "
                                  "another of its seventeen `exit (0)` sites")
        self.assertNotIn("s VERIFIED", out)
        self.assertEqual(CC.drat_trim_verdict(out), "no-verdict", out)

    def test_the_source_still_has_the_exit_zero_sites(self) -> None:
        # Derived from the authority, not from a number in a comment: if a new
        # drat-trim removes these, the claim above stops being true and this
        # test says so rather than the comment quietly rotting.
        assert DRAT_TRIM is not None
        src = DRAT_TRIM.parent / "drat-trim.c"
        if not src.is_file():
            self.skipTest(f"drat-trim.c not beside the binary at {DRAT_TRIM}")
        text = src.read_text(errors="replace")
        import re
        sites = re.findall(r"exit\s*\(0\)", text)
        self.assertGreaterEqual(
            len(sites), 10,
            "drat-trim used to have 17 `exit (0)` sites including MEMOUT and "
            "TIMEOUT; if that is no longer so, re-derive the exit contract",
        )
        self.assertIn('printf ("s TIMEOUT\\n"), exit (0);', text)


class TheClaimCheckerCannotPassWithoutCrossChecking(unittest.TestCase):
    """`scripts/check-claim-certificates.py --drat-checker` is one of the two
    recipes that run drat-trim (`just claims`). Both of its silent-pass shapes
    are driven here."""

    def run_checker(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["python3", str(ROOT / "scripts" / "check-claim-certificates.py"), *args],
            capture_output=True, text=True, timeout=900, cwd=ROOT,
        )

    def test_a_nonexistent_drat_checker_is_an_error_not_a_silent_skip(self) -> None:
        r = self.run_checker("--drat-checker", "/nonexistent/drat-trim",
                             "--only", "rado-r4-a4-b3")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("not an executable file", r.stderr)

    def test_a_run_that_cross_checked_nothing_fails(self) -> None:
        # `rado-r4-a4-b3` carries four evidence rows and NONE of them reaches
        # the external branch (one has no stored artifact, three are
        # `replay-only`). Before the count existed this exited 0 having
        # invoked the checker zero times -- a `--drat-checker` run that
        # established nothing and said so nowhere.
        r = self.run_checker("--drat-checker", "/bin/true",
                             "--only", "rado-r4-a4-b3")
        self.assertIn("external DRAT cross-checks run: 0", r.stdout)
        self.assertNotEqual(r.returncode, 0, r.stdout[-2000:])
        self.assertIn("ran ZERO", r.stderr)


if __name__ == "__main__":
    unittest.main()
