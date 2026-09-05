"""Tests for `scripts/check-shape-duplicates.py`.

Two parts:

1. Ordinary unit tests of the pure parsing/comparison functions, plus
   end-to-end `main()` tests over synthetic fixtures (no cargo build
   needed -- `--duplicates-file` reads canned `shape_search --duplicates`
   text).

2. A self-contained mutation loop (`MutationTests`) that copies the
   script's source into a scratch temp directory, applies ONE textual
   mutation at a time (each disables exactly one guard), and asserts the
   guard's own test now FAILS against the mutant while it PASSES against
   the unmutated baseline. A guard nobody can remove is decoration
   (CLAUDE.md); this is that check, run automatically rather than by hand.

   Every mutant is invoked as `python3 -B <mutant>.py ...` in a fresh
   subprocess. `-B` disables bytecode caching entirely, which sidesteps
   this repository's documented stale-`.pyc` mutation hazard (Python
   caches compiled modules on `(mtime-in-whole-seconds, size)`, and
   same-size mutants written back-to-back can collide within one second)
   without needing to track file sizes or clear `__pycache__` by hand.
"""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

# Overridable so the mutation loop below can point a freshly-spawned
# subprocess at a mutated copy of the script instead of the real one.
SCRIPT = Path(
    os.environ.get(
        "CHECK_SHAPE_DUPLICATES_SCRIPT", str(Path(__file__).parents[1] / "check-shape-duplicates.py")
    )
)
SPEC = importlib.util.spec_from_file_location("check_shape_duplicates", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


REAL_FIXTURE = """\
coverage: groups=[logic,nat,axreal,integer,rat,characterization,string,creal,complex,cpoint] declarations=1845 values_indexed=false build=12.9s
control: axiom=30 definition=282 theorem=1457 opaque=0 inductive=23 constructor=30 recursor=23 quot=0
DUPLICATE  Int.lt  Int.Characterization.zero_lt_one Int.zero_lt_one
DUPLICATE  Rat -> Rat -> Rat -> Nat -> Nat -> Rat.IsDistribution -> Rat.PairwiseUncorrelated -> Rat.lt -> Rat.le  Rat.chebyshev_sampleMean_uncorrelated Rat.weak_law_of_large_numbers
DUPLICATE  CPoint -> CPoint -> CPoint -> CReal.Equiv  CPoint.apollonius_from_stewart CPoint.apollonius_median
DUPLICATE  CReal -> Nat -> CReal.le  CReal.rat_approx_upper CReal.sampleUpperBound
DUPLICATE  CReal -> Nat -> CReal.le  CReal.rat_approx_lower CReal.sampleLowerBound
DUPLICATE  Int -> Int -> Or  Int.Characterization.le_total Int.le_total
DUPLICATE  Int -> Not  Int.Characterization.discrete Int.no_int_between
DUPLICATE  Nat -> Nat -> Eq  Nat.succ_sub_succ Nat.succ_sub_succ_eq_sub
DUPLICATE  Nat -> Nat -> Eq -> Eq  Nat.Peano.succ_injective Nat.succ_injective
DUPLICATE  Nat -> Nat -> Nat.le -> Nat.le  Nat.le_succ_succ Nat.succ_le_succ
verdict: DUPLICATE-GROUPS 10
"""

REAL_ALLOWLIST = [
    {"names": ["Int.Characterization.zero_lt_one", "Int.zero_lt_one"], "reason": "alias"},
    {
        "names": ["Rat.chebyshev_sampleMean_uncorrelated", "Rat.weak_law_of_large_numbers"],
        "reason": "alias",
    },
    {"names": ["CPoint.apollonius_from_stewart", "CPoint.apollonius_median"], "reason": "cross-check"},
    {"names": ["CReal.rat_approx_upper", "CReal.sampleUpperBound"], "reason": "alias"},
    {"names": ["CReal.rat_approx_lower", "CReal.sampleLowerBound"], "reason": "alias"},
    {"names": ["Int.Characterization.le_total", "Int.le_total"], "reason": "alias"},
    {"names": ["Int.Characterization.discrete", "Int.no_int_between"], "reason": "alias"},
    {"names": ["Nat.succ_sub_succ", "Nat.succ_sub_succ_eq_sub"], "reason": "alias"},
    {"names": ["Nat.Peano.succ_injective", "Nat.succ_injective"], "reason": "alias"},
    {"names": ["Nat.le_succ_succ", "Nat.succ_le_succ"], "reason": "alias"},
]


def write(path: Path, text: str) -> None:
    path.write_text(text)


class ParseDuplicatesTests(unittest.TestCase):
    def test_parses_the_real_fixture_into_ten_groups(self):
        groups = MODULE.parse_duplicates(REAL_FIXTURE)
        self.assertEqual(len(groups), 10)
        shapes = {shape for shape, _ in groups}
        self.assertIn("Int.lt", shapes)
        names = {names for _, names in groups}
        self.assertIn(frozenset({"Int.Characterization.zero_lt_one", "Int.zero_lt_one"}), names)

    def test_ignores_non_duplicate_lines(self):
        text = "coverage: something\nDUPLICATE  A -> B  X Y\nverdict: DUPLICATE-GROUPS 1\n"
        groups = MODULE.parse_duplicates(text)
        self.assertEqual(groups, [("A -> B", frozenset({"X", "Y"}))])

    def test_malformed_line_missing_a_column_raises(self):
        # Only one double-space separator -- the names column is missing.
        text = "DUPLICATE  A -> B\n"
        with self.assertRaises(MODULE.DuplicatesFormatError):
            MODULE.parse_duplicates(text)

    def test_line_with_fewer_than_two_names_raises(self):
        text = "DUPLICATE  A -> B  OnlyOneName\n"
        with self.assertRaises(MODULE.DuplicatesFormatError):
            MODULE.parse_duplicates(text)

    def test_three_way_group_is_parsed_as_one_group_of_three(self):
        text = "DUPLICATE  A -> B  X Y Z\n"
        groups = MODULE.parse_duplicates(text)
        self.assertEqual(groups, [("A -> B", frozenset({"X", "Y", "Z"}))])


class ParseVerdictCountTests(unittest.TestCase):
    def test_reads_the_verdict_line(self):
        self.assertEqual(MODULE.parse_verdict_count(REAL_FIXTURE), 10)

    def test_absent_verdict_line_is_none(self):
        self.assertIsNone(MODULE.parse_verdict_count("DUPLICATE  A -> B  X Y\n"))


class ParseCoverageLineTests(unittest.TestCase):
    """`parse_coverage_line` -- the ADR-1634 forwarding hook that lets
    `check-merge-hygiene.sh` read the live declaration count from this
    script's own stdout instead of re-running `shape_search`."""

    def test_reads_the_coverage_line_from_the_real_fixture(self):
        line = MODULE.parse_coverage_line(REAL_FIXTURE)
        self.assertIsNotNone(line)
        self.assertTrue(line.startswith("coverage: "))
        self.assertIn("declarations=1845", line)

    def test_absent_coverage_line_is_none(self):
        self.assertIsNone(MODULE.parse_coverage_line("DUPLICATE  A -> B  X Y\n"))


class LoadAllowlistTests(unittest.TestCase):
    def test_loads_a_valid_allowlist(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "allow.json"
            write(p, json.dumps(REAL_ALLOWLIST))
            allowed = MODULE.load_allowlist(p)
            self.assertEqual(len(allowed), 10)
            self.assertIn(frozenset({"Int.Characterization.zero_lt_one", "Int.zero_lt_one"}), allowed)

    def test_top_level_must_be_a_list(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "allow.json"
            write(p, json.dumps({"not": "a list"}))
            with self.assertRaises(MODULE.AllowlistError):
                MODULE.load_allowlist(p)

    def test_entry_missing_reason_raises(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "allow.json"
            write(p, json.dumps([{"names": ["A", "B"]}]))
            with self.assertRaises(MODULE.AllowlistError):
                MODULE.load_allowlist(p)

    def test_entry_with_empty_reason_raises(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "allow.json"
            write(p, json.dumps([{"names": ["A", "B"], "reason": "   "}]))
            with self.assertRaises(MODULE.AllowlistError):
                MODULE.load_allowlist(p)

    def test_entry_with_one_name_raises(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "allow.json"
            write(p, json.dumps([{"names": ["OnlyOne"], "reason": "x"}]))
            with self.assertRaises(MODULE.AllowlistError):
                MODULE.load_allowlist(p)

    def test_duplicate_entries_for_the_same_group_raise(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "allow.json"
            write(
                p,
                json.dumps(
                    [
                        {"names": ["A", "B"], "reason": "x"},
                        {"names": ["B", "A"], "reason": "y"},
                    ]
                ),
            )
            with self.assertRaises(MODULE.AllowlistError):
                MODULE.load_allowlist(p)

    def test_the_committed_allowlist_is_itself_valid(self):
        # The actual file this gate ships with must load cleanly.
        #
        # This used to pin the length at exactly 10, and that pin measured
        # nothing the gate does not already measure: `check-shape-duplicates`
        # FAILS on any reported group missing from this file and on any entry
        # here no longer reported, so the list cannot grow silently -- every
        # addition is a group someone had to read and write a reason for. What
        # the exact number DID do was make a legitimate adjudication fail an
        # unrelated control (it went 10 -> 15 the first time the gate was ever
        # run automatically, 2026-08-31, ADR-1170), which is the maintenance
        # shape CLAUDE.md's pinned-inventory entry warns about.
        #
        # Replaced with a floor -- so an emptied or truncated file cannot pass
        # -- plus the per-entry structure the count never checked. `source`
        # and `adjudicated` are what separate a record from a rubber stamp:
        # `load_allowlist` requires only `reason`, so without these two lines
        # nothing anywhere requires an entry to say WHEN it was read or WHERE
        # the reading is written down.
        allowed = MODULE.load_allowlist(MODULE.DEFAULT_ALLOWLIST)
        self.assertGreaterEqual(len(allowed), 10)
        for names, entry in allowed.items():
            self.assertTrue(entry["reason"].strip(), sorted(names))
            self.assertTrue(str(entry.get("source", "")).strip(), sorted(names))
            self.assertTrue(str(entry.get("adjudicated", "")).strip(), sorted(names))


class EvaluateTests(unittest.TestCase):
    def test_matching_sets_report_nothing(self):
        reported = [("Shape", frozenset({"A", "B"}))]
        allowed = {frozenset({"A", "B"}): {"reason": "x"}}
        unrecognized, stale = MODULE.evaluate(reported, allowed)
        self.assertEqual(unrecognized, [])
        self.assertEqual(stale, [])

    def test_a_reported_group_absent_from_the_allowlist_is_unrecognized(self):
        reported = [("Shape", frozenset({"A", "B"}))]
        unrecognized, stale = MODULE.evaluate(reported, {})
        self.assertEqual(unrecognized, [("Shape", frozenset({"A", "B"}))])
        self.assertEqual(stale, [])

    def test_an_allowlist_entry_absent_from_the_report_is_stale(self):
        allowed = {frozenset({"A", "B"}): {"reason": "x"}}
        unrecognized, stale = MODULE.evaluate([], allowed)
        self.assertEqual(unrecognized, [])
        self.assertEqual([names for names, _ in stale], [frozenset({"A", "B"})])

    def test_a_group_gaining_a_third_member_is_unrecognized_not_matched(self):
        # Extending an existing pair to a triple changes its identity: the
        # allowlist entry for the pair must NOT silently cover the triple.
        reported = [("Shape", frozenset({"A", "B", "C"}))]
        allowed = {frozenset({"A", "B"}): {"reason": "x"}}
        unrecognized, stale = MODULE.evaluate(reported, allowed)
        self.assertEqual(unrecognized, [("Shape", frozenset({"A", "B", "C"}))])
        self.assertEqual([names for names, _ in stale], [frozenset({"A", "B"})])


class MainEndToEndTests(unittest.TestCase):
    def run_main(self, dup_text: str, allowlist) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory() as d:
            dup_path = Path(d) / "dups.txt"
            allow_path = Path(d) / "allow.json"
            write(dup_path, dup_text)
            write(allow_path, json.dumps(allowlist))
            proc = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPT),
                    "--duplicates-file",
                    str(dup_path),
                    "--allowlist",
                    str(allow_path),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )
            return proc.returncode, proc.stdout, proc.stderr

    def test_matching_allowlist_exits_zero(self):
        code, out, _err = self.run_main(REAL_FIXTURE, REAL_ALLOWLIST)
        self.assertEqual(code, 0, out)
        self.assertIn("OK: 10", out)

    def test_coverage_line_is_forwarded_on_success(self):
        """ADR-1634: `check-merge-hygiene.sh` reads the live declaration count
        from THIS script's stdout rather than re-running `shape_search`."""
        code, out, _err = self.run_main(REAL_FIXTURE, REAL_ALLOWLIST)
        self.assertEqual(code, 0, out)
        self.assertIn("coverage: ", out)
        self.assertIn("declarations=1845", out)

    def test_coverage_line_is_forwarded_even_on_failure(self):
        """The forwarding happens before the pass/fail verdict, so a caller
        reading the live count does not need the duplicates check to pass."""
        extra = REAL_FIXTURE.replace(
            "verdict: DUPLICATE-GROUPS 10", "DUPLICATE  Foo -> Bar  New.One New.Two\nverdict: DUPLICATE-GROUPS 11"
        )
        code, out, _err = self.run_main(extra, REAL_ALLOWLIST)
        self.assertEqual(code, 1)
        self.assertIn("declarations=1845", out)

    def test_new_duplicate_exits_one(self):
        extra = REAL_FIXTURE.replace(
            "verdict: DUPLICATE-GROUPS 10", "DUPLICATE  Foo -> Bar  New.One New.Two\nverdict: DUPLICATE-GROUPS 11"
        )
        code, _out, err = self.run_main(extra, REAL_ALLOWLIST)
        self.assertEqual(code, 1)
        self.assertIn("NEW/UNADJUDICATED", err)
        self.assertIn("New.One", err)

    def test_stale_allowlist_entry_exits_one(self):
        allowlist = REAL_ALLOWLIST + [{"names": ["Gone.One", "Gone.Two"], "reason": "no longer real"}]
        code, _out, err = self.run_main(REAL_FIXTURE, allowlist)
        self.assertEqual(code, 1)
        self.assertIn("STALE", err)
        self.assertIn("Gone.One", err)

    def test_malformed_allowlist_exits_two(self):
        code, _out, err = self.run_main(REAL_FIXTURE, [{"names": ["A", "B"]}])
        self.assertEqual(code, 2)
        self.assertIn("reason", err)

    def test_verdict_count_mismatch_exits_two(self):
        wrong = REAL_FIXTURE.replace("verdict: DUPLICATE-GROUPS 10", "verdict: DUPLICATE-GROUPS 99")
        code, _out, err = self.run_main(wrong, REAL_ALLOWLIST)
        self.assertEqual(code, 2)
        self.assertIn("verdict", err.lower())


# --- Mutation loop: each guard's own test must fail against a mutant that
# disables it, and pass against the baseline. ---------------------------

GUARDS: list[tuple[str, str, str]] = [
    (
        "malformed-line-column-count",
        "if len(parts) != 3:",
        "if False:  # MUTATED malformed-line-column-count",
    ),
    (
        "fewer-than-two-names",
        "if len(names) < 2:",
        "if False:  # MUTATED fewer-than-two-names",
    ),
    (
        "allowlist-empty-reason",
        'if not isinstance(reason, str) or not reason.strip():',
        "if False:  # MUTATED allowlist-empty-reason",
    ),
    (
        "allowlist-bad-names-shape",
        "if not isinstance(names, list) or len(names) < 2 or not all(isinstance(n, str) for n in names):",
        "if False:  # MUTATED allowlist-bad-names-shape",
    ),
    (
        "allowlist-duplicate-entry",
        "if key in out:",
        "if False:  # MUTATED allowlist-duplicate-entry",
    ),
    (
        "unrecognized-detection",
        "unrecognized = [(shape, names) for shape, names in reported if names not in allowed]",
        "unrecognized = []  # MUTATED unrecognized-detection",
    ),
    (
        "stale-detection",
        "stale = [(names, entry) for names, entry in allowed.items() if names not in reported_keys]",
        "stale = []  # MUTATED stale-detection",
    ),
    (
        "verdict-count-mismatch",
        "if verdict_count is not None and verdict_count != len(reported):",
        "if False:  # MUTATED verdict-count-mismatch",
    ),
]

# Which test in this module is the one specific to each guard (run by name
# via unittest's dotted test id, one process per invocation).
# NOT `__name__`: it is invocation-dependent -- `test_check_shape_duplicates`
# under `-m unittest` from this directory, `scripts.tests.test_check_shape_duplicates`
# by dotted path from the repo root, `__main__` when run as a script. `run_one_test`
# always spawns its subprocess with `cwd=scripts/tests`, so only the bare module name
# resolves there, and using `__name__` made this suite pass under exactly ONE
# invocation and fail under the other two -- a gate on one working directory.
# Caught by the baseline assertion in `test_every_guard_is_killed_by_its_own_mutation`,
# which refuses to score mutants against a failing baseline.
_MODULE = "test_check_shape_duplicates"

GUARD_TEST_IDS: dict[str, str] = {
    "malformed-line-column-count": f"{_MODULE}.ParseDuplicatesTests.test_malformed_line_missing_a_column_raises",
    "fewer-than-two-names": f"{_MODULE}.ParseDuplicatesTests.test_line_with_fewer_than_two_names_raises",
    "allowlist-empty-reason": f"{_MODULE}.LoadAllowlistTests.test_entry_with_empty_reason_raises",
    "allowlist-bad-names-shape": f"{_MODULE}.LoadAllowlistTests.test_entry_with_one_name_raises",
    "allowlist-duplicate-entry": f"{_MODULE}.LoadAllowlistTests.test_duplicate_entries_for_the_same_group_raise",
    "unrecognized-detection": f"{_MODULE}.MainEndToEndTests.test_new_duplicate_exits_one",
    "stale-detection": f"{_MODULE}.MainEndToEndTests.test_stale_allowlist_entry_exits_one",
    "verdict-count-mismatch": f"{_MODULE}.MainEndToEndTests.test_verdict_count_mismatch_exits_two",
}


def run_one_test(script_path: Path, test_id: str) -> bool:
    """Run exactly one test id against `script_path` as SCRIPT. Returns True
    if that test PASSED.

    Reruns this same test file as a subprocess with an environment variable
    pointing at the (possibly mutated) script, so the mutant is loaded fresh
    in its own interpreter -- `-B` disables bytecode caching, so there is no
    stale-`.pyc` risk even though mutants are written back-to-back with
    identical sizes.
    """
    env = dict(os.environ)
    env["CHECK_SHAPE_DUPLICATES_SCRIPT"] = str(script_path)
    proc = subprocess.run(
        [sys.executable, "-B", "-m", "unittest", test_id],
        cwd=str(Path(__file__).parent),
        capture_output=True,
        text=True,
        timeout=60,
        env=env,
    )
    return proc.returncode == 0


class MutationTests(unittest.TestCase):
    """Each guard, deleted one at a time in a scratch copy, must kill its
    own test while every other guard's baseline test still passes."""

    def test_every_guard_is_killed_by_its_own_mutation(self):
        baseline_ok = run_one_test(SCRIPT, GUARD_TEST_IDS["unrecognized-detection"])
        self.assertTrue(baseline_ok, "baseline (unmutated) run must pass before trusting any mutant result")

        results = {}
        with tempfile.TemporaryDirectory() as d:
            source = SCRIPT.read_text()
            for guard_name, anchor, replacement in GUARDS:
                occurrences = source.count(anchor)
                self.assertEqual(
                    occurrences,
                    1,
                    f"guard anchor for {guard_name!r} must match exactly once in the "
                    f"source, found {occurrences} -- anchor text has drifted from the "
                    "script, update GUARDS",
                )
                mutant_text = source.replace(anchor, replacement, 1)
                mutant_path = Path(d) / f"mutant-{guard_name}.py"
                mutant_path.write_text(mutant_text)

                test_id = GUARD_TEST_IDS[guard_name]
                mutant_passed = run_one_test(mutant_path, test_id)
                results[guard_name] = mutant_passed

        survived = [name for name, passed in results.items() if passed]
        self.assertEqual(
            survived,
            [],
            f"these guards SURVIVED their own mutation (test still passed with the "
            f"guard disabled -- decoration, not a check): {survived}",
        )


if __name__ == "__main__":
    unittest.main()
