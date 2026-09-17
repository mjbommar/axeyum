#!/usr/bin/env python3
"""Controls for the cindergraph-defects gate (`scripts/check-cindergraph-defects.sh`).

Two halves, and the split is the point:

``ReaderGuards`` drives every failure CLASS of the second reading
(`scripts/check-cindergraph-defects.py`) on synthetic rows, one test per class,
with no toolchain at all. Deleting a guard in the reader must kill exactly one
of these.

``LiveGate`` runs the shipped gate ONCE over the real samples, the real
cindergraph, the native solver and clang, and then reads its failure lines
back one class at a time. The mutations registered in
``scripts/tests/mutation_controls.py`` under ``cindergraph-defects`` are
mutations of the SUBJECT — a sample loses its bounds check, the lifter's
usual-arithmetic rule breaks, `replay()` starts saying yes — and each must kill
exactly one of these: the test that watches the class the gate reports it
under. If a mutation killed two, the classes overlap and the gate's diagnosis
is worth less than it reads; if it killed none, the gate cannot fail and
CLAUDE.md says what that is worth.

The live half SKIPS (never passes) on a host without clang, exactly as the
gate itself does, and FAILS when the gate refuses -- a missing module is a
provisioning error on a host that has the venv, not a reason to go green.

    python3 -m unittest scripts.tests.test_check_cindergraph_defects
    python3 scripts/tests/mutation_controls.py cindergraph-defects
"""

from __future__ import annotations

import importlib.util
import os
import pathlib
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
GATE = ROOT / "scripts" / "check-cindergraph-defects.sh"
READER = ROOT / "scripts" / "check-cindergraph-defects.py"


def _reader():
    spec = importlib.util.spec_from_file_location("check_cindergraph_defects", READER)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


READER_MODULE = _reader()
FAIL = READER_MODULE.FAIL


# --------------------------------------------------------------------------
# The reader's guards, on synthetic evidence.
# --------------------------------------------------------------------------

_CLEAN = ("s.c", "f_fixed", "clean", "-", "2 obligations over 1 paths, all unsat", "no witness")
_WITNESS = (
    "s.c",
    "f_bug",
    "buffer",
    "line 9",
    "`memcpy(d, s, n)` with n=1",
    "REPLAYED: ASan (line 9)",
)
_DEAD = (
    "s.c",
    "g",
    "dead-branch",
    "line 4",
    "`n < 0` true edge is infeasible",
    "proved unreachable",
)
_EXPECT = {"f_fixed": "clean", "f_bug": "finding", "g": "finding"}
_STDOUT = (
    "cindergraph|version=0.1.0|commit=abc|pinned=abc|match=yes\n"
    "CINDERGRAPH_DEFECTS_REPLAY_CONTROL|witness=s.c:9|judged_at=10|refused|fired at 9\n"
    "CINDERGRAPH_DEFECTS_RUN|rows=3|replayed=1|dead=1|clean=1|bounded=0|no_oracle=0|refused=0|failures=0\n"
)


def _classes(rows, expect=_EXPECT, stdout=_STDOUT, status=0):
    failures, _ = READER_MODULE.evaluate(list(rows), dict(expect), stdout, status)
    return sorted({cls for cls, _ in failures})


class ReaderGuards(unittest.TestCase):
    def test_the_clean_evidence_passes(self) -> None:
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD]), [])

    def test_a_function_without_an_expect_line_is_an_expectation_failure(self) -> None:
        expect = {k: v for k, v in _EXPECT.items() if k != "g"}
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD], expect), ["expectation"])

    def test_an_expect_line_without_a_row_is_an_expectation_failure(self) -> None:
        stdout = _STDOUT.replace("rows=3", "rows=2").replace("dead=1", "dead=0")
        self.assertEqual(_classes([_CLEAN, _WITNESS], stdout=stdout), ["expectation"])

    def test_a_clean_function_gaining_a_witness_is_an_expectation_failure(self) -> None:
        # The driver prints EXPECTATION-FAILED; the counts move too. One class.
        gained = ("s.c", "f_fixed", "buffer", "line 12", "`memcpy`", "REPLAYED: ASan (line 12)")
        failed = ("s.c", "f_fixed", "EXPECTATION-FAILED", "-", "expected clean", "")
        stdout = _STDOUT.replace("rows=3", "rows=4").replace("replayed=1", "replayed=2")
        stdout = stdout.replace("clean=1", "clean=0").replace("failures=0", "failures=1")
        self.assertEqual(
            _classes([gained, failed, _WITNESS, _DEAD], stdout=stdout, status=1), ["expectation"]
        )

    def test_an_unexpected_refusal_is_an_expectation_failure(self) -> None:
        refused = ("s.c", "f_fixed", "refused", "-", "-", "line 3: goto is refused")
        stdout = _STDOUT.replace("clean=1", "clean=0").replace("refused=0", "refused=1")
        self.assertEqual(_classes([refused, _WITNESS, _DEAD], stdout=stdout), ["expectation"])

    def test_a_witness_that_did_not_replay_is_a_replay_failure(self) -> None:
        bad = _WITNESS[:5] + ("DID NOT REPLAY: exit 0, no sanitizer report",)
        stdout = _STDOUT.replace("replayed=1", "replayed=0").replace("failures=0", "failures=1")
        self.assertEqual(_classes([_CLEAN, bad, _DEAD], stdout=stdout, status=1), ["replay"])

    def test_a_replay_at_another_line_is_a_replay_failure(self) -> None:
        elsewhere = _WITNESS[:5] + ("REPLAYED: ASan (line 10)",)
        self.assertEqual(_classes([_CLEAN, elsewhere, _DEAD]), ["replay"])

    def test_a_replay_naming_no_line_is_a_replay_failure(self) -> None:
        unlocated = _WITNESS[:5] + ("REPLAYED: ASan somewhere",)
        self.assertEqual(_classes([_CLEAN, unlocated, _DEAD]), ["replay"])

    def test_a_control_that_accepted_the_wrong_line_is_a_control_failure(self) -> None:
        stdout = _STDOUT.replace("|refused|", "|ACCEPTED|")
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD], stdout=stdout), ["control"])

    def test_a_missing_control_line_is_a_control_failure(self) -> None:
        stdout = "\n".join(l for l in _STDOUT.splitlines() if "REPLAY_CONTROL" not in l) + "\n"
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD], stdout=stdout), ["control"])

    def test_an_unpinned_cindergraph_is_a_provenance_failure(self) -> None:
        stdout = _STDOUT.replace("commit=abc|pinned=abc", "commit=abc|pinned=def")
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD], stdout=stdout), ["provenance"])

    def test_an_unknown_commit_is_a_provenance_failure_even_if_both_are_unknown(self) -> None:
        stdout = _STDOUT.replace("commit=abc|pinned=abc", "commit=unknown|pinned=unknown")
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD], stdout=stdout), ["provenance"])

    def test_driver_counts_that_disagree_with_the_table_are_inconsistent(self) -> None:
        stdout = _STDOUT.replace("replayed=1", "replayed=2")
        self.assertEqual(_classes([_CLEAN, _WITNESS, _DEAD], stdout=stdout), ["inconsistent"])

    def test_a_green_exit_with_driver_failures_is_inconsistent(self) -> None:
        stdout = _STDOUT.replace("failures=0", "failures=1")
        self.assertEqual(
            _classes([_CLEAN, _WITNESS, _DEAD], stdout=stdout, status=0), ["inconsistent"]
        )

    def test_an_empty_table_is_inconsistent(self) -> None:
        stdout = _STDOUT.replace("rows=3", "rows=0").replace("replayed=1", "replayed=0")
        stdout = stdout.replace("dead=1", "dead=0").replace("clean=1", "clean=0")
        self.assertEqual(_classes([], {}, stdout=stdout), ["inconsistent"])


# --------------------------------------------------------------------------
# The shipped gate, once, over the real samples.
# --------------------------------------------------------------------------

_LIVE: dict[str, object] = {}


def _live() -> tuple[int, str]:
    """Run the gate once per process; every live test reads the same output."""
    if "result" not in _LIVE:
        env = dict(os.environ)
        env.pop("AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS", None)
        done = subprocess.run(
            ["bash", str(GATE)],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            check=False,
            timeout=1800,
        )
        _LIVE["result"] = (done.returncode, done.stdout + done.stderr)
    return _LIVE["result"]  # type: ignore[return-value]


class LiveGate(unittest.TestCase):
    def setUp(self) -> None:
        self.status, self.out = _live()
        if "CINDERGRAPH_DEFECTS|SKIPPED|" in self.out:
            self.skipTest("no sanitizer toolchain on this host: " + self.out.strip()[-120:])
        if "CINDERGRAPH_DEFECTS|REFUSED|" in self.out:
            self.fail("the gate refused to run:\n" + self.out[-800:])

    def _failures(self, cls: str) -> list[str]:
        return [l for l in self.out.splitlines() if l.startswith(f"{FAIL}|{cls}|")]

    def test_every_expectation_in_the_samples_is_met(self) -> None:
        self.assertEqual(self._failures("expectation"), [])

    def test_every_witness_replayed_at_its_own_line(self) -> None:
        self.assertEqual(self._failures("replay"), [])

    def test_the_replay_check_refuses_a_wrong_line(self) -> None:
        self.assertEqual(self._failures("control"), [])

    def test_it_ran_the_pinned_cindergraph(self) -> None:
        self.assertEqual(self._failures("provenance"), [])

    def test_the_driver_and_the_reader_agree(self) -> None:
        self.assertEqual(self._failures("inconsistent"), [])

    def test_the_verdict_names_only_known_classes_and_matches_the_exit_status(self) -> None:
        # Any failure of an unknown class, or a PASS/FAIL that disagrees with
        # the exit status, would otherwise go unwatched by the tests above.
        fails = [l for l in self.out.splitlines() if l.startswith(FAIL + "|")]
        unknown = [l for l in fails if l.split("|")[1] not in READER_MODULE.CLASSES]
        self.assertEqual(unknown, [])
        summary = [l for l in self.out.splitlines() if l.startswith("CINDERGRAPH_DEFECTS|rows=")]
        self.assertEqual(len(summary), 1, self.out[-800:])
        verdict = summary[0].rsplit("|", 1)[1]
        self.assertEqual(verdict, "PASS" if not fails else "FAIL")
        self.assertEqual(self.status == 0, verdict == "PASS")
        self.assertIn(f"failures={len(fails)}|", summary[0])


if __name__ == "__main__":
    unittest.main()
