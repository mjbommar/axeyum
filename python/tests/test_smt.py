"""`axeyum.smt.solve` -- the three verdicts, the one exception, and a
differential against the binary this binding is meant to replace."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

import axeyum
from axeyum import smt

REPO_ROOT = Path(__file__).resolve().parents[2]
SMTCOMP_CLI = REPO_ROOT / "target" / "release" / "examples" / "smtcomp_cli"
TIMEOUT_MS = 20_000

# A 64-bit semiprime factoring query: `a * b = 3369738766071892021` with both
# factors above 1. Nothing about it is decidable in a millisecond, and it is not
# refutable either, so a 1 ms budget can only come back undecided.
HARD_FACTORING = """(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (= (bvmul a b) (_ bv3369738766071892021 64)))
(assert (bvugt a (_ bv1 64)))
(assert (bvugt b (_ bv1 64)))
(check-sat)"""

# Fixed, not globbed: a differential whose input set can silently shrink to zero
# is the inert-gate trap. `test_differential_ran_enough_comparisons` asserts the
# count as well.
DIFFERENTIAL_FILES = [
    "corpus/regression/qf_bv/sat_wraparound.smt2",
    "corpus/regression/qf_bv/unsat_eq_conflict.smt2",
    "corpus/regression/qf_lia/sat_gt.smt2",
    "corpus/regression/qf_lia/unsat_parity.smt2",
    "corpus/regression/qf_uf/sat_distinct.smt2",
    "corpus/regression/qf_uf/unsat_congruence.smt2",
    "corpus/regression/qf_lra/sat_halfplane.smt2",
    "corpus/regression/qf_lra/unsat_sum_conflict.smt2",
]


def test_sat_replays() -> None:
    outcome = smt.solve(
        "(set-logic QF_BV)\n"
        "(declare-fun x () (_ BitVec 8))\n"
        "(declare-fun y () (_ BitVec 8))\n"
        "(assert (= (bvadd x y) (_ bv10 8)))\n"
        "(assert (bvult x (_ bv3 8)))\n"
        "(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert outcome.status == "sat"
    assert outcome.logic == "QF_BV"
    assert outcome.detail == ""
    assert set(outcome.model) == {"x", "y"}
    # The canonical check: the model satisfies the ORIGINAL assertions.
    assert outcome.replay() is True
    assert (int(outcome.model["x"]) + int(outcome.model["y"])) % 256 == 10


def test_unsat() -> None:
    outcome = smt.solve(
        "(set-logic QF_BV)\n"
        "(declare-fun x () (_ BitVec 8))\n"
        "(assert (bvult x (_ bv1 8)))\n"
        "(assert (bvugt x (_ bv0 8)))\n"
        "(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert outcome.status == "unsat"
    assert outcome.model == {}
    assert outcome.replay() is False


def test_unknown_is_a_value_not_an_exception() -> None:
    # No `pytest.raises` here on purpose: a budget-exhausted query is a VALUE.
    outcome = smt.solve(HARD_FACTORING, timeout_ms=1)
    assert outcome.status == "unknown"
    assert outcome.detail != ""
    assert outcome.model == {}
    assert outcome.replay() is False


def test_expected_status_is_echoed_never_consulted() -> None:
    # A script whose declared `:status` is a LIE. If the binding leaked it to the
    # solver, the verdict would follow the lie.
    outcome = smt.solve(
        "(set-logic QF_BV)\n"
        "(set-info :status unsat)\n"
        "(declare-fun x () (_ BitVec 4))\n"
        "(assert (= x (_ bv5 4)))\n"
        "(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert outcome.expected_status == "unsat"
    assert outcome.status == "sat"


def test_parse_error_raises() -> None:
    with pytest.raises(axeyum.SmtLibParseError) as caught:
        smt.solve("(this is not smtlib")
    assert isinstance(caught.value, axeyum.AxeyumError)


def _cli_verdict(path: Path) -> str:
    completed = subprocess.run(
        [str(SMTCOMP_CLI), str(path), "--timeout-ms", str(TIMEOUT_MS)],
        capture_output=True,
        text=True,
        check=True,
        timeout=120,
    )
    return completed.stdout.strip()


@pytest.mark.skipif(
    not SMTCOMP_CLI.exists() or shutil.which(str(SMTCOMP_CLI)) is None,
    reason=(
        f"{SMTCOMP_CLI} not built "
        "(cargo build --release -p axeyum-solver --features full --example smtcomp_cli)"
    ),
)
@pytest.mark.parametrize("relative", DIFFERENTIAL_FILES)
def test_differential_against_smtcomp_cli(relative: str) -> None:
    path = REPO_ROOT / relative
    assert path.exists(), f"corpus file vanished: {path}"
    cli = _cli_verdict(path)
    binding = smt.solve(path.read_text(), timeout_ms=TIMEOUT_MS).status
    assert binding == cli, f"{relative}: binding={binding} smtcomp_cli={cli}"


def test_differential_ran_enough_comparisons() -> None:
    # The differential is parametrized, so a shrunk list would silently reduce
    # it to nothing while still passing. This is the count guard.
    assert len(DIFFERENTIAL_FILES) >= 6
    assert len(set(DIFFERENTIAL_FILES)) == len(DIFFERENTIAL_FILES)


def test_replay_false_is_not_a_soundness_signal() -> None:
    """Pins the one known gap, so it cannot widen unnoticed.

    The front door reaches routes ``axeyum_solver::solve`` alone does not, and
    the replay state this binding builds comes from the latter. A quantified
    query the front door decides ``sat`` therefore has no replay available, and
    ``replay()`` says ``False`` -- which is NOT "the model is wrong".

    TODO(plan 02): give ``replay()`` a third answer, or build the replay state
    from the front door itself.
    """
    outcome = smt.solve(
        "(set-logic LIA)\n(assert (not (forall ((n Int)) (>= n 0))))\n(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert outcome.status == "sat"
    assert outcome.model == {}
    assert outcome.replay() is False

    # ... while a ground query on the same logic replays fine, so the gap is the
    # quantified route and not the binding's replay wiring.
    ground = smt.solve(
        "(set-logic LIA)\n(declare-fun k () Int)\n(assert (> k 3))\n(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert ground.status == "sat"
    assert ground.replay() is True
    assert int(ground.model["k"]) > 3
