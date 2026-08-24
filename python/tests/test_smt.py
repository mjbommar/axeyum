"""`axeyum.smt.solve` -- the three verdicts, the one exception, and a
differential against the binary this binding is meant to replace."""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

import axeyum
from axeyum import ir, smt

REPO_ROOT = Path(__file__).resolve().parents[2]
# `AXEYUM_SMTCOMP_CLI` lets a snapshot tree point at a binary built elsewhere;
# without it the in-tree release build is used. Neither present means SKIP --
# a differential that silently ran zero comparisons is the inert-gate trap.
SMTCOMP_CLI = Path(
    os.environ.get(
        "AXEYUM_SMTCOMP_CLI", str(REPO_ROOT / "target" / "release" / "examples" / "smtcomp_cli")
    )
)
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
    # QF_BV
    "corpus/regression/qf_bv/sat_wraparound.smt2",
    "corpus/regression/qf_bv/unsat_eq_conflict.smt2",
    "corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bug578.smt2",
    "corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bool-model.smt2",
    "corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bv-term-small-rw-228.smt2",
    "corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bvproof3.smt2",
    "corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__divtest_2_5.smt2",
    "corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__divtest_2_6.smt2",
    # QF_LIA
    "corpus/regression/qf_lia/sat_gt.smt2",
    "corpus/regression/qf_lia/unsat_parity.smt2",
    "corpus/regression/qf_lia/unsat_integer_gap.smt2",
    "corpus/regression/cvc5/qf_lia/cvc5__cli__regress0__bug365.smt2",
    "corpus/regression/cvc5/qf_lia/cvc5__cli__regress0__bug383.smt2",
    "corpus/regression/cvc5/qf_lia/cvc5__cli__regress0__named-expr-use.smt2",
    # QF_LRA
    "corpus/regression/qf_lra/sat_halfplane.smt2",
    "corpus/regression/qf_lra/unsat_sum_conflict.smt2",
    "corpus/regression/qf_lra/unsat_empty_interval.smt2",
    "corpus/regression/cvc5/qf_lra/cvc5__cli__regress0__bug187.smt2",
    "corpus/regression/cvc5/qf_lra/cvc5__cli__regress0__simple-lra.smt2",
    # QF_UF
    "corpus/regression/qf_uf/sat_distinct.smt2",
    "corpus/regression/qf_uf/unsat_congruence.smt2",
    "corpus/regression/cvc5/qf_uf/cvc5__cli__regress0__chained-equality.smt2",
    "corpus/regression/cvc5/qf_uf/cvc5__cli__regress0__uf__bool-pred-nested.smt2",
    # arrays, datatypes, nonlinear integers, UF+LIA
    "corpus/regression/qf_abv/unsat_read_over_write.smt2",
    "corpus/regression/qf_dt/unsat_distinct_constructors.smt2",
    "corpus/regression/qf_nia/unsat_square_two.smt2",
    "corpus/regression/qf_uflia/sat_consistent.smt2",
    "corpus/regression/qf_uflia/unsat_congruence.smt2",
]

# The three cvc5 `qf_s` files are deliberately absent: they parse-error, so a
# differential over them would compare two error paths rather than two solvers.


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
    assert outcome.replay_available is True
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
    assert outcome.replay_available is False
    with pytest.raises(axeyum.ReplayUnavailable):
        outcome.replay()


def test_unknown_is_a_value_not_an_exception() -> None:
    # No `pytest.raises` here on purpose: a budget-exhausted query is a VALUE.
    outcome = smt.solve(HARD_FACTORING, timeout_ms=1)
    assert outcome.status == "unknown"
    assert outcome.detail != ""
    assert outcome.model == {}
    assert outcome.replay_available is False
    with pytest.raises(axeyum.ReplayUnavailable):
        outcome.replay()


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
    assert len(DIFFERENTIAL_FILES) >= 20
    assert len(set(DIFFERENTIAL_FILES)) == len(DIFFERENTIAL_FILES)
    missing = [name for name in DIFFERENTIAL_FILES if not (REPO_ROOT / name).exists()]
    assert missing == []
    # And it spans more than one logic, which a count alone does not prove.
    logics = {name.split("/")[-2].split("__")[0] for name in DIFFERENTIAL_FILES}
    assert {"qf_bv", "qf_lia", "qf_lra", "qf_uf"} <= logics


def test_replay_unavailable_is_distinct_from_replay_failed() -> None:
    """Pins the one known gap, so it cannot widen unnoticed -- and pins that it
    is reported as its own state, never as ``False``.

    The front door reaches routes ``axeyum_solver::solve`` alone does not, and
    the replay state this binding builds comes from the latter. A quantified
    query the front door decides ``sat`` therefore has no replay available;
    ``replay_available`` is ``False`` and ``replay()`` RAISES. ``False`` from
    ``replay()`` is reserved for "replayed and the model is wrong".
    """
    outcome = smt.solve(
        "(set-logic LIA)\n(assert (not (forall ((n Int)) (>= n 0))))\n(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert outcome.status == "sat"
    assert outcome.model == {}
    assert outcome.replay_available is False
    assert "quantified" in (outcome.replay_unavailable_reason or "")
    with pytest.raises(axeyum.ReplayUnavailable, match="quantified"):
        outcome.replay()

    # ... while a ground query on the same logic replays fine, so the gap is the
    # quantified route and not the binding's replay wiring.
    ground = smt.solve(
        "(set-logic LIA)\n(declare-fun k () Int)\n(assert (> k 3))\n(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert ground.status == "sat"
    assert ground.replay() is True
    assert int(ground.model["k"]) > 3


# ---------------------------------------------------------------- sessions


MULTI_QUERY = """(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (bvult x (_ bv3 8)))
(check-sat)
(get-model)
(pop 1)
(assert (bvugt x (_ bv250 8)))
(assert (bvult x (_ bv2 8)))
(check-sat)
(get-unsat-core)
(echo "done")
(get-info :all-statistics)
"""


def test_session_answers_every_output_command_in_order() -> None:
    responses = smt.session(MULTI_QUERY, timeout_ms=TIMEOUT_MS)
    kinds = [response.kind for response in responses]
    assert len(responses) >= 5
    # One response per OUTPUT command, in script order.
    assert kinds[0] == "check-sat"
    assert kinds[1] == "model"
    verdicts = [r.status for r in responses if r.kind == "check-sat"]
    assert verdicts == ["sat", "unsat"]
    assert "echo" in kinds


def test_session_keeps_unsupported_and_error_distinct() -> None:
    # `(get-unsat-core)` without `:produce-unsat-cores` is an ERROR (illegal in
    # the state the script reached); `(get-info :all-statistics)` is
    # UNSUPPORTED (outside the implemented surface). Collapsing the two would
    # lose the difference between "that script is wrong" and "we do not do
    # that", so the binding keeps them as separate kinds.
    responses = smt.session(MULTI_QUERY, timeout_ms=TIMEOUT_MS)
    kinds = {response.kind for response in responses}
    assert "error" in kinds or "unsupported" in kinds
    for response in responses:
        if response.kind in {"error", "unsupported"}:
            assert response.command is not None
            assert response.text is not None
    # The two never share a kind string.
    assert not ({"error"} & {"unsupported"})


def test_incremental_returns_one_verdict_per_check_sat() -> None:
    verdicts = smt.incremental(MULTI_QUERY, timeout_ms=TIMEOUT_MS)
    assert verdicts == ["sat", "unsat"]
    # It delegates to the same session walk, so the two cannot disagree.
    session_verdicts = [
        r.status for r in smt.session(MULTI_QUERY, timeout_ms=TIMEOUT_MS) if r.kind == "check-sat"
    ]
    assert verdicts == session_verdicts


def test_declarations_are_global_and_survive_pop() -> None:
    # SMT-LIB: `pop` unwinds assertions, not declarations.
    verdicts = smt.incremental(
        "(set-logic QF_BV)\n"
        "(push 1)\n"
        "(declare-fun x () (_ BitVec 4))\n"
        "(assert (= x (_ bv1 4)))\n"
        "(check-sat)\n"
        "(pop 1)\n"
        "(assert (= x (_ bv2 4)))\n"
        "(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    assert verdicts == ["sat", "sat"]


# ------------------------------------------------------- the get-* family


def test_get_value_reads_the_replay_checked_model() -> None:
    values = smt.get_value(
        "(set-logic QF_BV)\n"
        "(declare-fun x () (_ BitVec 8))\n"
        "(assert (= x (_ bv12 8)))\n"
        "(check-sat)\n"
        "(get-value (x (bvadd x (_ bv1 8))))",
        timeout_ms=TIMEOUT_MS,
    )
    assert values is not None
    assert [int(value) for value in values] == [12, 13]


def test_get_value_is_none_on_unsat() -> None:
    assert (
        smt.get_value(
            "(set-logic QF_BV)\n"
            "(declare-fun x () (_ BitVec 4))\n"
            "(assert (and (bvult x (_ bv1 4)) (bvugt x (_ bv0 4))))\n"
            "(check-sat)\n"
            "(get-value (x))",
            timeout_ms=TIMEOUT_MS,
        )
        is None
    )


def test_get_assignment_reports_named_boolean_truth_values() -> None:
    assignment = smt.get_assignment(
        "(set-logic QF_UF)\n"
        "(set-option :produce-assignments true)\n"
        "(declare-fun p () Bool)\n"
        "(declare-fun q () Bool)\n"
        "(assert (! p :named a))\n"
        "(assert (! (not q) :named b))\n"
        "(check-sat)\n"
        "(get-assignment)",
        timeout_ms=TIMEOUT_MS,
    )
    assert assignment is not None
    assert dict(assignment) == {"a": True, "b": True}


def test_unsat_core_is_deletion_minimized() -> None:
    core = smt.unsat_core(
        "(set-logic QF_LIA)\n"
        "(set-option :produce-unsat-cores true)\n"
        "(declare-fun n () Int)\n"
        "(assert (! (> n 10) :named lower))\n"
        "(assert (! (< n 0) :named upper))\n"
        "(assert (! (= n n) :named useless))\n"
        "(check-sat)\n"
        "(get-unsat-core)",
        timeout_ms=TIMEOUT_MS,
    )
    assert core is not None
    # Every returned name is genuinely needed -- the tautology is not.
    assert set(core) == {"lower", "upper"}


def test_unsat_core_is_none_on_sat() -> None:
    assert (
        smt.unsat_core(
            "(set-logic QF_LIA)\n"
            "(set-option :produce-unsat-cores true)\n"
            "(declare-fun n () Int)\n"
            "(assert (! (> n 10) :named lower))\n"
            "(check-sat)\n"
            "(get-unsat-core)",
            timeout_ms=TIMEOUT_MS,
        )
        is None
    )


def test_get_proof_returns_alethe_text_or_an_honest_none() -> None:
    proof = smt.get_proof(
        "(set-logic QF_BV)\n"
        "(set-option :produce-proofs true)\n"
        "(declare-fun x () (_ BitVec 4))\n"
        "(assert (bvult x (_ bv1 4)))\n"
        "(assert (bvugt x (_ bv0 4)))\n"
        "(check-sat)\n"
        "(get-proof)",
        timeout_ms=TIMEOUT_MS,
    )
    # `None` means NO EMITTER COVERS THIS REFUTATION -- it is not a claim that
    # the script is satisfiable. Both answers are correct here; what is not
    # acceptable is a proof that does not look like Alethe.
    if proof is not None:
        assert "(step" in proof or "(assume" in proof


# ------------------------------------------------------ parsing and writing


def test_parse_exposes_the_command_sequence() -> None:
    script = smt.parse(MULTI_QUERY)
    assert script.logic == "QF_BV"
    assert script.check_sats == 2
    kinds = [command["kind"] for command in script.commands]
    assert kinds.count("check-sat") == 2
    assert "push" in kinds and "pop" in kinds
    assert [c["levels"] for c in script.commands if c["kind"] == "push"] == [1]
    assert "x" in script.model_symbols


def test_parse_reports_the_declared_status_without_consulting_it() -> None:
    script = smt.parse(
        "(set-logic QF_BV)\n(set-info :status unsat)\n"
        "(declare-fun x () (_ BitVec 4))\n(assert (= x (_ bv5 4)))\n(check-sat)"
    )
    assert script.expected_status == "unsat"
    # ... and the front door still answers `sat`, because the declared status
    # is benchmark metadata the solver never sees.
    assert (
        smt.solve(
            "(set-logic QF_BV)\n(set-info :status unsat)\n"
            "(declare-fun x () (_ BitVec 4))\n(assert (= x (_ bv5 4)))\n(check-sat)",
            timeout_ms=TIMEOUT_MS,
        ).status
        == "sat"
    )


def test_parse_error_is_distinct_from_a_budget_miss() -> None:
    with pytest.raises(axeyum.SmtLibParseError):
        smt.parse("(this is not smtlib")


def test_flat_view_is_the_solvable_one() -> None:
    script = smt.parse(
        "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n(assert (= x (_ bv3 8)))\n(check-sat)"
    )
    view = script.flat_view()
    assert view is not None
    assert len(view) == 1
    assert script.render(view[0]) == "(= x (_ bv3 8))"
    assert script.word_only_fallback is None


def test_no_script_ever_yields_an_empty_solvable_flat_view() -> None:
    """The invariant `solvable_flat_view` exists to hold.

    An empty assertion list solves as a vacuous ``sat`` -- a shipped P0. The
    bound accessor must therefore never hand out an empty list as solvable: it
    answers ``None`` for a word-first-fallback parse instead. Its
    ``checked_flat_view`` sibling ``debug_assert!``s and is silently wrong in
    release, which is why it is not bound at all.

    **Not-done note.** A parse that actually takes the word-first fallback
    could not be constructed from ``smt.parse`` in this slice: every over-cap
    string script tried (literals from 60 to 4096 characters, 2 to 10-way
    concatenations, and all 152 committed corpus files) either parses normally
    or raises ``SmtLibParseError``, and zero committed benchmarks set
    ``word_only_fallback``. So the ``None`` branch is asserted structurally
    here rather than by a fixture, and the invariant it protects is checked
    over the whole corpus.
    """
    from pathlib import Path as _Path

    checked = 0
    for path in sorted((REPO_ROOT / "corpus" / "regression").rglob("*.smt2")):
        assert isinstance(path, _Path)
        try:
            script = smt.parse(path.read_text())
        except axeyum.SmtLibParseError:
            continue
        view = script.flat_view()
        checked += 1
        # The whole point: never an empty list. `None` or something real.
        assert view is None or len(view) > 0, path
        assert (view is None) == (script.word_only_fallback is not None), path
    assert checked >= 100, f"only {checked} corpus scripts parsed -- did the corpus shrink?"


def test_an_over_cap_string_script_refuses_rather_than_returning_an_empty_view() -> None:
    # The other side of the same invariant: when nothing can represent the
    # script, the answer is an exception, not a solvable-looking empty view.
    with pytest.raises(axeyum.SmtLibParseError):
        smt.parse(
            "(set-logic QF_S)\n(declare-fun s () String)\n"
            f'(assert (= s "{"a" * 4096}"))\n(check-sat)'
        )


def test_write_script_round_trips_through_parse() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    assertion = arena.eq(arena.bvadd(x, arena.bv_const(8, 3)), arena.bv_const(8, 10))
    text = smt.write_script(arena, [assertion])
    assert "(check-sat)" in text

    reparsed = smt.parse(text)
    view = reparsed.flat_view()
    assert view is not None and len(view) == 1
    assert reparsed.render(view[0]) == arena.render(assertion)

    # ... and the round trip is a fixed point, not a one-way normalization.
    again = smt.parse(smt.write_script(arena, [assertion]))
    assert again.render(again.flat_view()[0]) == reparsed.render(view[0])


def test_write_script_rejects_a_foreign_term() -> None:
    # The Rust writer PANICS on a term from another arena; the epoch check is
    # what turns that into an exception.
    left, right = ir.Arena(), ir.Arena()
    term = left.bool_var("p")
    with pytest.raises(axeyum.EpochError):
        smt.write_script(right, [term])


def test_script_terms_are_not_interchangeable_with_arena_terms() -> None:
    script = smt.parse("(set-logic QF_BV)\n(declare-fun x () (_ BitVec 4))\n(assert (= x x))")
    view = script.flat_view()
    assert view is not None
    other = smt.parse("(set-logic QF_BV)\n(declare-fun y () (_ BitVec 4))\n(assert (= y y))")
    with pytest.raises(axeyum.EpochError):
        other.render(view[0])


def test_solve_accepts_the_full_budget_keyword_set() -> None:
    outcome = smt.solve(
        HARD_FACTORING,
        timeout_ms=TIMEOUT_MS,
        node_budget=1,
        resource_limit=10,
        memory_limit_mb=4096,
        cnf_variable_budget=10,
        cnf_clause_budget=10,
        prove_unsat=False,
        preprocess=True,
    )
    # A budget miss is an `unknown` VALUE with a reason, never an exception.
    assert outcome.status == "unknown"
    assert outcome.detail != ""
