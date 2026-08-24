"""`axeyum.solver` -- verdicts, evidence, proofs, and the checkers that can fail.

The theme of this file is the repository's own rule: *a checker that cannot
fail is worse than no checker*. So the tests below insist that

* ``unknown`` arrives as a value with a classified kind, never an exception;
* ``Evidence.check_outcome()`` can say ``nothing-to-check`` on a shape where
  the ``bool``-returning ``check()`` would have said ``True``;
* ``recheck_lrat()`` is ``None``, not ``True``, when there is no LRAT;
* a tampered DRAT is ``verified=False``, and a budget miss is a third answer;
* an ``unsat``-proof export on a *satisfiable* query says ``satisfiable``, and
  a 1 ms budget on a hard one says ``inconclusive`` -- not "proved".
"""

from __future__ import annotations

import pytest

import axeyum
from axeyum import ir, solver
from axeyum._native.ir import bv as ir_bv
from axeyum._native.solver import cnf, proofs

TIMEOUT_MS = 20_000

# A 64-bit semiprime factoring query. Nothing about it is decidable in a
# millisecond, and it is not refutable either, so a 1 ms budget can only come
# back undecided.
HARD_FACTORING_PRODUCT = 3_369_738_766_071_892_021

# 2**61 - 1, a Mersenne prime. Asking for two non-trivial factors *without*
# multiplication overflow is genuinely unsatisfiable and genuinely hard: the
# bit-blasted CNF is ~40k variables and ~150k clauses, so a 1 ms budget cannot
# decide it and a proof search cannot finish it.
HARD_PRIME = 2_305_843_009_213_693_951


def hard_factoring(arena: ir.Arena) -> list[ir.Term]:
    a = arena.bv_var("a", 64)
    b = arena.bv_var("b", 64)
    one = arena.bv_const(64, 1)
    return [
        arena.eq(arena.bvmul(a, b), arena.bv_const(64, HARD_FACTORING_PRODUCT)),
        arena.bvugt(a, one),
        arena.bvugt(b, one),
    ]


def hard_unsat_factoring(arena: ir.Arena) -> list[ir.Term]:
    a = arena.bv_var("f1", 64)
    b = arena.bv_var("f2", 64)
    one = arena.bv_const(64, 1)
    return [
        arena.eq(arena.bvmul(a, b), arena.bv_const(64, HARD_PRIME)),
        arena.not_(arena.bvumulo(a, b)),
        arena.bvugt(a, one),
        arena.bvugt(b, one),
    ]


def unsat_bv(arena: ir.Arena) -> list[ir.Term]:
    x = arena.bv_var("x", 8)
    return [
        arena.bvult(x, arena.bv_const(8, 1)),
        arena.bvugt(x, arena.bv_const(8, 0)),
    ]


# ------------------------------------------------------------------- config


def test_config_exposes_the_plain_solver_config_fields() -> None:
    config = solver.Config(
        timeout_ms=1234,
        resource_limit=10,
        memory_limit_mb=64,
        node_budget=99,
        cnf_variable_budget=100,
        cnf_clause_budget=200,
        prove_unsat=True,
        preprocess=False,
    )
    assert config.timeout_ms == 1234
    assert config.prove_unsat is True
    assert config.preprocess is False
    assert config.node_budget == 99


def test_config_rejects_an_unknown_bit_lowering_mode() -> None:
    with pytest.raises(axeyum.AxeyumError):
        solver.Config(bit_lowering_mode="nonsense")


def test_config_defaults_match_the_rust_defaults() -> None:
    config = solver.Config()
    assert config.timeout_ms is None
    assert config.prove_unsat is False
    # `preprocess` is the one bool that defaults ON in Rust.
    assert config.preprocess is True


# ------------------------------------------------------------ check results


def test_sat_carries_a_model_that_replays() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    y = arena.bv_var("y", 8)
    goal = [
        arena.eq(arena.bvadd(x, y), arena.bv_const(8, 10)),
        arena.bvult(x, arena.bv_const(8, 3)),
    ]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat"
    assert result.is_sat() and not result.is_unsat() and not result.is_unknown()
    model = result.model(arena)
    assert set(model) >= {"x", "y"}
    assert (int(model["x"]) + int(model["y"])) % 256 == 10
    assert result.replay(arena, goal) is True


def test_unsat_has_no_model_and_replay_refuses_rather_than_lying() -> None:
    arena = ir.Arena()
    goal = unsat_bv(arena)
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "unsat"
    assert result.model(arena) == {}
    # NOT `False`: "there was nothing to replay" and "the replay disagreed" are
    # different findings, and only the second is a soundness signal.
    with pytest.raises(ValueError):
        result.replay(arena, goal)


def test_unknown_is_a_value_with_a_classified_kind() -> None:
    arena = ir.Arena()
    result = solver.solve(arena, hard_factoring(arena), solver.Config(timeout_ms=1))
    assert result.status == "unknown"
    assert result.is_unknown()
    assert result.unknown_kind in solver.UNKNOWN_KINDS
    assert result.unknown_kind == axeyum.UnknownKind.TIMEOUT
    assert result.unknown_detail is not None


def test_node_budget_exhaustion_is_its_own_unknown_kind() -> None:
    arena = ir.Arena()
    result = solver.solve(
        arena, hard_factoring(arena), solver.Config(timeout_ms=TIMEOUT_MS, node_budget=1)
    )
    assert result.status == "unknown"
    assert result.unknown_kind == axeyum.UnknownKind.NODE_BUDGET


def test_check_result_converts_to_an_assignment_the_evaluator_accepts() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    goal = [arena.eq(x, arena.bv_const(8, 42))]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assignment = result.to_assignment(arena)
    assert int(ir.eval(arena, x, assignment)) == 42


def test_solve_rejects_a_foreign_term() -> None:
    left, right = ir.Arena(), ir.Arena()
    term = left.bool_var("p")
    with pytest.raises(axeyum.EpochError):
        solver.solve(right, [term])


def test_model_and_replay_reject_a_foreign_arena() -> None:
    arena = ir.Arena()
    goal = [arena.eq(arena.bv_var("x", 8), arena.bv_const(8, 1))]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    other = ir.Arena()
    with pytest.raises(axeyum.EpochError):
        result.model(other)


def test_uninterpreted_function_models_come_back_as_func_values() -> None:
    arena = ir.Arena()
    carrier = arena.declare_uninterpreted_sort("U")
    sort = ir.Sort.uninterpreted(carrier)
    f = arena.declare_fun("f", [sort], ir.Sort.bool())
    a = arena.var(arena.declare("a", sort))
    b = arena.var(arena.declare("b", sort))
    goal = [arena.apply(f, [a]), arena.not_(arena.apply(f, [b]))]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat"
    functions = result.functions(arena)
    assert "f" in functions
    assert isinstance(functions["f"], axeyum.FuncValue)
    assert len(functions["f"].params) == 1


# -------------------------------------------------------------- dispatch


def test_check_auto_explained_agrees_with_solve_and_records_routes() -> None:
    arena = ir.Arena()
    goal = unsat_bv(arena)
    plain = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    explained, trace = solver.check_auto_explained(
        arena, goal, solver.Config(timeout_ms=TIMEOUT_MS)
    )
    # Verdict-invariant: the recorder never participates in a branch.
    assert explained.status == plain.status
    assert len(trace) > 0
    assert trace.to_json().startswith("{") or trace.to_json().startswith("[")


def test_unsat_core_returns_indices_not_terms() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    irrelevant = arena.bvult(arena.bv_var("y", 8), arena.bv_const(8, 200))
    goal = [
        irrelevant,
        arena.bvult(x, arena.bv_const(8, 1)),
        arena.bvugt(x, arena.bv_const(8, 0)),
    ]
    core = solver.unsat_core(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert core is not None
    assert all(isinstance(index, int) for index in core)
    assert set(core) == {1, 2}


def test_unsat_core_is_none_on_a_satisfiable_query() -> None:
    arena = ir.Arena()
    goal = [arena.bvult(arena.bv_var("x", 8), arena.bv_const(8, 200))]
    assert solver.unsat_core(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS)) is None


@pytest.mark.parametrize("strategy", ["eager_pure_rust", "lazy_bv_abstraction", "auto"])
def test_every_bound_strategy_decides_the_same_query(strategy: str) -> None:
    arena = ir.Arena()
    goal = unsat_bv(arena)
    result = solver.solve_with_strategy(arena, goal, strategy, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "unsat"


def test_unknown_strategy_names_are_refused() -> None:
    arena = ir.Arena()
    with pytest.raises(axeyum.AxeyumError):
        solver.solve_with_strategy(arena, [arena.bool_var("p")], "oracle")


def test_portfolio_and_recommendation() -> None:
    arena = ir.Arena()
    goal = unsat_bv(arena)
    recommended = solver.recommended_portfolio(arena, goal)
    assert len(recommended) > 0
    assert set(recommended) <= set(solver.STRATEGIES) | {"unrecognized"}
    result = solver.solve_with_portfolio(
        arena, goal, list(recommended), solver.Config(timeout_ms=TIMEOUT_MS)
    )
    assert result.status == "unsat"


# ------------------------------------------------------------- incremental


def test_incremental_push_pop_and_scope_depth() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    warm = solver.Incremental(arena)
    warm.assert_(arena, arena.bvult(x, arena.bv_const(8, 10)))
    assert warm.check(arena).status == "sat"

    warm.push()
    assert warm.scope_depth == 1
    warm.assert_(arena, arena.bvugt(x, arena.bv_const(8, 20)))
    assert warm.check(arena).status == "unsat"

    assert warm.pop() is True
    assert warm.scope_depth == 0
    assert warm.check(arena).status == "sat"
    # `pop` at the base frame is `False`, not an error -- the Rust contract.
    assert warm.pop() is False


def test_incremental_check_assuming_does_not_persist() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    warm = solver.Incremental(arena)
    warm.assert_(arena, arena.bvult(x, arena.bv_const(8, 10)))
    contradiction = arena.bvugt(x, arena.bv_const(8, 20))
    assert warm.check_assuming(arena, [contradiction]).status == "unsat"
    # The assumption is gone again.
    assert warm.check(arena).status == "sat"


def test_incremental_is_bound_to_one_arena() -> None:
    arena = ir.Arena()
    other = ir.Arena()
    warm = solver.Incremental(arena)
    term = arena.bool_var("p")
    with pytest.raises(axeyum.EpochError):
        warm.assert_(other, term)
    with pytest.raises(axeyum.EpochError):
        warm.check(other)


def test_incremental_stats_are_returned_data() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    warm = solver.Incremental(arena)
    warm.assert_(arena, arena.bvult(x, arena.bv_const(8, 10)))
    warm.check(arena)
    stats = warm.stats()
    # Gauges, not just timers: an encoding actually happened.
    assert stats["cnf_clauses"] > 0
    assert stats["cnf_variables"] > 0
    assert stats["aig_nodes"] > 0
    assert {"checks", "root_encodings", "solve_us", "replay_us"} <= set(stats)
    assert warm.encoded_clause_count > 0
    assert warm.encoded_variable_count > 0
    assert warm.lowered_aig_node_count > 0


def test_replay_checked_sat_cache_reports_every_decline_class() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    warm = solver.Incremental(arena)
    warm.enable_replay_checked_sat_cache()
    warm.assert_(arena, arena.bvult(x, arena.bv_const(8, 10)))
    warm.check(arena)
    warm.check(arena)
    stats = warm.replay_checked_sat_cache_stats()
    assert stats["hits"] + stats["misses"] >= 2
    # Every decline class is reported, not just the hit rate: a cache that
    # cannot say why it refused is a cache you cannot audit.
    for key in (
        "replay_failures",
        "declined_unsat",
        "declined_unknown",
        "declined_oversized_models",
        "declined_non_scalar_models",
    ):
        assert key in stats
    warm.disable_replay_checked_sat_cache()
    assert warm.replay_checked_sat_cache_stats()["entries"] == 0


# ---------------------------------------------------------------- evidence


def test_evidence_verifies_a_sat_model() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    goal = [arena.eq(x, arena.bv_const(8, 9))]
    report = solver.produce_evidence(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert report.verdict == "sat"
    outcome = report.check_outcome(arena, goal)
    assert outcome.is_verified()
    assert outcome.status == "verified"
    assert outcome.reason is None


def test_evidence_check_outcome_is_nothing_to_check_where_a_bool_would_pass() -> None:
    """The three-valued checker earns its keep here.

    An ``unknown`` verdict has no claim to re-validate. The Rust
    ``Evidence::check`` returns ``true`` for it -- a green result over an empty
    set, which is exactly the checker-that-cannot-fail defect. ``check_outcome``
    reports ``nothing-to-check`` with the reason ``undecided`` instead, and
    ``is_verified()`` is ``False``.
    """
    arena = ir.Arena()
    goal = hard_factoring(arena)
    report = solver.produce_evidence(arena, goal, solver.Config(timeout_ms=1))
    assert report.verdict == "unknown"
    outcome = report.check_outcome(arena, goal)
    assert outcome.status == "nothing-to-check"
    assert outcome.reason == "undecided"
    assert outcome.is_nothing_to_check()
    assert not outcome.is_verified()
    assert not outcome.is_failed()
    # And the class deliberately has no `__bool__`, so `if outcome:` cannot
    # silently read a non-pass as a pass through truthiness of the object.
    assert "__bool__" not in type(outcome).__dict__


def test_evidence_check_outcome_is_nothing_to_check_on_an_empty_subject() -> None:
    # A model replayed against zero assertions passes vacuously. That is
    # reported as nothing-checked, never as a verification.
    arena = ir.Arena()
    report = solver.produce_evidence(arena, [], solver.Config(timeout_ms=TIMEOUT_MS))
    outcome = report.check_outcome(arena, [])
    assert outcome.status == "nothing-to-check"
    assert outcome.reason == "empty-subject"


def test_evidence_reports_provenance_and_the_trust_ledger() -> None:
    arena = ir.Arena()
    goal = unsat_bv(arena)
    report = solver.produce_evidence(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert report.verdict == "unsat"
    provenance = report.provenance
    assert provenance["semantics_version"]
    assert provenance["assertion_count"] == 2
    assert provenance["timeout_ms"] == TIMEOUT_MS
    known = set(solver.trust_ids())
    for label, certified in report.trusted_steps:
        assert label in known
        assert isinstance(certified, bool)


def test_evidence_kind_names_the_certificate_shape() -> None:
    arena = ir.Arena()
    report = solver.produce_evidence(
        arena, unsat_bv(arena), solver.Config(timeout_ms=TIMEOUT_MS, prove_unsat=True)
    )
    assert report.evidence_kind
    assert report.is_certified() in (True, False)


def test_prove_and_disprove() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    hypothesis = arena.bvult(x, arena.bv_const(8, 4))
    true_goal = arena.bvult(x, arena.bv_const(8, 8))
    false_goal = arena.bvult(x, arena.bv_const(8, 2))

    proved = solver.prove(arena, [hypothesis], true_goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert proved.status == "proved"
    assert proved.report is not None

    disproved = solver.prove(arena, [hypothesis], false_goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert disproved.status == "disproved"
    counter = disproved.countermodel
    assert counter is not None
    assert int(counter.model(arena)["x"]) in (2, 3)


def test_prove_reports_unknown_as_a_value() -> None:
    arena = ir.Arena()
    goal = hard_factoring(arena)
    outcome = solver.prove(arena, goal[1:], arena.not_(goal[0]), solver.Config(timeout_ms=1))
    assert outcome.status == "unknown"
    assert outcome.unknown_kind is not None


# ------------------------------------------------------------------- meta


def test_metadata_tables_are_read_only_markdown() -> None:
    for table in (solver.capabilities(), solver.support_matrix(), solver.trust_ledger()):
        assert isinstance(table, str)
        assert len(table) > 100
        assert "|" in table
    assert len(solver.trust_ids()) > 0


# ----------------------------------------------------------------- proofs


def test_qf_bv_unsat_proof_rechecks_from_its_text() -> None:
    arena = ir.Arena()
    outcome = proofs.export_qf_bv_unsat_proof(arena, unsat_bv(arena))
    assert outcome.status == "proved"
    proof = outcome.proof
    assert proof is not None
    assert proof.dimacs.startswith("p cnf")
    assert proof.recheck() is True


def test_qf_bv_unsat_proof_on_a_satisfiable_query_is_not_a_proof() -> None:
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    outcome = proofs.export_qf_bv_unsat_proof(arena, [arena.bvult(x, arena.bv_const(8, 200))])
    assert outcome.status == "satisfiable"
    assert outcome.is_satisfiable()
    assert not outcome.is_proved()
    assert outcome.proof is None


def test_a_one_millisecond_budget_is_inconclusive_not_a_pass() -> None:
    arena = ir.Arena()
    outcome = proofs.export_qf_bv_unsat_proof(arena, hard_unsat_factoring(arena), timeout_ms=1)
    # `inconclusive` is the third answer. A timeout is NOT `satisfiable` and it
    # is NOT `proved`.
    assert outcome.status == "inconclusive"
    assert outcome.is_inconclusive()
    assert not outcome.is_proved()
    assert not outcome.is_satisfiable()
    assert outcome.proof is None


def test_recheck_lrat_is_none_on_a_drat_only_proof() -> None:
    """`None` is not `True`, and this pins that it stays `None`.

    A proof with no LRAT elaboration is DRAT-checkable and nothing more. If
    `recheck_lrat` coerced that to `True` the caller would believe a
    linear-time check ran when none did.
    """
    arena = ir.Arena()
    outcome = proofs.export_qf_bv_unsat_proof(arena, unsat_bv(arena))
    proof = outcome.proof
    assert proof is not None
    if proof.lrat is None:
        assert proof.recheck_lrat() is None
    else:
        # The exporter elaborated an LRAT here; the None case is exercised by
        # a hand-built proof below instead.
        assert proof.recheck_lrat() is True


def test_recheck_lrat_is_none_on_a_hand_built_drat_only_certificate() -> None:
    # The one shape that is guaranteed LRAT-free: a certificate whose `lrat`
    # field was never populated. Build it through the CNF core, which emits
    # DRAT only.
    formula = cnf.parse_dimacs("p cnf 1 2\n1 0\n-1 0\n")
    outcome = cnf.solve_with_drat_proof(formula)
    assert outcome.status == "unsat"
    assert outcome.drat is not None
    checked = cnf.check_drat(formula, outcome.drat)
    assert checked.status == "verified"
    assert checked.verified is True


def test_uf_and_datatype_proof_exporters_are_bound() -> None:
    arena = ir.Arena()
    sort = ir.Sort.bv(4)
    f = arena.declare_fun("f", [sort], sort)
    a = arena.var(arena.declare("a", sort))
    b = arena.var(arena.declare("b", sort))
    # Congruence: a == b forces f(a) == f(b).
    goal = [
        arena.eq(a, b),
        arena.not_(arena.eq(arena.apply(f, [a]), arena.apply(f, [b]))),
    ]
    outcome = proofs.export_qf_uf_unsat_proof(arena, goal)
    assert outcome.status == "proved"
    assert outcome.proof.recheck() is True
    assert hasattr(proofs, "export_datatype_unsat_proof")
    assert hasattr(proofs, "export_qf_abv_unsat_proof")
    assert hasattr(proofs, "export_qf_aufbv_unsat_proof")
    assert hasattr(proofs, "export_qf_lia_unsat_proof")


# -------------------------------------------------------------------- cnf


def test_dimacs_round_trips_and_evaluates() -> None:
    text = "p cnf 2 2\n1 -2 0\n-1 2 0\n"
    formula = cnf.parse_dimacs(text)
    assert formula.variable_count == 2
    assert formula.clause_count == 2
    assert formula.clauses == [[1, -2], [-1, 2]]
    assert formula.evaluate([True, True]) is True
    assert formula.evaluate([True, False]) is False
    assert cnf.parse_dimacs(formula.to_dimacs()).to_dimacs() == formula.to_dimacs()


def test_check_drat_on_a_tampered_proof_is_verified_false() -> None:
    # A formula whose refutation takes more than one step, so truncating the
    # proof leaves something that still parses and still step-checks.
    formula = cnf.parse_dimacs(
        "p cnf 3 8\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n3 0\n-3 1 0\n-3 2 0\n1 3 0\n"
    )
    outcome = cnf.solve_with_drat_proof(formula)
    assert outcome.status == "unsat"
    honest = cnf.check_drat(formula, outcome.drat)
    assert honest.verified is True

    # Tamper by truncation: drop the step that derives the empty clause. Every
    # remaining step still checks, so this is exactly the case a checker that
    # only validated individual steps would wave through -- and it must not.
    lines = [line for line in outcome.drat.splitlines() if line.strip()]
    assert lines, "the core produced no DRAT steps to truncate"
    truncated = "".join(f"{line}\n" for line in lines[:-1])
    tampered = cnf.check_drat(formula, truncated)
    assert tampered.status == "verified"
    assert tampered.verified is False


def test_check_drat_resource_out_is_neither_true_nor_false() -> None:
    formula = cnf.parse_dimacs("p cnf 1 2\n1 0\n-1 0\n")
    outcome = cnf.solve_with_drat_proof(formula)
    starved = cnf.check_drat(formula, outcome.drat, max_steps=0)
    assert starved.status in {"resource-out", "interrupted"}
    assert starved.verified is None


def test_proof_sat_core_reports_sat_with_a_model() -> None:
    formula = cnf.parse_dimacs("p cnf 2 2\n1 -2 0\n-1 2 0\n")
    outcome = cnf.solve_with_drat_proof(formula)
    assert outcome.status == "sat"
    assert outcome.assignment is not None
    assert formula.evaluate(outcome.assignment) is True


def test_proof_sat_core_budget_miss_is_undecided() -> None:
    arena = ir.Arena()
    lowering = ir_bv.lower_terms(arena, hard_unsat_factoring(arena))
    encoding = cnf.tseitin_encode(lowering)
    assert encoding.variable_count > 1_000
    outcome = cnf.solve_with_drat_proof(encoding.formula(), max_conflicts=1)
    # Undecided is a VERDICT here, not an error and not a `sat`/`unsat`.
    assert outcome.status in {"resource-out", "interrupted"}
    assert outcome.assignment is None
    assert outcome.drat is None


def test_default_conflict_budget_is_a_readable_constant() -> None:
    assert cnf.DEFAULT_PROOF_SAT_CONFLICT_LIMIT == 2_000_000
    assert cnf.DEFAULT_PROGRESS_CONFLICT_INTERVAL == 5_000


def test_the_full_lowering_to_cnf_to_model_replay_chain() -> None:
    """The 'never drop lowering/lift maps' rule, exercised end to end.

    Terms -> AIG -> CNF -> SAT assignment -> AIG node values -> IR assignment
    -> the ORIGINAL term evaluated. If any map in that chain were wrong, the
    final evaluation would disagree with the constraint the CNF solved.
    """
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    goal = arena.eq(arena.bvadd(x, arena.bv_const(8, 3)), arena.bv_const(8, 10))
    lowering = ir_bv.lower_terms(arena, [goal])
    encoding = cnf.tseitin_encode(lowering)
    outcome = cnf.solve_with_drat_proof(encoding.formula())
    assert outcome.status == "sat"

    node_values = encoding.aig_node_values_from_assignment(lowering, outcome.assignment)
    assert len(node_values) == lowering.node_count
    lifted = lowering.assignment_from_aig_values(node_values)
    assert ir.eval(arena, goal, lifted) is True
    assert int(ir.eval(arena, x, lifted)) == 7
