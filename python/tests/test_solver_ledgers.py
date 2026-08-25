"""The read-only solver ledgers (tier R) as STRUCTURED data, not Markdown.

Slice S1 of `docs/python-2026-08/09-coverage-plan.md`. The point of the slice is
that a Markdown table is a *rendering*: a caller asking "which capabilities does
an external checker read?" had to regex a table, and a regex that matches
nothing looks exactly like a table with no such rows -- the empty-result trap
this repository keeps paying for.

So every assertion below is written against the structured rows AND cross-checked
against the Markdown the same build renders. A structured list that silently
dropped rows, or a Markdown renderer that silently gained them, fails here.

Two distinctions the tests refuse to let collapse:

* ``assurance`` (is there a certificate?) and ``checked_by`` (who reads it?);
* a ``TrustStep``'s per-run ``certified`` and the ledger-wide
  ``ledger_certified``.
"""

from __future__ import annotations

import pytest

from axeyum import ir, smt, solver

TIMEOUT_MS = 20_000

# Exact populations of the two Rust consts, pinned. A count that drifts is a
# real change to what this build claims it can do, and it should have to be
# written down here. Nonzero is asserted separately -- a ledger that renders
# zero rows and a ledger nobody pointed at the subject are the same observation.
CAPABILITY_ROWS = 105
SUPPORT_MATRIX_ROWS = 19
TRUST_LEDGER_ROWS = 14


def markdown_table_rows(markdown: str, header_prefix: str) -> list[str]:
    """The body rows of the Markdown table whose header starts with `header_prefix`."""
    lines = markdown.splitlines()
    for index, line in enumerate(lines):
        if line.startswith(header_prefix):
            body = lines[index + 2 :]
            return [row for row in body if row.startswith("|")]
    raise AssertionError(f"no table header starting {header_prefix!r}")


# --------------------------------------------------------------------------
# capabilities::CAPABILITIES
# --------------------------------------------------------------------------


def test_capability_rows_are_structured_not_markdown() -> None:
    rows = solver.capability_rows()
    assert isinstance(rows, list)
    assert not isinstance(rows[0], str)
    assert isinstance(solver.capabilities(), str)


def test_capability_row_count_is_exact_and_nonzero() -> None:
    rows = solver.capability_rows()
    assert len(rows) == CAPABILITY_ROWS
    assert CAPABILITY_ROWS > 0


def test_capability_row_count_equals_the_rendered_table() -> None:
    rendered = markdown_table_rows(solver.capabilities(), "| Area | Capability |")
    assert len(rendered) == len(solver.capability_rows()) == CAPABILITY_ROWS


def test_every_capability_id_appears_in_the_markdown() -> None:
    markdown = solver.capabilities()
    missing = [row.id for row in solver.capability_rows() if f"| {row.id} |" not in markdown]
    assert missing == []


def test_every_capability_renders_as_a_full_markdown_row() -> None:
    markdown = solver.capabilities()
    for row in solver.capability_rows():
        rendered = (
            f"| {row.area} | {row.feature} | {row.assurance} "
            f"| {row.checked_by} | {row.evidence} | {row.reference} |"
        )
        assert rendered in markdown, row.id


def test_capability_id_is_the_area_feature_pair() -> None:
    row = solver.capability_rows()[0]
    assert row.id == f"{row.area} | {row.feature}"
    assert row.area and row.feature


def test_capability_assurance_and_checked_by_are_separate_axes() -> None:
    rows = solver.capability_rows()
    assert {row.assurance for row in rows} <= set(solver.ASSURANCES)
    assert {row.checked_by for row in rows} <= set(solver.CHECKED_BY)
    # The two axes are independent: `checked` is claimed by rows with more than
    # one `checked_by`, so neither field can be derived from the other.
    checked = {row.checked_by for row in rows if row.assurance == "checked"}
    assert len(checked) > 1


def test_capability_external_checker_rows_exist_and_are_a_minority() -> None:
    rows = solver.capability_rows()
    external = [row for row in rows if row.checked_by == "external-artifact-checker"]
    assert external, "no row claims an external checker -- the field would be decoration"
    assert len(external) < len(rows)


def test_capability_rows_are_frozen() -> None:
    row = solver.capability_rows()[0]
    with pytest.raises(AttributeError):
        row.assurance = "checked"


def test_capability_labels_cover_every_rust_variant() -> None:
    assert solver.ASSURANCES == [
        "checked",
        "validated",
        "sound, incomplete",
        "experimental",
    ]
    assert solver.CHECKED_BY == [
        "external-artifact-checker",
        "self-checker",
        "differential-only",
        "argument-only",
    ]


# --------------------------------------------------------------------------
# support_matrix::SUPPORT_MATRIX
# --------------------------------------------------------------------------


def test_support_matrix_row_count_is_exact_and_nonzero() -> None:
    rows = solver.support_matrix_rows()
    assert len(rows) == SUPPORT_MATRIX_ROWS
    assert SUPPORT_MATRIX_ROWS > 0


def test_support_matrix_row_count_equals_the_rendered_table() -> None:
    rendered = markdown_table_rows(solver.support_matrix(), "| Fragment |")
    assert len(rendered) == len(solver.support_matrix_rows()) == SUPPORT_MATRIX_ROWS


def test_every_support_row_renders_as_a_markdown_row() -> None:
    markdown = solver.support_matrix()
    for row in solver.support_matrix_rows():
        rendered = f"| {row.fragment} | {row.parser} | {row.ir} | {row.solver} | {row.proof} |"
        assert rendered in markdown, row.fragment


def test_support_statuses_are_drawn_from_the_four_label_sets() -> None:
    rows = solver.support_matrix_rows()
    assert {row.parser for row in rows} <= set(solver.PARSER_STATUSES)
    assert {row.ir for row in rows} <= set(solver.IR_STATUSES)
    assert {row.solver for row in rows} <= set(solver.SOLVER_STATUSES)
    assert {row.proof for row in rows} <= set(solver.PROOF_STATUSES)


def test_support_axes_are_independent() -> None:
    """A fragment the parser accepts is not thereby decided or proved."""
    rows = solver.support_matrix_rows()
    accepted = [row for row in rows if row.parser == "accepted"]
    assert accepted
    assert any(row.solver != "decides" or row.proof != "checked" for row in accepted)


def test_support_rows_carry_a_grounding_note() -> None:
    for row in solver.support_matrix_rows():
        assert row.note.strip(), row.fragment


def test_support_rows_are_frozen() -> None:
    row = solver.support_matrix_rows()[0]
    with pytest.raises(AttributeError):
        row.proof = "checked"


# --------------------------------------------------------------------------
# trust::ALL_TRUST_IDS
# --------------------------------------------------------------------------


def test_trust_ledger_row_count_is_exact_and_matches_trust_ids() -> None:
    rows = solver.trust_ledger_rows()
    assert len(rows) == TRUST_LEDGER_ROWS
    assert [row.id for row in rows] == list(solver.trust_ids())


def test_trust_rows_render_into_the_ledger_markdown() -> None:
    markdown = solver.trust_ledger()
    for row in solver.trust_ledger_rows():
        rendered = (
            f"| {row.id} | {row.meaning} | {row.pedantic_level} | {row.status} | {row.reference} |"
        )
        assert rendered in markdown, row.id


def test_trust_hole_count_agrees_with_the_rendered_headline() -> None:
    holes = [row for row in solver.trust_ledger_rows() if not row.ledger_certified]
    assert holes, "a ledger with no trust holes would be the claim to check hardest"
    assert f"Trusted base: **{len(holes)}** reduction(s) remain trust holes." in (
        solver.trust_ledger()
    )


def test_static_ledger_certified_equals_ledger_certified() -> None:
    """The static ledger carries no per-run information, and says so."""
    for row in solver.trust_ledger_rows():
        assert row.certified == row.ledger_certified, row.id
        assert row.status == ("certified" if row.ledger_certified else "trust hole")


def test_trust_pedantic_levels_are_graded() -> None:
    levels = {row.pedantic_level for row in solver.trust_ledger_rows()}
    assert levels <= set(range(11))
    assert len(levels) > 1, "a single grade would make the axis decoration"


def test_evidence_report_trust_steps_agree_with_the_tuple_form() -> None:
    """A Farkas refutation of `x > 1 and x < 0` records the reduction it used."""
    arena = ir.Arena()
    x = arena.real_var("x")
    report = solver.produce_evidence(
        arena,
        [arena.real_gt(x, arena.real_const(1)), arena.real_lt(x, arena.real_const(0))],
        solver.Config(timeout_ms=TIMEOUT_MS, prove_unsat=True),
    )
    assert report.verdict == "unsat"
    steps = report.trust_steps
    assert steps, "an unsat that names no trusted reduction cannot be audited"
    assert [(step.id, step.certified) for step in steps] == list(report.trusted_steps)
    for step in steps:
        assert step.meaning and step.reference
        assert isinstance(step.ledger_certified, bool)


def test_evidence_trust_steps_carry_the_ledger_metadata() -> None:
    arena = ir.Arena()
    x = arena.real_var("x")
    report = solver.produce_evidence(
        arena,
        [arena.real_gt(x, arena.real_const(1)), arena.real_lt(x, arena.real_const(0))],
        solver.Config(timeout_ms=TIMEOUT_MS, prove_unsat=True),
    )
    (step,) = report.trust_steps
    assert step.id == "farkas"
    assert step.certified is True
    assert step.reference == "ADR-0015"
    ledger = {row.id: row for row in solver.trust_ledger_rows()}
    assert step.ledger_certified == ledger[step.id].ledger_certified
    assert step.meaning == ledger[step.id].meaning


# --------------------------------------------------------------------------
# backend::Capabilities and backend::SolveStats
# --------------------------------------------------------------------------


def test_backend_capabilities_are_structured() -> None:
    capabilities = solver.SatBvBackend().capabilities()
    assert "axeyum-sat-bv" in capabilities.name
    assert capabilities.produces_models is True
    assert capabilities.complete is True


def test_last_stats_is_none_before_any_check() -> None:
    """`None` is the value, not an empty `SolveStats` reading as a zero-time run."""
    assert solver.SatBvBackend().last_stats() is None


def test_last_stats_after_a_check_reports_every_field() -> None:
    backend = solver.SatBvBackend()
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    result = backend.check(arena, [arena.eq(x, arena.bv_const(8, 3))])
    assert result.status == "sat"
    stats = backend.last_stats()
    assert stats is not None
    assert stats.assertion_count == 1
    assert stats.terms_translated > 0
    assert stats.solve_ns > 0
    assert stats.translate_ns >= 0
    assert stats.model_lift_ns >= 0


def test_solve_stats_seconds_and_nanoseconds_agree() -> None:
    backend = solver.SatBvBackend()
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    backend.check(arena, [arena.eq(x, arena.bv_const(8, 3))])
    stats = backend.last_stats()
    assert stats is not None
    for seconds, nanos in (
        (stats.translate_seconds, stats.translate_ns),
        (stats.solve_seconds, stats.solve_ns),
        (stats.model_lift_seconds, stats.model_lift_ns),
    ):
        assert seconds == pytest.approx(nanos / 1e9, rel=1e-9, abs=1e-12)


def test_solve_stats_backend_counters_are_named_floats() -> None:
    backend = solver.SatBvBackend()
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    backend.check(arena, [arena.eq(x, arena.bv_const(8, 3))])
    stats = backend.last_stats()
    assert stats is not None
    for name, value in stats.backend:
        assert isinstance(name, str)
        assert isinstance(value, float)


def test_solve_stats_is_frozen() -> None:
    backend = solver.SatBvBackend()
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    backend.check(arena, [arena.eq(x, arena.bv_const(8, 3))])
    stats = backend.last_stats()
    assert stats is not None
    with pytest.raises(AttributeError):
        stats.assertion_count = 0


def test_backend_unknown_is_a_value_not_an_exception() -> None:
    backend = solver.SatBvBackend()
    arena = ir.Arena()
    a = arena.bv_var("a", 64)
    b = arena.bv_var("b", 64)
    one = arena.bv_const(64, 1)
    result = backend.check(
        arena,
        [
            arena.eq(arena.bvmul(a, b), arena.bv_const(64, 3_369_738_766_071_892_021)),
            arena.bvugt(a, one),
            arena.bvugt(b, one),
        ],
        solver.Config(timeout_ms=1),
    )
    assert result.status == "unknown"
    assert result.unknown_kind is not None


# --------------------------------------------------------------------------
# smtlib.rs: get-assertions / get-info / get-option
# --------------------------------------------------------------------------

SCOPED_SCRIPT = """(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #b0001))
(get-assertions)
(push 1)
(assert (bvult x #b1000))
(get-assertions)
(pop 1)
(get-assertions)
"""


def test_get_assertions_returns_the_texts_in_order() -> None:
    snapshots = smt.get_assertions(SCOPED_SCRIPT)
    assert snapshots == [
        ["(= x (_ bv1 4))"],
        ["(= x (_ bv1 4))", "(bvult x (_ bv8 4))"],
        ["(= x (_ bv1 4))"],
    ]


def test_get_assertions_is_none_when_the_script_asks_for_none() -> None:
    """`None` means "no snapshot requested", not "no assertions"."""
    assert smt.get_assertions("(declare-const x (_ BitVec 4))(assert (= x #b0001))(check-sat)") is (
        None
    )


def test_get_option_echoes_a_set_option() -> None:
    answers = smt.get_option(
        "(set-option :produce-models true)(get-option :produce-models)(get-option :random-seed)"
    )
    assert answers == [(":produce-models", "true"), (":random-seed", "0")]


def test_get_option_reports_an_unknown_key_as_unsupported() -> None:
    """Unsupported and absent are different answers; neither is dropped."""
    answers = smt.get_option("(get-option :no-such-option)")
    assert answers == [(":no-such-option", "unsupported")]
    assert smt.get_option("(check-sat)") is None


def test_get_info_reason_unknown_after_an_unknown_returns_a_reason() -> None:
    script = """(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))
(assert (= (bvmul a b) (_ bv3369738766071892021 64)))
(assert (bvugt a (_ bv1 64)))
(assert (bvugt b (_ bv1 64)))
(check-sat)
(get-info :reason-unknown)
"""
    assert smt.solve(script, timeout_ms=1).status == "unknown"
    answers = smt.get_info(script, timeout_ms=1)
    assert answers is not None
    reasons = dict(answers)
    reason = reasons[":reason-unknown"]
    assert reason not in ("", '""'), "a decided-shaped answer for an undecided query"
    assert reason.strip()


def test_get_info_reason_unknown_is_empty_when_the_query_was_decided() -> None:
    answers = smt.get_info(
        "(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b0001))"
        "(check-sat)(get-info :reason-unknown)",
        timeout_ms=TIMEOUT_MS,
    )
    assert answers == [(":reason-unknown", '""')]


def test_get_info_keeps_recorded_values_and_flags_unknown_keys() -> None:
    answers = smt.get_info(
        "(set-info :source |a source|)(get-info :name)(get-info :source)(get-info :nope)"
    )
    assert answers is not None
    keys = [key for key, _ in answers]
    assert keys == [":name", ":source", ":nope"]
    values = dict(answers)
    assert "axeyum" in values[":name"]
    assert values[":source"] == "a source"
    assert values[":nope"] == "unsupported"
    assert smt.get_info("(check-sat)") is None
