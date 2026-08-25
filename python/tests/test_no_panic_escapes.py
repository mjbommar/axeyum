"""No Rust panic may reach a Python caller as a `BaseException`.

# Why this is a distinct property, not "it raises something"

`PyO3` turns a Rust `panic!` into `pyo3_runtime.PanicException`, and that class
derives from **`BaseException`**, not `Exception`. So a caller who wrote the
ordinary thing --

    try:
        arena.real_ratio(1, 0)
    except Exception:
        ...

-- does not catch it. The traceback escapes to the top, the process usually
dies, and the message is a Rust internal ("rational denominator must be
non-zero", naming a file the caller has never heard of). Every test below
therefore asserts two separate things: the *specific* type raised, and that the
type is an `Exception` subclass. The second assertion is the one that fails if a
guard is deleted, because a panic still "raises".

`PanicException` is imported here on purpose, and only to prove the distinction
is real. A test that could not name the wrong answer is not measuring anything.

# The measured population

`tools/panic_probe.py` walks every public callable in `axeyum._native` and calls
it with an adversarial argument battery. Before the guards below it reported
`panics=3` and `segfaults=19`; after, `panics=0`. The full census lives in
`docs/plan/generated/panic-probe.md` and the reasoning in
`docs/python-2026-08/13-panic-surface.md`. `test_probe_targeted_battery_is_panic_free`
re-runs the adversarial scenarios in-process on every pytest run, so a
regression that re-introduces a panic fails the suite rather than waiting for
someone to run the tool.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import pytest

import axeyum
from axeyum import cas, ir, kernel, smt, solver

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import panic_probe  # (import follows the sys.path insert above)

REPORT = REPO_ROOT / "docs" / "plan" / "generated" / "panic-probe.md"


def assert_ordinary(error: BaseException) -> None:
    """The exception must be catchable by `except Exception`.

    This is the whole property. `PanicException` is a `BaseException` that is
    NOT an `Exception`, so this assertion is exactly the one a re-introduced
    panic fails -- and the only one, since a panic does raise.
    """
    assert isinstance(error, Exception), (
        f"{type(error).__module__}.{type(error).__name__} is a BaseException that is not an "
        "Exception, so `except Exception` does not catch it"
    )
    assert not panic_probe._is_panic(error), f"a Rust panic reached Python: {error}"


# --- the distinction this file exists to enforce is real ----------------------
#
# `pyo3_runtime` is NOT importable here, and that is the good news rather than a
# problem: PyO3 registers the module lazily, the first time it converts a panic.
# A successful `import pyo3_runtime` in this process would mean a panic had
# already happened. So the control below builds a stand-in with the same module
# and class name -- which is exactly what `_is_panic` keys on -- and proves that
# `assert_ordinary` REJECTS it. Without this, every `assert_ordinary` call in
# the file could be vacuous and nothing would say so.


class PanicException(BaseException):
    """A stand-in for `pyo3_runtime.PanicException`.

    Same name, same `__module__`, and the same relationship to `Exception`:
    derived from `BaseException` and NOT from `Exception`. That is the whole
    property under test, so a stand-in is a faithful subject for the control.
    """


PanicException.__module__ = "pyo3_runtime"


def test_a_panic_would_be_rejected_by_the_assertions_in_this_file():
    """The negative control. Without it, every assertion here could be vacuous.

    A `PanicException` raises, so a test that only checked "something was
    raised" would pass on a re-introduced panic. This pins the two checks that
    would not.
    """
    panic = PanicException("synthetic")
    assert isinstance(panic, BaseException)
    assert not isinstance(panic, Exception)
    assert panic_probe._is_panic(panic), (
        "the probe's classifier stopped recognizing a PanicException; every "
        "`panics=` count it prints is now meaningless"
    )
    with pytest.raises(AssertionError):
        assert_ordinary(panic)


def test_pyo3_runtime_is_absent_because_nothing_has_panicked():
    """PyO3 creates `pyo3_runtime` only when it first converts a panic.

    Its absence after this module has exercised every guarded site is direct
    evidence that no panic was converted. If it ever IS importable here, some
    call in this process panicked and the census needs re-running.
    """
    assert "pyo3_runtime" not in sys.modules, (
        "pyo3_runtime is loaded, so a Rust panic was converted in this process"
    )


# --- `Rational::checked_new` keeps `new`'s `assert!(den != 0)` ---------------
#
# Four binding call sites passed a caller-supplied denominator to
# `Rational::checked_new` believing the name meant "returns None instead of
# panicking". It does not: it is graceful about i128 OVERFLOW only, and asserts
# on a zero denominator. The probe found the first of these; the other three
# need argument shapes a generic pool does not produce.


def test_real_ratio_zero_denominator_is_a_value_error():
    arena = ir.Arena()
    with pytest.raises(ValueError) as caught:
        arena.real_ratio(1, 0)
    assert_ordinary(caught.value)
    assert "non-zero" in str(caught.value)


def test_set_real_div_zero_numerator_denominator_is_a_value_error():
    arena = ir.Arena()
    with pytest.raises(ValueError) as caught:
        arena.assignment().set_real_div_zero((1, 0), (1, 1))
    assert_ordinary(caught.value)


def test_set_real_div_zero_quotient_denominator_is_a_value_error():
    arena = ir.Arena()
    with pytest.raises(ValueError) as caught:
        arena.assignment().set_real_div_zero((1, 1), (1, 0))
    assert_ordinary(caught.value)


class ZeroDenominator:
    """Not a `Fraction`, but `py_to_value` accepts anything with the pair.

    `fractions.Fraction` can never present a zero denominator, which is why this
    site looked safe. Duck typing is what reaches it.
    """

    numerator = 1
    denominator = 0


def test_assignment_set_real_with_a_zero_denominator_is_a_sort_error():
    arena = ir.Arena()
    symbol = arena.declare("r", ir.Sort.real())
    assignment = arena.assignment()
    with pytest.raises(ir.SortError) as caught:
        assignment.set(arena, symbol, ZeroDenominator())
    assert_ordinary(caught.value)


def test_assignment_set_real_still_accepts_an_ordinary_fraction():
    """The positive control for the guard above: it must not refuse valid input."""
    arena = ir.Arena()
    symbol = arena.declare("r", ir.Sort.real())
    assignment = arena.assignment()
    assignment.set(arena, symbol, Fraction(3, 4))
    assert ir.eval(arena, arena.var(symbol), assignment) == Fraction(3, 4)


def test_fp_from_real_zero_denominator_is_a_value_error():
    arena = ir.Arena()
    with pytest.raises(ValueError) as caught:
        ir.fp.from_real(arena, ir.fp.F32, ir.fp.RoundingMode.NearestTiesToEven, 1, 0)
    assert_ordinary(caught.value)


def test_fp_from_real_still_converts_a_representable_rational():
    arena = ir.Arena()
    term = ir.fp.from_real(arena, ir.fp.F32, ir.fp.RoundingMode.NearestTiesToEven, 1, 2)
    assert term is not None


# --- the tree-recursive text routines overflow the stack, which ABORTS -------
#
# `axeyum_ir::render` and `axeyum_smtlib::write_script` recurse once per node.
# Beyond ~16k deep on an 8 MB stack the process dies with SIGABRT -- not a
# `PanicException`, so no `except` of any kind can see it. The binding refuses
# above a budget instead.


def deep_term(arena: ir.Arena, depth: int):
    """A `bvnot` chain `depth` deep."""
    term = arena.bv_const(8, 1)
    for _ in range(depth):
        term = arena.bvnot(term)
    return term


def test_render_of_a_too_deep_term_is_a_budget_exceeded():
    arena = ir.Arena()
    term = deep_term(arena, 40_000)
    with pytest.raises(axeyum.BudgetExceeded) as caught:
        arena.render(term)
    assert_ordinary(caught.value)
    assert "recurses once per node" in str(caught.value)


def test_arena_write_script_of_a_too_deep_term_is_a_budget_exceeded():
    arena = ir.Arena()
    term = deep_term(arena, 40_000)
    with pytest.raises(axeyum.BudgetExceeded) as caught:
        arena.write_script([arena.eq(term, term)])
    assert_ordinary(caught.value)


def test_smt_write_script_of_a_too_deep_term_is_a_budget_exceeded():
    arena = ir.Arena()
    term = deep_term(arena, 40_000)
    with pytest.raises(axeyum.BudgetExceeded) as caught:
        smt.write_script(arena, [arena.eq(term, term)])
    assert_ordinary(caught.value)


def test_render_under_the_budget_still_works():
    """The positive control: the budget must not refuse ordinary terms."""
    arena = ir.Arena()
    term = deep_term(arena, 4_000)
    assert arena.render(term).count("bvnot") == 4_000


# --- an allocation the Rust allocator would ABORT on -------------------------


def test_matrix_identity_above_the_entry_budget_is_a_value_error():
    with pytest.raises(ValueError) as caught:
        cas.Matrix.identity(70_000)
    assert_ordinary(caught.value)
    assert "binding budget" in str(caught.value)


def test_matrix_zeros_above_the_entry_budget_is_a_value_error():
    with pytest.raises(ValueError) as caught:
        cas.Matrix.zeros(70_000, 70_000)
    assert_ordinary(caught.value)


def test_matrix_within_the_budget_still_builds():
    assert cas.Matrix.identity(4).rows == 4


# --- the one site where no preflight was possible ----------------------------


def test_cpoint_prelude_returns_instead_of_killing_the_interpreter():
    """`build_cpoint_prelude` overflowed the 8 MB main-thread stack.

    It took CPython down with SIGSEGV -- silently, with no traceback and no
    `PanicException` -- on a call with NO arguments, from a pristine kernel.
    There is nothing to preflight, so the fix is a thread with room for the
    recursion; `join()` is what turns a panic inside it into a typed
    `InternalError` without `catch_unwind`.

    This test is the whole guard: if the deep stack is removed, the process
    dies and pytest reports a crashed worker rather than a failure.
    """
    prelude = kernel.Kernel().build_cpoint_prelude()
    assert prelude.kind == "cpoint"
    assert len(prelude.field_names) > 0


def test_internal_error_is_an_ordinary_exception_under_axeyum_error():
    """The type a caught panic is converted to must itself be catchable."""
    assert issubclass(axeyum.InternalError, axeyum.AxeyumError)
    assert issubclass(axeyum.InternalError, Exception)
    assert not panic_probe._is_panic(axeyum.InternalError("x"))


# --- the dispatcher route where a preflight was NOT possible -----------------
#
# `(= s1 s2)` over two `String` symbols reached `axeyum-bv`'s
# `unreachable!("sequence terms are rejected before bit lowering")` through the
# multi-theory dispatcher. A sort preflight cannot fix it: the two tests below
# use the SAME sort and only one of them is fatal, so refusing sequences up
# front would break the other. The panic is caught at the dispatch call and
# retyped; `test_string_length_query_is_still_answered` is the control that
# says the fix did not become a blanket refusal.


def string_equality(arena: ir.Arena):
    left = arena.var(arena.declare("s0", ir.Sort.string()))
    right = arena.var(arena.declare("s1", ir.Sort.string()))
    return arena.eq(left, right)


@pytest.mark.parametrize("route", ["solve", "check_auto_explained", "unsat_core"])
def test_string_equality_through_the_dispatcher_is_an_internal_error(route: str):
    arena = ir.Arena()
    term = string_equality(arena)
    call = getattr(solver, route)
    with pytest.raises(axeyum.InternalError) as caught:
        call(arena, [term], solver.Config(timeout_ms=200))
    assert_ordinary(caught.value)
    assert "panicked" in str(caught.value)
    assert "bug in Axeyum" in str(caught.value)


def test_string_length_query_is_still_answered():
    """The control: a sequence term the dispatcher HANDLES must still be handled.

    This is what makes the fix a caught panic rather than a sort preflight. If
    somebody replaces the `catch_unwind` with "refuse anything with a sequence
    sort", this test fails.
    """
    arena = ir.Arena()
    symbol = arena.var(arena.declare("s", ir.Sort.string()))
    term = arena.eq(arena.seq_len(symbol), arena.int_const(1))
    try:
        result = solver.solve(arena, [term], solver.Config(timeout_ms=2_000))
    except axeyum.InternalError:  # pragma: no cover - would be the regression
        pytest.fail("a query the dispatcher handles was reported as an internal error")
    except axeyum.AxeyumError:
        return  # a typed refusal from the solver is a legitimate outcome
    assert result.status in {"sat", "unsat", "unknown"}


def test_ordinary_bitvector_query_is_unaffected():
    """The broadest control: the catch must not change any normal verdict."""
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    result = solver.solve(arena, [arena.eq(x, arena.bv_const(8, 3))], solver.Config())
    assert result.status == "sat"


# --- the meta-test: the probe's own adversarial battery ----------------------


def test_probe_targeted_battery_is_panic_free():
    """Every hand-written adversarial scenario returns or raises an `Exception`.

    This is the regression gate. It runs the same battery `tools/panic_probe.py`
    runs -- the cross-arena handles, the cross-kernel handles, the degenerate
    widths, the by-zero operators, the out-of-range extracts, the mis-lifted
    assignments -- in-process, so re-introducing a panic anywhere they reach
    fails the suite.

    Two scenarios are excluded by name, and only two: `cas.Expr.__add__` and
    `cas.normalize` at depth 50,000 still ABORT the process (a recursive
    `Clone`/`Drop` over a boxed chain inside `axeyum-cas`, not a panic -- see
    `docs/python-2026-08/13-panic-surface.md`). Running them here would kill the
    pytest process rather than fail a test.
    """
    specimens = panic_probe.build_specimens(axeyum._native)
    cases = panic_probe.targeted_cases(axeyum._native, specimens)

    excluded = {
        ("cas.Expr.__add__", "targeted:depth=50000"),
        ("cas.normalize", "targeted:depth=50000"),
    }
    escapes: list[str] = []
    ran = 0
    raised = 0
    for target, label, thunk in cases:
        if (target, label) in excluded:
            continue
        ran += 1
        try:
            thunk()
        except Exception:  # noqa: BLE001 - a typed exception is the contract
            raised += 1
        except BaseException as error:  # noqa: BLE001
            kind = f"{type(error).__module__}.{type(error).__name__}"
            escapes.append(f"{target} [{label}] -> {kind}: {error}")

    assert not escapes, "calls that escaped `except Exception`:\n" + "\n".join(escapes)
    # A battery that ran nothing, or one where nothing was refused, would pass
    # the assertion above while measuring nothing. Both are asserted.
    assert ran >= 150, f"the adversarial battery shrank to {ran} cases"
    assert raised >= 50, f"only {raised} of {ran} adversarial calls were refused at all"


def test_committed_probe_report_records_zero_panics():
    """The generated census must agree that the panic surface is closed."""
    assert REPORT.exists(), f"{REPORT} is missing; run tools/panic_probe.py --write"
    text = REPORT.read_text(encoding="utf-8")
    headline = next(
        line.strip() for line in text.splitlines() if line.strip().startswith("PANIC_PROBE|")
    )
    fields = dict(part.split("=", 1) for part in headline.split("|")[1:])
    assert int(fields["panics"]) == 0, headline
    # The count is only meaningful if the probe actually made calls.
    assert int(fields["probed"]) > 10_000, headline
    assert int(fields["callables"]) > 1_000, headline
