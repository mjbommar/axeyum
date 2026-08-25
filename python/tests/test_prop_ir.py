"""Hypothesis differential: the trusted IR evaluator against a Python reference.

``axeyum_ir::eval`` is the checker every ``sat`` in this repository is replayed
against, so a wrong value here is not a wrong answer in one route -- it is a
checker that certifies wrong answers. This file re-implements its semantics
independently, in Python, from the SMT-LIB definitions, and compares the two on
random inputs.

The reference is written from the standard, and each function cites both the
SMT-LIB source of the convention and the line of ``crates/axeyum-ir/src/eval.rs``
that implements it, so a reader can check the two against each other without
running anything. Where the standard leaves an operation *underspecified* the
citation names the convention the IR picked -- that is exactly where a
reference written from a vague memory of C semantics would disagree.

**Degenerate arguments are generated deliberately** (the fuzz-seed-class hard
rule in CLAUDE.md): the operand strategy mixes ``0``, ``1``, all-ones and the
signed minimum into every draw, and the by-zero cases are additionally pinned by
non-random tests below, because a differential that structurally cannot produce
``(bvudiv x 0)`` is blind on the axis where soundness is most fragile (a
wrong-unsat shipped that way once -- ``a946f925``).
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import pytest
from hypothesis import given
from hypothesis import strategies as st

from axeyum import ir

MAX_WIDTH = 64
WIDTHS = st.integers(min_value=1, max_value=MAX_WIDTH)


# --- the Python reference -----------------------------------------------------


def mask(width: int) -> int:
    """All-ones at `width` bits."""
    return (1 << width) - 1


def signed(width: int, value: int) -> int:
    """Two's-complement reading of an unsigned `width`-bit `value`."""
    return value - (1 << width) if (value >> (width - 1)) & 1 else value


def unsigned(width: int, value: int) -> int:
    """Wraps a signed integer back into `width` unsigned bits."""
    return value & mask(width)


def ref_bvudiv(width: int, x: int, y: int) -> int:
    """SMT-LIB ``bvudiv``: total, and ``(bvudiv x 0)`` is **all ones**.

    SMT-LIB 2.6 FixedSizeBitVectors defines ``bvudiv`` by the `bv2nat`
    quotient for a nonzero divisor and fixes the zero case to all ones -- it is
    total, not partial. Implemented at eval.rs:546
    (``x.checked_div(y).unwrap_or(u128::MAX)``, masked by `bin_bv`).
    """
    if y == 0:
        return mask(width)
    return x // y


def ref_bvurem(width: int, x: int, y: int) -> int:
    """SMT-LIB ``bvurem``: total, and ``(bvurem x 0)`` is **x**.

    Same clause of the standard; eval.rs:547
    (``x.checked_rem(y).unwrap_or(x)``).
    """
    if y == 0:
        return x
    return x % y


def _trunc_div(a: int, b: int) -> int:
    """Truncating (toward zero) division -- C semantics, not Python's floor."""
    quotient = abs(a) // abs(b)
    return -quotient if (a < 0) != (b < 0) else quotient


def ref_bvsdiv(width: int, x: int, y: int) -> int:
    """SMT-LIB ``bvsdiv``: truncating signed division; by zero it is ``-1`` for
    a non-negative dividend and ``1`` otherwise.

    The standard defines ``bvsdiv`` by an ``ite`` expansion over the sign bits
    that bottoms out in ``bvudiv``, so the zero divisor inherits ``bvudiv``'s
    all-ones (i.e. ``-1``) for a non-negative dividend, and ``bvneg`` of it for
    a negative one. eval.rs:548-556 spells out the same case.
    """
    sx, sy = signed(width, x), signed(width, y)
    if sy == 0:
        return unsigned(width, -1 if sx >= 0 else 1)
    return unsigned(width, _trunc_div(sx, sy))


def ref_bvsrem(width: int, x: int, y: int) -> int:
    """SMT-LIB ``bvsrem``: remainder whose sign follows the **dividend**;
    by zero it is ``x``.

    eval.rs:557-564.
    """
    sx, sy = signed(width, x), signed(width, y)
    if sy == 0:
        return unsigned(width, sx)
    return unsigned(width, sx - _trunc_div(sx, sy) * sy)


def ref_bvsmod(width: int, x: int, y: int) -> int:
    """SMT-LIB ``bvsmod``: remainder whose sign follows the **divisor**;
    by zero it is ``x``.

    This is the pair `bvsrem`/`bvsmod` that a reference written from C's ``%``
    collapses into one operation, and they differ on every input whose operand
    signs disagree. eval.rs:565-576.
    """
    sx, sy = signed(width, x), signed(width, y)
    if sy == 0:
        return unsigned(width, sx)
    remainder = sx - _trunc_div(sx, sy) * sy
    if remainder != 0 and (remainder < 0) != (sy < 0):
        remainder += sy
    return unsigned(width, remainder)


def ref_bvshl(width: int, x: int, y: int) -> int:
    """``bvshl``: shift amount is an unsigned bit-vector; ``y >= width`` is 0."""
    return 0 if y >= width else unsigned(width, x << y)


def ref_bvlshr(width: int, x: int, y: int) -> int:
    """``bvlshr``: logical right shift; ``y >= width`` is 0."""
    return 0 if y >= width else x >> y


def ref_bvashr(width: int, x: int, y: int) -> int:
    """``bvashr``: arithmetic right shift; ``y >= width`` replicates the sign."""
    sign = (x >> (width - 1)) & 1
    if y >= width:
        return mask(width) if sign else 0
    return unsigned(width, signed(width, x) >> y)


BV_TO_BV: dict[str, Callable[[int, int, int], int]] = {
    "bvand": lambda w, x, y: x & y,
    "bvor": lambda w, x, y: x | y,
    "bvxor": lambda w, x, y: x ^ y,
    "bvnand": lambda w, x, y: unsigned(w, ~(x & y)),
    "bvnor": lambda w, x, y: unsigned(w, ~(x | y)),
    "bvxnor": lambda w, x, y: unsigned(w, ~(x ^ y)),
    "bvadd": lambda w, x, y: unsigned(w, x + y),
    "bvsub": lambda w, x, y: unsigned(w, x - y),
    "bvmul": lambda w, x, y: unsigned(w, x * y),
    "bvudiv": ref_bvudiv,
    "bvurem": ref_bvurem,
    "bvsdiv": ref_bvsdiv,
    "bvsrem": ref_bvsrem,
    "bvsmod": ref_bvsmod,
    "bvshl": ref_bvshl,
    "bvlshr": ref_bvlshr,
    "bvashr": ref_bvashr,
}

BV_TO_BOOL: dict[str, Callable[[int, int, int], bool]] = {
    "bvult": lambda w, x, y: x < y,
    "bvule": lambda w, x, y: x <= y,
    "bvugt": lambda w, x, y: x > y,
    "bvuge": lambda w, x, y: x >= y,
    "bvslt": lambda w, x, y: signed(w, x) < signed(w, y),
    "bvsle": lambda w, x, y: signed(w, x) <= signed(w, y),
    "bvsgt": lambda w, x, y: signed(w, x) > signed(w, y),
    "bvsge": lambda w, x, y: signed(w, x) >= signed(w, y),
    "eq": lambda w, x, y: x == y,
}

# The overflow predicates are *desugared* by the builders into ordinary ops
# (`bv_uaddo` is a carry-out extract, `bv_smulo` a sign-extended product), so
# the reference here is their arithmetic meaning -- independent of the encoding
# under test, which is the point.
BV_OVERFLOW: dict[str, Callable[[int, int, int], bool]] = {
    "bvuaddo": lambda w, x, y: x + y > mask(w),
    "bvusubo": lambda w, x, y: x < y,
    "bvumulo": lambda w, x, y: x * y > mask(w),
    "bvsaddo": lambda w, x, y: (
        not (-(1 << (w - 1)) <= signed(w, x) + signed(w, y) <= (1 << (w - 1)) - 1)
    ),
    "bvssubo": lambda w, x, y: (
        not (-(1 << (w - 1)) <= signed(w, x) - signed(w, y) <= (1 << (w - 1)) - 1)
    ),
    "bvsmulo": lambda w, x, y: (
        not (-(1 << (w - 1)) <= signed(w, x) * signed(w, y) <= (1 << (w - 1)) - 1)
    ),
}

UNARY_BV: dict[str, Callable[[int, int], int]] = {
    "bvnot": lambda w, x: unsigned(w, ~x),
    "bvneg": lambda w, x: unsigned(w, -x),
}


# --- generators ---------------------------------------------------------------


@st.composite
def bv_case(draw: st.DrawFn, width: st.SearchStrategy[int] = WIDTHS) -> tuple[int, int, int]:
    """A width and two operands, with the degenerate values mixed in by hand.

    Hypothesis biases integer draws toward boundaries on its own, but "on its
    own" is not a property the by-zero soundness cases may rest on: `sampled_from`
    puts ``0``, ``1``, all-ones and the signed minimum in the draw explicitly.
    """
    w = draw(width)
    corners = st.sampled_from([0, 1, mask(w), 1 << (w - 1), mask(w) >> 1])
    operand = st.one_of(corners, st.integers(min_value=0, max_value=mask(w)))
    return w, draw(operand), draw(operand)


def eval_binary(op: str, width: int, x: int, y: int) -> Any:
    """Builds ``(op x y)`` over a fresh arena and evaluates it under a model.

    Variables rather than constants, so the path under test is the one a real
    query takes: symbol declaration, `Assignment` coercion of a Python int to
    the declared sort, and the evaluator -- not a constant folded at build time.
    """
    arena = ir.Arena()
    a = arena.bv_var("a", width)
    b = arena.bv_var("b", width)
    term = getattr(arena, op)(a, b)
    model = ir.Assignment(arena)
    model.set(arena, arena.find_symbol("a"), x)
    model.set(arena, arena.find_symbol("b"), y)
    return ir.eval(arena, term, model)


# --- the properties -----------------------------------------------------------


@given(case=bv_case(), op=st.sampled_from(sorted(BV_TO_BV)))
def test_bv_binary_matches_reference(case: tuple[int, int, int], op: str) -> None:
    """Every bit-vector-valued binary op agrees with the SMT-LIB reference."""
    width, x, y = case
    value = eval_binary(op, width, x, y)
    assert value.width == width, (op, width, x, y)
    assert int(value) == BV_TO_BV[op](width, x, y), (op, width, x, y)


@given(case=bv_case(), op=st.sampled_from(sorted(BV_TO_BOOL)))
def test_bv_comparisons_match_reference(case: tuple[int, int, int], op: str) -> None:
    """Every comparison agrees, signed and unsigned alike."""
    width, x, y = case
    value = eval_binary(op, width, x, y)
    assert value is BV_TO_BOOL[op](width, x, y), (op, width, x, y)


@given(case=bv_case(), op=st.sampled_from(sorted(BV_OVERFLOW)))
def test_bv_overflow_predicates_match_arithmetic(case: tuple[int, int, int], op: str) -> None:
    """The overflow predicates agree with unbounded-integer arithmetic.

    The builders encode these as bit tricks over the word width; the reference
    computes the exact product/sum in Python integers and asks whether it fits.
    """
    width, x, y = case
    value = eval_binary(op, width, x, y)
    assert value is BV_OVERFLOW[op](width, x, y), (op, width, x, y)


@given(case=bv_case(), op=st.sampled_from(sorted(UNARY_BV)))
def test_bv_unary_matches_reference(case: tuple[int, int, int], op: str) -> None:
    """``bvnot`` and ``bvneg`` agree, including at the signed minimum."""
    width, x, _ = case
    arena = ir.Arena()
    a = arena.bv_var("a", width)
    model = ir.Assignment(arena)
    model.set(arena, arena.find_symbol("a"), x)
    value = ir.eval(arena, getattr(arena, op)(a), model)
    assert value.width == width
    assert int(value) == UNARY_BV[op](width, x), (op, width, x)


@given(case=bv_case())
def test_bvcomp_is_a_one_bit_equality(case: tuple[int, int, int]) -> None:
    """``bvcomp`` is equality as a **1-bit bit-vector**, not a Bool."""
    width, x, y = case
    value = eval_binary("bvcomp", width, x, y)
    assert value.width == 1
    assert int(value) == int(x == y)


@given(data=st.data(), width=WIDTHS)
def test_structural_ops_match_reference(data: st.DataObject, width: int) -> None:
    """extract / concat / repeat / extend / rotate agree with slicing on ints."""
    x = data.draw(st.integers(min_value=0, max_value=mask(width)), label="x")
    y = data.draw(st.integers(min_value=0, max_value=mask(width)), label="y")
    lo = data.draw(st.integers(min_value=0, max_value=width - 1), label="lo")
    hi = data.draw(st.integers(min_value=lo, max_value=width - 1), label="hi")
    by = data.draw(st.integers(min_value=0, max_value=8), label="by")
    times = data.draw(st.integers(min_value=1, max_value=max(1, 64 // width)), label="times")

    arena = ir.Arena()
    a = arena.bv_var("a", width)
    b = arena.bv_var("b", width)
    model = ir.Assignment(arena)
    model.set(arena, arena.find_symbol("a"), x)
    model.set(arena, arena.find_symbol("b"), y)

    def value_of(term: Any) -> Any:
        return ir.eval(arena, term, model)

    extracted = value_of(arena.extract(hi, lo, a))
    assert extracted.width == hi - lo + 1
    assert int(extracted) == (x >> lo) & mask(hi - lo + 1)

    # SMT-LIB `concat`: the FIRST argument is the HIGH-order part.
    concatenated = value_of(arena.concat(a, b))
    assert concatenated.width == 2 * width
    assert int(concatenated) == (x << width) | y

    repeated = value_of(arena.repeat(times, a))
    assert repeated.width == width * times
    expected_repeat = 0
    for _ in range(times):
        expected_repeat = (expected_repeat << width) | x
    assert int(repeated) == expected_repeat

    zero_extended = value_of(arena.zero_extend(by, a))
    assert zero_extended.width == width + by
    assert int(zero_extended) == x

    sign_extended = value_of(arena.sign_extend(by, a))
    assert sign_extended.width == width + by
    assert int(sign_extended) == unsigned(width + by, signed(width, x))

    # The builders normalize the rotation amount modulo the width at build
    # time, so `by == width` and `by == 0` intern to the same term.
    shift = by % width
    rotated_left = value_of(arena.rotate_left(by, a))
    expected_left = x if shift == 0 else unsigned(width, (x << shift) | (x >> (width - shift)))
    assert int(rotated_left) == expected_left
    rotated_right = value_of(arena.rotate_right(by, a))
    expected_right = x if shift == 0 else unsigned(width, (x >> shift) | (x << (width - shift)))
    assert int(rotated_right) == expected_right


# --- the degenerate cases, pinned without randomness --------------------------
#
# These duplicate a corner the property tests also reach. That is deliberate:
# a generator can drift (every string fuzz generator in this repository omitted
# escapes for weeks and hid a wrong verdict), and a non-random test cannot.

DEGENERATE_WIDTHS = [1, 2, 3, 7, 8, 16, 31, 32, 63, 64]


@pytest.mark.parametrize("width", DEGENERATE_WIDTHS)
def test_bvudiv_by_zero_is_all_ones(width: int) -> None:
    """``(bvudiv x 0)`` is all ones at every width -- SMT-LIB totality."""
    for x in (0, 1, mask(width), 1 << (width - 1)):
        value = eval_binary("bvudiv", width, x, 0)
        assert int(value) == mask(width), (width, x)


@pytest.mark.parametrize("width", DEGENERATE_WIDTHS)
def test_bvurem_by_zero_is_the_dividend(width: int) -> None:
    """``(bvurem x 0)`` is ``x``."""
    for x in (0, 1, mask(width), 1 << (width - 1)):
        assert int(eval_binary("bvurem", width, x, 0)) == x, (width, x)


@pytest.mark.parametrize("width", DEGENERATE_WIDTHS)
def test_signed_division_by_zero_follows_smtlib(width: int) -> None:
    """``bvsdiv``/``bvsrem``/``bvsmod`` by zero, at every width."""
    for x in (0, 1, mask(width), 1 << (width - 1), mask(width) >> 1):
        sx = signed(width, x)
        assert int(eval_binary("bvsdiv", width, x, 0)) == unsigned(width, -1 if sx >= 0 else 1)
        assert int(eval_binary("bvsrem", width, x, 0)) == x
        assert int(eval_binary("bvsmod", width, x, 0)) == x


def test_no_zero_divisor_raises_zerodivisionerror() -> None:
    """A caller expecting Python's ``ZeroDivisionError`` would misread a correct
    answer, so the binding must never raise one."""
    for op in ("bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"):
        assert eval_binary(op, 8, 200, 0) is not None


# --- Int -----------------------------------------------------------------------

INT_BOUND = 1 << 40
INTS = st.one_of(
    st.sampled_from([0, 1, -1, 2, -2, INT_BOUND, -INT_BOUND]),
    st.integers(min_value=-INT_BOUND, max_value=INT_BOUND),
)


def eval_int(op: str, x: int, y: int | None = None) -> Any:
    """Builds an Int term over declared variables and evaluates it."""
    arena = ir.Arena()
    a = arena.int_var("a")
    model = ir.Assignment(arena)
    model.set(arena, arena.find_symbol("a"), x)
    if y is None:
        return ir.eval(arena, getattr(arena, op)(a), model)
    b = arena.int_var("b")
    model.set(arena, arena.find_symbol("b"), y)
    return ir.eval(arena, getattr(arena, op)(a, b), model)


def ref_int_div(x: int, y: int) -> int:
    """SMT-LIB Ints ``div``: **Euclidean**, and ``(div x 0)`` is ``0`` here.

    SMT-LIB's Ints theory defines ``div``/``mod`` by the Euclidean law
    ``x = y * (div x y) + (mod x y)`` with ``0 <= (mod x y) < |y|`` -- which is
    NOT C's truncating division and not Python's floor division either, except
    where the signs happen to agree. Division by zero is left unspecified by the
    standard; this IR pins it, and the convention is stated at
    crates/axeyum-ir/src/eval.rs:772-774 ("by convention `div a 0 = 0` and
    `mod a 0 = a`"), implemented at eval.rs:775-786.
    """
    if y == 0:
        return 0
    remainder = x % abs(y)  # Python's % with a positive modulus is Euclidean
    return (x - remainder) // y


def ref_int_mod(x: int, y: int) -> int:
    """SMT-LIB Ints ``mod``: in ``[0, |y|)``; ``(mod x 0)`` is ``x``.

    eval.rs:787-791 (``x.rem_euclid(y)``, and ``x`` for a zero divisor).
    """
    if y == 0:
        return x
    return x % abs(y)


@given(x=INTS, y=INTS)
def test_int_div_mod_are_euclidean_and_total(x: int, y: int) -> None:
    """``div``/``mod`` match the Euclidean reference, zero divisor included."""
    assert eval_int("int_div", x, y) == ref_int_div(x, y), (x, y)
    assert eval_int("int_mod", x, y) == ref_int_mod(x, y), (x, y)
    if y != 0:
        # The defining law, asserted directly rather than through the reference.
        assert x == y * ref_int_div(x, y) + ref_int_mod(x, y)
        assert 0 <= ref_int_mod(x, y) < abs(y)


@given(x=INTS, y=INTS)
def test_int_arithmetic_matches_python(x: int, y: int) -> None:
    """Addition, subtraction, multiplication, negation, absolute value."""
    assert eval_int("int_add", x, y) == x + y
    assert eval_int("int_sub", x, y) == x - y
    assert eval_int("int_mul", x, y) == x * y
    assert eval_int("int_neg", x) == -x
    assert eval_int("int_abs", x) == abs(x)


@given(x=INTS, y=INTS)
def test_int_comparisons_match_python(x: int, y: int) -> None:
    """The four Int order predicates."""
    assert eval_int("int_lt", x, y) is (x < y)
    assert eval_int("int_le", x, y) is (x <= y)
    assert eval_int("int_gt", x, y) is (x > y)
    assert eval_int("int_ge", x, y) is (x >= y)


@pytest.mark.parametrize("x", [-7, -1, 0, 1, 7, 1 << 40])
def test_int_div_mod_by_zero_are_total(x: int) -> None:
    """The degenerate divisor, pinned without randomness: ``div x 0 = 0`` and
    ``mod x 0 = x``, and neither raises."""
    assert eval_int("int_div", x, 0) == 0
    assert eval_int("int_mod", x, 0) == x
