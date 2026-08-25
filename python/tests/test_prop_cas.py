"""Hypothesis properties for ``axeyum.cas`` over random polynomials in Q[x, y].

Each property is an algebraic identity that must hold for **every** polynomial,
checked through the certified zero test rather than by comparing printed forms
(``Expr.__str__`` is not round-trippable, and two spellings of the same
polynomial are equal without being identical: ``differentiate`` alone returns
``0*x^3*y + (1/4)*(3*x^2*1)*y + ...``).

``None`` is a value here, never a failure: across the CAS it means *outside the
fragment, declined, or an* ``i128`` *overflow*. Every such example is counted as
a **decline** by :class:`Tally` and the test asserts a floor on the examples it
genuinely checked -- so a change that made an operation decline everything fails
this suite instead of passing it silently.
"""

from __future__ import annotations

import math
from fractions import Fraction

from _prop_helpers import Tally
from hypothesis import given, settings
from hypothesis import strategies as st

from axeyum import cas

MAX_DEGREE = 4
VAR_NAMES = ("x", "y")

# A drawn polynomial: its terms as (coefficient, exponent-per-variable), and the
# variable names those exponents line up with.
Poly = tuple[list[tuple[Fraction, tuple[int, ...]]], tuple[str, ...]]

# Small coefficients keep the `i128` numerator/denominator far from overflow, so
# a decline in these suites means the OPERATION declined, not that the generator
# wandered out of range.
COEFFICIENTS = st.builds(
    Fraction,
    st.integers(min_value=-12, max_value=12),
    st.integers(min_value=1, max_value=6),
)


@st.composite
def polynomial(draw: st.DrawFn, variables: int = 2) -> Poly:
    """A polynomial as a list of ``(coefficient, exponents)`` terms.

    Returned as data rather than as an `Expr` so the test can build the CAS
    expression AND an independent Python reference from the same draw.
    """
    names = VAR_NAMES[:variables]
    exponents = st.tuples(*[st.integers(min_value=0, max_value=MAX_DEGREE) for _ in names]).filter(
        lambda powers: sum(powers) <= MAX_DEGREE
    )
    terms = draw(st.lists(st.tuples(COEFFICIENTS, exponents), min_size=1, max_size=5))
    return terms, names


def to_expr(terms: list[tuple[Fraction, tuple[int, ...]]], names: tuple[str, ...]) -> cas.Expr:
    """Builds the CAS expression for a drawn polynomial."""
    total = cas.Expr.zero()
    for coefficient, powers in terms:
        term = cas.Expr.rat(coefficient.numerator, coefficient.denominator)
        for name, power in zip(names, powers, strict=True):
            for _ in range(power):
                term = term * cas.Expr.var(name)
        total = total + term
    return total


def evaluate(
    terms: list[tuple[Fraction, tuple[int, ...]]],
    names: tuple[str, ...],
    point: dict[str, Fraction],
) -> Fraction:
    """Exact rational value of the drawn polynomial -- the reference."""
    total = Fraction(0)
    for coefficient, powers in terms:
        value = coefficient
        for name, power in zip(names, powers, strict=True):
            value *= point[name] ** power
        total += value
    return total


def certified_equal(left: cas.Expr, right: cas.Expr) -> bool | None:
    """`True`/`False` when the zero test is certified, `None` when it declines.

    The verdict is read from the `Certified` variant only: an `Unknown` zero
    test is not a pass, and collapsing it to `False` would turn a declined
    check into a reported defect.
    """
    verdict = cas.equal(left, right)
    if verdict.kind != "certified":
        return None
    return bool(verdict.equal)


@given(drawn=polynomial(variables=1))
@settings(max_examples=150)
def _factor_round_trip(drawn: Poly, tally: Tally) -> None:
    terms, names = drawn
    poly = cas.expand(to_expr(terms, names))
    factored = cas.factor(poly, names[0])
    if factored is None:
        tally.decline("factor declined")
        return
    verdict = certified_equal(cas.expand(factored), poly)
    if verdict is None:
        tally.decline("zero test not certified")
        return
    tally.check()
    assert verdict is True, (poly, factored)


def test_expand_of_factor_is_the_original() -> None:
    """``expand(factor(p)) == p``, decided by the certified zero test."""
    tally = Tally("expand(factor(p))")
    _factor_round_trip(tally=tally)
    print(f"PROP|{tally}")
    tally.require(20)


@given(drawn=polynomial())
@settings(max_examples=150)
def _integrate_then_differentiate(drawn: Poly, tally: Tally) -> None:
    terms, names = drawn
    poly = to_expr(terms, names)
    integral = cas.integrate(poly, names[0])
    if integral is None:
        tally.decline("integrate declined")
        return
    derivative = cas.simplify(integral.antiderivative.differentiate(names[0]))
    verdict = certified_equal(derivative, poly)
    if verdict is None:
        tally.decline("zero test not certified")
        return
    tally.check()
    assert verdict is True, (poly, integral.antiderivative)
    # The integral carries its own certificate; a certified integral whose
    # derivative did not match would mean the certificate proves nothing.
    assert integral.is_certified() is True


def test_differentiate_undoes_integrate() -> None:
    """``d/dx integral(p) == p`` -- the fundamental theorem, on polynomials."""
    tally = Tally("d/dx integrate(p)")
    _integrate_then_differentiate(tally=tally)
    print(f"PROP|{tally}")
    tally.require(100)


@given(drawn=polynomial(), point=st.tuples(COEFFICIENTS, COEFFICIENTS))
@settings(max_examples=150)
def _evaluation_agrees_with_fractions(
    drawn: Poly, point: tuple[Fraction, Fraction], tally: Tally
) -> None:
    terms, names = drawn
    poly = to_expr(terms, names)
    bindings = dict(zip(names, point, strict=False))
    expected = evaluate(terms, names, bindings)

    exact = poly.eval({name: value for name, value in bindings.items()})
    if exact is None:
        tally.decline("Expr.eval declined")
        return
    tally.check()
    # Exact rational arithmetic on both sides: equality, not a tolerance.
    assert exact == expected, (poly, bindings, exact, expected)

    approximate = cas.evalf(poly, {name: float(value) for name, value in bindings.items()})
    if approximate is None:
        tally.decline("evalf declined")
        return
    assert math.isclose(approximate, float(expected), rel_tol=1e-9, abs_tol=1e-12), (
        poly,
        bindings,
        approximate,
        float(expected),
    )


def test_evaluation_agrees_with_exact_rational_arithmetic() -> None:
    """`Expr.eval` is exact over `Fraction`; `evalf` agrees to floating point."""
    tally = Tally("eval vs fractions")
    _evaluation_agrees_with_fractions(tally=tally)
    print(f"PROP|{tally}")
    tally.require(100)


@given(drawn=polynomial())
@settings(max_examples=150)
def _normalize_is_idempotent(drawn: Poly, tally: Tally) -> None:
    terms, names = drawn
    poly = to_expr(terms, names)
    once = cas.normalize(poly)
    if once is None:
        tally.decline("normalize declined")
        return
    twice = cas.normalize(once.to_expr())
    if twice is None:
        tally.decline("normalize declined on its own output")
        return
    tally.check()
    assert twice == once, (poly, once.to_expr(), twice.to_expr())


def test_normalize_is_idempotent() -> None:
    """``normalize(normalize(p)) == normalize(p)`` -- a canonical form that
    moved on the second pass would not be canonical."""
    tally = Tally("normalize idempotent")
    _normalize_is_idempotent(tally=tally)
    print(f"PROP|{tally}")
    tally.require(100)


@given(a=polynomial(), b=polynomial(), c=polynomial())
@settings(max_examples=100)
def _ring_laws(a: Poly, b: Poly, c: Poly, tally: Tally) -> None:
    polys = []
    for terms, names in (a, b, c):
        poly = cas.MvPoly.from_expr(to_expr(terms, names))
        if poly is None:
            tally.decline("MvPoly.from_expr declined")
            return
        polys.append(poly)
    p, q, r = polys

    # Every `MvPoly` operation returns `None` on an `i128` overflow. Each is
    # bound to a name and checked before use, so an overflow anywhere ends the
    # example as a DECLINE -- never as a silently satisfied identity.
    products: dict[str, cas.MvPoly | None] = {
        "p+q": p.add(q),
        "q+p": q.add(p),
        "q+r": q.add(r),
        "p*q": p.mul(q),
        "q*p": q.mul(p),
        "p*r": p.mul(r),
    }
    if any(value is None for value in products.values()):
        tally.decline("MvPoly overflow in a subterm")
        return

    associativity = (products["p+q"].add(r), p.add(products["q+r"]))
    distributivity = (p.mul(products["q+r"]), products["p*q"].add(products["p*r"]))
    if any(value is None for value in (*associativity, *distributivity)):
        tally.decline("MvPoly overflow combining subterms")
        return

    tally.check()
    assert associativity[0] == associativity[1], "addition is not associative"
    assert products["p+q"] == products["q+p"], "addition is not commutative"
    assert products["p*q"] == products["q*p"], "multiplication is not commutative"
    assert distributivity[0] == distributivity[1], (
        "multiplication does not distribute over addition"
    )


def test_mvpoly_ring_laws() -> None:
    """`MvPoly` is a commutative ring: associativity, commutativity,
    distributivity."""
    tally = Tally("MvPoly ring laws")
    _ring_laws(tally=tally)
    print(f"PROP|{tally}")
    tally.require(50)
