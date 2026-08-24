"""`axeyum.cas` -- expressions, polynomials, and the certificate-shaped values.

Two properties are load-bearing here and are asserted, not assumed:

* ``None`` is a value. ``normalize``, ``factor``, ``integrate``, ``MvPoly.add``
  and friends return ``None`` for *outside the fragment or i128 overflow*, and
  the tests below check that shape rather than treating it as an error.
* A certificate is inspected, never trusted. ``equal`` and ``integrate`` hand
  back a witness, and the tests re-derive from the witness instead of reading
  the flag.
"""

from __future__ import annotations

import math
import random
from fractions import Fraction

import pytest

from axeyum._native import cas

E = cas.Expr


def x() -> cas.Expr:
    return E.var("x")


def i(n: int) -> cas.Expr:
    return E.int(n)


# --------------------------------------------------------------------------
# module shape
# --------------------------------------------------------------------------


def test_cas_submodule_is_importable_by_name() -> None:
    import axeyum._native.cas as native_cas

    assert native_cas.__name__ == "axeyum._native.cas"


def test_cas_error_is_an_axeyum_error() -> None:
    import axeyum

    assert issubclass(cas.CasError, axeyum.AxeyumError)
    assert issubclass(cas.Gf2Error, cas.CasError)


@pytest.mark.parametrize(
    "name",
    [
        "Expr",
        "MvPoly",
        "Monomial",
        "MultiPoly",
        "Rational",
        "ZeroTest",
        "Certainty",
        "Assumptions",
        "LimitPoint",
        "Matrix",
        "RealInterval",
        "normalize",
        "equal",
        "integrate",
        "evalf",
        "simplify",
        "factor",
    ],
)
def test_public_name_present(name: str) -> None:
    assert hasattr(cas, name)


# --------------------------------------------------------------------------
# Rational
# --------------------------------------------------------------------------


def test_rational_normalizes() -> None:
    r = cas.Rational(4, -6)
    assert (r.numerator, r.denominator) == (-2, 3)
    assert r.to_fraction() == Fraction(-2, 3)


def test_rational_zero_denominator_is_a_value_error() -> None:
    with pytest.raises(ValueError):
        cas.Rational(1, 0)


def test_rational_round_trips_through_fraction() -> None:
    for value in (Fraction(3, 7), Fraction(-11, 4), Fraction(5)):
        assert cas.Rational.coerce(value).to_fraction() == value


def test_rational_coerces_a_plain_int() -> None:
    assert cas.Rational.coerce(7).to_fraction() == Fraction(7)


def test_rational_equality_spans_int_and_fraction() -> None:
    assert cas.Rational(6, 3) == 2
    assert cas.Rational(1, 2) == Fraction(1, 2)


def test_rational_is_integer_and_is_zero() -> None:
    assert cas.Rational(4, 2).is_integer()
    assert not cas.Rational(1, 2).is_integer()
    assert cas.Rational(0, 5).is_zero()


# --------------------------------------------------------------------------
# Expr constructors and operators
# --------------------------------------------------------------------------


def test_expr_rat_with_zero_denominator_is_a_value_error() -> None:
    # The Rust `CasExpr::rat` PANICS here; the binding must not.
    with pytest.raises(ValueError):
        E.rat(1, 0)


def test_expr_rat_builds_an_exact_constant() -> None:
    assert E.rat(3, 6).eval({}) == Fraction(1, 2)


def test_expr_zero_and_one() -> None:
    assert E.zero().eval({}) == Fraction(0)
    assert E.one().eval({}) == Fraction(1)


def test_expr_var_evaluates_from_the_environment() -> None:
    assert x().eval({"x": Fraction(5, 2)}) == Fraction(5, 2)


def test_expr_eval_of_an_unbound_variable_is_none_not_an_error() -> None:
    assert x().eval({}) is None


def test_expr_arithmetic_round_trips_through_eval() -> None:
    env = {"x": Fraction(3), "y": Fraction(-2)}
    y = E.var("y")
    assert (x() + y).eval(env) == Fraction(1)
    assert (x() - y).eval(env) == Fraction(5)
    assert (x() * y).eval(env) == Fraction(-6)
    assert (x() / y).eval(env) == Fraction(-3, 2)
    assert (-x()).eval(env) == Fraction(-3)
    assert (x() ** 3).eval(env) == Fraction(27)


def test_expr_pow_rejects_a_modulus() -> None:
    with pytest.raises(TypeError):
        pow(x(), 2, 5)


def test_expr_equality_is_structural() -> None:
    assert x() + i(1) == x() + i(1)
    assert x() + i(1) != i(1) + x()  # not in normal form; `normalize` decides


def test_expr_hash_agrees_with_equality() -> None:
    assert hash(x() * i(2)) == hash(x() * i(2))
    assert len({x(), x(), E.var("y")}) == 2


def test_expr_str_renders_but_is_not_a_parser() -> None:
    assert str(x().pow(2)) == "x^2"
    assert not hasattr(cas, "parse")  # the crate has no parser to project


def test_expr_variables() -> None:
    assert (x() * E.var("y") + E.var("z")).variables() == ["x", "y", "z"]


@pytest.mark.parametrize(
    "name",
    [
        "ln",
        "exp",
        "sin",
        "cos",
        "tan",
        "atan",
        "sqrt",
        "cbrt",
        "airy_ai",
        "airy_bi",
        "lambert_w",
        "erf",
        "gamma",
        "digamma",
        "factorial",
        "si",
        "ci",
        "ei",
        "li",
        "abs",
        "sign",
        "floor",
        "ceiling",
    ],
)
def test_unary_builder_exists_and_differentiates(name: str) -> None:
    built = getattr(x(), name)()
    assert isinstance(built, cas.Expr)
    assert isinstance(built.differentiate("x"), cas.Expr)


@pytest.mark.parametrize(
    "name,arg", [("nth_root", 3), ("polygamma", 2), ("bessel_j", 1), ("bessel_i", 1)]
)
def test_indexed_unary_builder(name: str, arg: int) -> None:
    built = getattr(x(), name)(arg)
    assert isinstance(built, cas.Expr)


def test_imaginary_unit_squares_to_minus_one() -> None:
    unit = E.imaginary_unit()
    squared = cas.expand(unit * unit)
    assert squared is not None
    assert cas.equal(squared, i(-1)).equal is True


def test_substitute() -> None:
    assert x().pow(2).substitute("x", i(3)).eval({}) == Fraction(9)


def test_differentiate_n() -> None:
    third = x().pow(3).differentiate_n("x", 3)
    assert third.eval({"x": Fraction(0)}) == Fraction(6)


# --------------------------------------------------------------------------
# differentiate, cross-checked against a Python reference
# --------------------------------------------------------------------------


def _poly_from_coeffs(coeffs: list[int]) -> cas.Expr:
    """`sum(c_k * x**k)` built with the constructors."""
    built = E.zero()
    for power, coefficient in enumerate(coeffs):
        built = built + i(coefficient) * x() ** power
    return built


def _derivative_coeffs(coeffs: list[int]) -> list[int]:
    return [power * coefficient for power, coefficient in enumerate(coeffs)][1:]


def _horner(coeffs: list[int], value: Fraction) -> Fraction:
    total = Fraction(0)
    for coefficient in reversed(coeffs):
        total = total * value + coefficient
    return total


@pytest.mark.parametrize("seed", range(20))
def test_differentiate_matches_a_python_reference(seed: int) -> None:
    rng = random.Random(1000 + seed)
    coeffs = [rng.randint(-6, 6) for _ in range(rng.randint(1, 6))]
    derivative = _poly_from_coeffs(coeffs).differentiate("x")
    expected = _derivative_coeffs(coeffs)
    for point in (Fraction(-3), Fraction(-1, 2), Fraction(0), Fraction(2), Fraction(7, 3)):
        assert derivative.eval({"x": point}) == _horner(expected, point)


# --------------------------------------------------------------------------
# evalf, cross-checked against `math` / `fractions`
# --------------------------------------------------------------------------

_HEADS = [
    ("exp", math.exp),
    ("sin", math.sin),
    ("cos", math.cos),
    ("atan", math.atan),
]


def _random_expr(rng: random.Random, depth: int) -> tuple[cas.Expr, object]:
    """A random expression and a Python callable computing the same value."""
    if depth == 0 or rng.random() < 0.25:
        choice = rng.randint(0, 2)
        if choice == 0:
            return x(), (lambda env: env["x"])
        if choice == 1:
            return E.var("y"), (lambda env: env["y"])
        n = rng.randint(-4, 4)
        return i(n), (lambda env, n=n: float(n))
    op = rng.randint(0, 4)
    if op == 4:
        inner, inner_fn = _random_expr(rng, depth - 1)
        name, fn = _HEADS[rng.randrange(len(_HEADS))]
        return getattr(inner, name)(), (lambda env, fn=fn, g=inner_fn: fn(g(env)))
    if op == 3:
        inner, inner_fn = _random_expr(rng, depth - 1)
        power = rng.randint(0, 3)
        return inner**power, (lambda env, p=power, g=inner_fn: g(env) ** p)
    left, left_fn = _random_expr(rng, depth - 1)
    right, right_fn = _random_expr(rng, depth - 1)
    if op == 0:
        return left + right, (lambda env, a=left_fn, b=right_fn: a(env) + b(env))
    if op == 1:
        return left - right, (lambda env, a=left_fn, b=right_fn: a(env) - b(env))
    return left * right, (lambda env, a=left_fn, b=right_fn: a(env) * b(env))


@pytest.mark.parametrize("seed", range(50))
def test_evalf_matches_a_python_reference(seed: int) -> None:
    rng = random.Random(20260824 + seed)
    expr, reference = _random_expr(rng, 3)
    env = {"x": round(rng.uniform(-2.0, 2.0), 6), "y": round(rng.uniform(-2.0, 2.0), 6)}
    got = cas.evalf(expr, env)
    expected = reference(env)
    assert got is not None, f"evalf declined on {expr!s}"
    assert math.isclose(got, expected, rel_tol=1e-9, abs_tol=1e-9)


def test_evalf_of_an_unbound_variable_is_none() -> None:
    assert cas.evalf(x(), {}) is None


def test_rationalize_and_nsimplify() -> None:
    assert cas.rationalize(0.25, 100) == Fraction(1, 4)
    assert cas.nsimplify(0.5, 100) is not None


# --------------------------------------------------------------------------
# normalize / equal / ZeroTest
# --------------------------------------------------------------------------


def test_normalize_of_a_polynomial() -> None:
    normal = cas.normalize((x() + i(1)) * (x() - i(1)))
    assert normal is not None
    assert normal.eval({"x": Fraction(3)}) == Fraction(8)


def test_normalize_outside_the_fragment_is_none() -> None:
    assert cas.normalize(x().sin()) is None


def test_equal_on_a_true_identity() -> None:
    left = (x() + i(1)) * (x() + i(1))
    right = x().pow(2) + i(2) * x() + i(1)
    test = cas.equal(left, right)
    assert test.kind == "certified"
    assert test.equal is True
    assert test.certainty() == cas.Certainty.Certified


def test_equal_on_a_false_identity() -> None:
    test = cas.equal(x().pow(2), x().pow(2) + i(1))
    assert test.equal is False
    assert test.witness is not None
    assert not test.witness.is_zero()


def test_zero_test_witness_re_normalizes() -> None:
    """The witness IS the certificate: re-derive it, do not trust the flag."""
    left = (x() + i(2)) * (x() - i(2))
    right = x().pow(2) - i(4)
    test = cas.equal(left, right)
    assert test.equal is True
    witness = test.witness
    assert witness is not None
    assert witness.is_zero()
    # Independent re-derivation: normalize the difference ourselves.
    assert cas.normalize(left - right) == witness


def test_zero_test_unknown_has_no_verdict() -> None:
    huge = i(2**62) * x()
    test = cas.equal(huge * huge * huge, huge)
    if test.kind == "unknown":
        assert test.equal is None
        assert test.witness is None
    else:
        assert test.equal is False


def test_prove_derivative() -> None:
    claimed = i(2) * x()
    assert cas.prove_derivative(x().pow(2), "x", claimed).equal is True
    assert cas.prove_derivative(x().pow(2), "x", i(3) * x()).equal is False


# --------------------------------------------------------------------------
# MvPoly / Monomial / MultiPoly
# --------------------------------------------------------------------------


def test_mvpoly_constructors_and_terms() -> None:
    poly = cas.MvPoly.var("x").mul(cas.MvPoly.var("y"))
    assert poly is not None
    assert poly.term_count() == 1
    ((monomial, coefficient),) = poly.terms()
    assert coefficient == Fraction(1)
    assert monomial.powers() == [("x", 1), ("y", 1)]


def test_mvpoly_from_terms() -> None:
    monomial = cas.Monomial.from_powers([("x", 2)])
    poly = cas.MvPoly.from_terms([(monomial, Fraction(3, 2))])
    assert poly is not None
    assert poly.evaluate({"x": Fraction(2)}) == Fraction(6)


def test_mvpoly_arithmetic_and_degree() -> None:
    x_poly = cas.MvPoly.var("x")
    squared = x_poly.mul(x_poly)
    assert squared is not None
    assert squared.degree_in("x") == 2
    assert squared.total_degree() == 2
    assert squared.variables() == ["x"]


def test_mvpoly_operators_mirror_the_methods() -> None:
    a = cas.MvPoly.var("x")
    b = cas.MvPoly.constant(3)
    assert (a + b) == a.add(b)
    assert (a - b) == a.sub(b)
    assert (a * b) == a.mul(b)
    assert (-a) == a.neg()


def test_mvpoly_overflow_is_none_not_an_error() -> None:
    big = cas.MvPoly.constant(2**126)
    assert big.mul(big) is None


def test_mvpoly_division() -> None:
    x_poly = cas.MvPoly.var("x")
    one = cas.MvPoly.constant(1)
    numerator = x_poly.mul(x_poly).sub(one)
    divisor = x_poly.sub(one)
    quotient, remainder = numerator.divide(divisor)
    assert remainder.is_zero()
    assert numerator.exact_div(divisor) == quotient
    assert divisor.divides(numerator) is True


def test_mvpoly_gcd_and_derivative() -> None:
    x_poly = cas.MvPoly.var("x")
    squared = x_poly.mul(x_poly)
    assert squared.gcd(x_poly) is not None
    assert squared.derivative_in("x") == x_poly.mul(cas.MvPoly.constant(2))


def test_mvpoly_expr_bridge_round_trips() -> None:
    expr = x().pow(2) + i(3) * x()
    poly = cas.MvPoly.from_expr(expr)
    assert poly is not None
    assert cas.equal(poly.to_expr(), expr).equal is True


def test_mvpoly_from_expr_outside_the_fragment_is_none() -> None:
    assert cas.MvPoly.from_expr(x().sin()) is None


def test_monomial_one_and_exponent_of() -> None:
    one = cas.Monomial.one()
    assert one.total_degree() == 0
    assert one.exponent_of("x") == 0
    assert cas.Monomial.from_powers([("x", 3)]).exponent_of("x") == 3


def test_multipoly_to_univariate() -> None:
    normal = cas.normalize(x().pow(2) - i(4))
    assert normal is not None
    assert normal.to_univariate("x") == [Fraction(-4), Fraction(0), Fraction(1)]


def test_multipoly_to_expr_agrees() -> None:
    expr = x().pow(2) - i(4)
    normal = cas.normalize(expr)
    assert cas.equal(normal.to_expr(), expr).equal is True


def test_multipoly_zero() -> None:
    assert cas.MultiPoly.zero().is_zero()


# --------------------------------------------------------------------------
# integrate / definite_integrate
# --------------------------------------------------------------------------


def test_integrate_a_polynomial_is_certified_and_the_witness_re_normalizes() -> None:
    integrand = i(3) * x().pow(2)
    result = cas.integrate(integrand, "x")
    assert result is not None
    assert result.is_certified()
    certificate = result.certificate
    assert certificate.kind == "certified"
    assert certificate.equal is True
    witness = certificate.witness
    assert witness is not None and witness.is_zero()
    # Re-derive the obligation ourselves rather than trusting `is_certified`.
    derivative = result.antiderivative.differentiate("x")
    assert cas.equal(derivative, integrand).equal is True
    assert cas.normalize(derivative - integrand) == witness


def test_integrate_declines_as_none_not_an_error() -> None:
    assert cas.integrate(x().gamma(), "x") is None


def test_definite_integrate_is_certified() -> None:
    result = cas.definite_integrate(i(3) * x().pow(2), "x", i(0), i(1))
    assert result is not None
    assert result.is_certified()
    assert result.value.eval({}) == Fraction(1)
    assert result.certificate.equal is True


# --------------------------------------------------------------------------
# the simplification family
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    "name",
    [
        "simplify",
        "trigsimp",
        "simplify_radicals",
        "evaluate_trig",
        "rewrite_exp",
        "expand_log",
        "expand_trig",
        "logcombine",
        "conjugate",
    ],
)
def test_total_simplifier_returns_an_expr(name: str) -> None:
    assert isinstance(getattr(cas, name)(x() + i(0)), cas.Expr)


def test_expand_and_cancel() -> None:
    expanded = cas.expand((x() + i(1)) * (x() + i(1)))
    assert expanded is not None
    assert cas.equal(expanded, x().pow(2) + i(2) * x() + i(1)).equal is True
    cancelled = cas.cancel((x().pow(2) - i(1)) / (x() - i(1)))
    assert str(cancelled) == "x + 1"


def test_collect_and_apart() -> None:
    assert cas.collect(x() + x(), "x") is not None
    assert cas.apart(i(1) / (x().pow(2) - i(1)), "x") is not None


def test_factor_and_degree() -> None:
    poly = x().pow(2) - i(3) * x() + i(2)
    assert str(cas.factor(poly, "x")) == "(x - 1)*(x - 2)"
    assert cas.degree(poly, "x") == 2
    assert cas.leading_coeff(poly, "x") is not None


def test_simplify_under_assumptions() -> None:
    assumptions = cas.Assumptions().positive("x")
    assert isinstance(cas.simplify_under_assumptions(x().abs(), assumptions), cas.Expr)


def test_assumptions_signs() -> None:
    assumptions = cas.Assumptions().positive("x").negative("y").nonzero("z")
    assert assumptions.sign_of(x()) == cas.Sign.Positive
    assert assumptions.is_positive(x())
    assert assumptions.is_nonnegative(x())
    assert assumptions.is_nonzero(E.var("z"))
    assert assumptions.sign_of(E.var("w")) == cas.Sign.Unknown


def test_assumptions_are_immutable_builders() -> None:
    base = cas.Assumptions()
    derived = base.positive("x")
    assert base.sign_of(x()) == cas.Sign.Unknown
    assert derived.sign_of(x()) == cas.Sign.Positive


# --------------------------------------------------------------------------
# solving, limits, series
# --------------------------------------------------------------------------


def test_solve_a_quadratic() -> None:
    roots = cas.solve(x().pow(2) - i(3) * x() + i(2), "x")
    assert [str(root) for root in roots] == ["1", "2"]


def test_solve_polynomial_inequality() -> None:
    intervals = cas.solve_polynomial_inequality(x().pow(2) - i(5) * x() + i(6), "x", ">")
    assert len(intervals) == 2
    assert intervals[0].lower is None
    assert intervals[0].upper == Fraction(2)
    assert intervals[1].upper is None


def test_solve_polynomial_inequality_rejects_an_unknown_operator() -> None:
    with pytest.raises(ValueError):
        cas.solve_polynomial_inequality(x(), "x", "!=")


def test_real_root_intervals_and_counting() -> None:
    poly = x().pow(2) - i(2)
    intervals = cas.real_root_intervals(poly, "x")
    assert len(intervals) == 2
    assert cas.count_real_roots(poly, "x", Fraction(-3), Fraction(3)) == 2


def test_approximate_real_roots() -> None:
    roots = cas.approximate_real_roots(x().pow(2) - i(2), "x", Fraction(1, 1000))
    assert len(roots) == 2
    assert abs(float(roots[1]) - math.sqrt(2)) < 1e-3


def test_limit_at_a_finite_point() -> None:
    value = cas.limit((x().pow(2) - i(4)) / (x() - i(2)), "x", cas.LimitPoint.finite(2))
    assert str(value) == "4"


def test_limit_at_infinity() -> None:
    assert cas.limit(i(1) / x(), "x", cas.LimitPoint.pos_infinity()) is not None
    assert isinstance(cas.LimitPoint.neg_infinity(), cas.LimitPoint)


def test_series_and_series_at() -> None:
    assert cas.series(x().exp(), "x", 4) is not None
    assert cas.series_at(x().ln(), "x", i(1), 3) is not None


def test_solve_linear_system() -> None:
    y = E.var("y")
    solution = cas.solve_linear_system([x() + y - i(3), x() - y - i(1)], ["x", "y"])
    assert {name: str(value) for name, value in solution} == {"x": "2", "y": "1"}


def test_resultant_and_discriminant() -> None:
    assert str(cas.resultant(x().pow(2) - i(1), x() - i(1), "x")) == "0"
    assert str(cas.discriminant(x().pow(2) - i(5) * x() + i(6), "x")) == "1"


def test_sum_polynomial_and_gosper() -> None:
    n = E.var("n")
    assert cas.sum_polynomial(n, "n") is not None
    k = E.var("k")
    assert cas.gosper_sum(i(1) / (k * (k + i(1))), "k") is not None


def test_dsolve_homogeneous_and_inhomogeneous() -> None:
    assert cas.dsolve_homogeneous([Fraction(1), Fraction(0), Fraction(1)], "x") is not None
    assert cas.dsolve_inhomogeneous([Fraction(1), Fraction(1)], x(), "x") is not None


def test_solve_recurrence() -> None:
    fib = cas.solve_recurrence([Fraction(1), Fraction(1)], [Fraction(0), Fraction(1)], "n")
    assert fib is not None


# --------------------------------------------------------------------------
# linear algebra
# --------------------------------------------------------------------------


def _diag_two_three() -> cas.Matrix:
    return cas.Matrix.from_rows([[i(2), i(0)], [i(0), i(3)]])


def test_matrix_shape_and_determinant() -> None:
    matrix = _diag_two_three()
    assert (matrix.rows, matrix.cols) == (2, 2)
    assert str(matrix.determinant()) == "6"


def test_matrix_rank_trace_and_polynomials() -> None:
    matrix = _diag_two_three()
    assert cas.matrix_rank(matrix) == 2
    assert cas.trace(matrix) is not None
    assert str(cas.minimal_polynomial(matrix, "L")) == "L^2 - 5*L + 6"


def test_eigenvectors_report_one_per_eigenvalue() -> None:
    pairs = cas.eigenvectors(_diag_two_three(), "L")
    assert len(pairs) == 2
    assert all(len(vectors) >= 1 for _, vectors in pairs)


def test_matrix_arithmetic() -> None:
    identity = cas.Matrix.identity(2)
    matrix = _diag_two_three()
    assert matrix.mul(identity) == matrix
    assert matrix.add(cas.Matrix.zeros(2, 2)) == matrix
    assert matrix.transpose() == matrix


def test_gradient_of_a_two_variable_expression() -> None:
    y = E.var("y")
    parts = cas.gradient(x().pow(2) * y, ["x", "y"])
    assert len(parts) == 2
    assert str(parts[0]) == "2*x*y"


def test_hessian_and_jacobian() -> None:
    y = E.var("y")
    assert cas.hessian(x().pow(2) * y, ["x", "y"]) is not None
    assert cas.jacobian([x() * y, x() + y], ["x", "y"]) is not None


def test_standard_deviation() -> None:
    data = [Fraction(n) for n in (2, 4, 4, 4, 5, 5, 7, 9)]
    assert str(cas.standard_deviation(data)) == "2"


# --------------------------------------------------------------------------
# the CAS tour, reproduced from Python
# --------------------------------------------------------------------------
#
# These three strings are what `crates/axeyum-cas/examples/cas_tour.rs` prints,
# reproduced through the binding. If the Python surface ever renders something
# else for the same call sequence, the projection has drifted from the Rust API
# it claims to be.


def test_cas_tour_derivative_line() -> None:
    f = x().pow(3) - i(2) * x() + i(1)
    assert str(f) == "(x^3 - (2*x)) + 1"
    assert str(cas.expand(f.differentiate("x"))) == "3*x^2 - 2"


def test_cas_tour_certified_integral_lines() -> None:
    for integrand, expected in [
        (i(1) / x(), "ln(x)"),
        (i(1) / (x().pow(2) + i(1)), "atan(x)"),
        (x() * x().exp(), "(x - 1)*exp(x)"),
    ]:
        result = cas.integrate(integrand, "x")
        assert result is not None and result.is_certified()
        assert str(result.antiderivative) == expected


def test_cas_tour_algebra_lines() -> None:
    poly = x().pow(2) - i(3) * x() + i(2)
    assert str(cas.factor(poly, "x")) == "(x - 1)*(x - 2)"
    assert [str(root) for root in cas.solve(poly, "x")] == ["1", "2"]
    assert str(cas.series(x().exp(), "x", 4)) == "(1/24)*x^4 + (1/6)*x^3 + (1/2)*x^2 + x + 1"
    assert str(cas.apart(i(1) / (x().pow(2) - i(1)), "x")) == "(1/2)/(x - 1) + (-1/2)/(x + 1)"
