"""``axeyum.m`` -- the Mathematica-shaped verbs are a faithful, Python-only layer."""

from __future__ import annotations

import pytest

from axeyum import cas, m


def test_simplify_and_factor_from_a_string() -> None:
    assert m.show(m.Simplify("x*x + 5*x + 6")) == "x^2 + 5*x + 6"
    assert m.show(m.Factor("x^2 + 5 x + 6")) == "(x + 2)*(x + 3)"


def test_parser_accepts_mathematica_spellings() -> None:
    assert m.show(m.Expand("(x+2)(x+3)")) == "x^2 + 5*x + 6"
    assert m.show(m.Simplify("Sin[x]^2 + Cos[x]^2")) in {"sin(x)^2 + cos(x)^2", "1"}
    assert m.show(m.TrigSimplify("Sin[x]^2 + Cos[x]^2")) == "1"
    assert m.show(m.Simplify("2x - 3x")) == "-x"


def test_parser_refuses_what_it_cannot_represent() -> None:
    with pytest.raises(TypeError, match="integer literals"):
        m.parse("0.5*x")
    with pytest.raises(ValueError, match="unknown function"):
        m.parse("foo(x)")
    with pytest.raises(ValueError, match="cannot parse"):
        m.parse("x +")
    with pytest.raises(ValueError, match="exponents"):
        m.parse("x^y")


def test_variable_inference_never_guesses() -> None:
    assert m.show(m.Factor("y^2 - 1")) == "(y - 1)*(y + 1)"
    with pytest.raises(ValueError, match="name the variable"):
        m.Factor("x*y + y")
    # The Rust factoriser declines multivariate input: `None`, never a guess.
    assert m.Factor("x*y + y", "y") is None


def test_calculus_verbs() -> None:
    assert m.show(m.D("x^3")) == "3*x^2"
    assert m.show(m.D("x^3", n=2)) == "6*x"
    assert m.show(m.Integrate("x^2 + 5 x + 6")) == "(1/3)*x^3 + (5/2)*x^2 + 6*x"
    assert m.show(m.Series("exp(x)", order=2)) == "(1/2)*x^2 + x + 1"
    assert str(m.Limit("(x^2 - 1)/(x - 1)", 1)) == "2"
    assert m.N("x^2 + 5 x + 6", x=2.5) == 24.75


def test_solve_returns_expr_roots() -> None:
    roots = m.Solve("x^2 + 5 x + 6")
    assert roots is not None
    assert sorted(str(r) for r in roots) == ["-2", "-3"]


def test_results_keep_their_certificates() -> None:
    # The layer is sugar: the Rust certificate is still reachable on the Rust result.
    p = m.parse("x^2 + 5 x + 6")
    assert cas.equal(m.Expand("(x+2)(x+3)"), p).certainty() == cas.Certainty.Certified
    assert cas.integrate(p, "x").certificate.certainty() == cas.Certainty.Certified


def test_show_only_folds_signs_and_never_reorders() -> None:
    assert m.show(m.parse("x - 2")) == "x - 2"
    assert m.show(None) == "None"
    assert m.show(cas.factor(m.parse("x^2 - 1"), "x")) == "(x - 1)*(x + 1)"


def test_equations_parse_as_their_difference() -> None:
    assert m.show(m.Solve("2x + 3 = 7")) == "[2]"
    assert m.show(m.Solve("x^2 == 4")) == "[2, -2]"
    with pytest.raises(ValueError, match="one `=`"):
        m.parse("x <= 3")
    with pytest.raises(ValueError, match="one `=`"):
        m.parse("a = b = c")


def test_simplify_with_assumptions() -> None:
    assert m.show(m.Simplify("exp(ln(x))")) == "exp(ln(x))"
    assert m.show(m.Simplify("exp(ln(x))", assume={"x": "positive"})) == "x"
    with pytest.raises(ValueError, match="must be one of"):
        m.Simplify("x", assume={"x": "big"})


def test_limit_at_infinity() -> None:
    assert str(m.Limit("1/x", "inf")) == "0"
    assert str(m.Limit("1/x", float("-inf"))) == "0"
    assert str(m.Limit("(x^2 - 1)/(x - 1)", 1)) == "2"


def test_show_renders_lists() -> None:
    assert m.show([m.parse("x"), None]) == "[x, None]"


def test_systems_definite_integrals_substitution() -> None:
    assert m.Solve(["x + y = 3", "x - y = 1"], ["x", "y"]) == [
        {"x": m.parse("2"), "y": m.parse("1")}
    ]
    circle = m.Solve(["x^2 + y^2 = 1", "x = y"], ["x", "y"])
    assert circle is not None and len(circle) == 2
    with pytest.raises(TypeError, match="variables as a list"):
        m.Solve(["x + y = 3"])
    assert str(m.Integrate("x^2", ("x", 0, 1))) == "1/3"
    assert m.show(m.Substitute("x^2 + 1", x="y + 1")) == "(y + 1)^2 + 1"
    assert m.show(m.ReplaceAll("x^2 + 1", x=3)) == "3^2 + 1"


def test_equal_is_semantic_and_never_answers_false_for_undecided() -> None:
    assert m.parse("1 + x") != m.parse("x + 1")
    assert m.Equal("1 + x", "x + 1") is True
    assert m.Equal("(x+2)(x+3)", "x^2 + 5x + 6") is True
    assert m.Equal("x", "x + 1") is False


def test_constants_are_refused_not_silently_symbolised() -> None:
    with pytest.raises(ValueError, match="exact over Q"):
        m.parse("pi * x")
    assert "I" in m.show(m.parse("I * I"))  # rendered as Rust spells the imaginary unit


def test_mixed_arithmetic_with_python_numbers() -> None:
    from fractions import Fraction

    x = m.parse("x")
    assert m.show(x + 1) == "x + 1"
    assert m.show(1 + x) == "1 + x"
    assert m.show(2 * x) == "2*x"
    assert m.show(x / 2) == "x/2"
    assert m.show(1 - x) == "1 - x"
    assert m.show(x - Fraction(1, 3)) == "x - (1/3)"  # a rational keeps its parentheses
    assert m.show(Fraction(1, 2) / x) == "(1/2)/x"
    with pytest.raises(TypeError):
        _ = x + 0.5  # a float is not exact; write Fraction(1, 2)


def test_sums_are_exact() -> None:
    assert m.show(m.Sum("k", ("k", 1, "n"))) == "(1/2)*n^2 + (1/2)*n"
    assert m.show(m.Sum("k^2", ("k", 1, "n"))) == "(1/3)*n^3 + (1/2)*n^2 + (1/6)*n"
    assert str(m.Sum("k", ("k", 1, 100))) == "5050"
    with pytest.raises(ValueError, match="symbolic power"):
        m.Sum("1/2^k", ("k", 0, None))


def test_reduce_renders_interval_unions() -> None:
    inside = m.Reduce("x^2 - 4 < 0")
    assert inside is not None and [m.interval(i) for i in inside] == ["-2 < x < 2"]
    outside = m.Reduce("x^2 >= 4")
    assert outside is not None and [m.interval(i) for i in outside] == ["x <= -2", "2 <= x"]
    with pytest.raises(ValueError, match="exactly one of"):
        m.Reduce("x^2 - 4")


def test_polynomial_toolkit() -> None:
    from fractions import Fraction

    assert str(m.Rationalize(0.5)) == "1/2"
    roots = m.NRoots("x^2 - 2")
    assert roots is not None and len(roots) == 2
    assert abs(float(roots[1]) - 2**0.5) < 1e-6
    assert isinstance(roots[1], Fraction)
    assert m.Degree("x^3 + x") == 3
    assert m.Degree("sin(x)") is None
    assert str(m.Resultant("x^2 - 1", "x - 1", "x")) == "0"
    assert str(m.Discriminant("x^2 - 4")) == "16"
    q, r = m.PolynomialQuotientRemainder("x^3 - 1", "x - 1", "x")
    assert (m.show(q), str(r)) == ("x^2 + x + 1", "0")


# ---------------------------------------------------------------------------
# The long-tail verbs (coverage-plan slice S5). Each is a renaming of one
# `axeyum.cas` call, so the tests check the renaming AND that `None` survives
# it: a verb that substituted a default where the CAS declined would be
# inventing an answer.
# ---------------------------------------------------------------------------


def test_number_theory_verbs() -> None:
    assert m.PrimeQ(97) and not m.PrimeQ(1)
    assert m.FactorInteger(360) == [(2, 3), (3, 2), (5, 1)]
    assert m.FactorInteger(1) == []
    assert m.Divisors(12) == [1, 2, 3, 4, 6, 12]
    assert m.DivisorSigma(1, 12) == 28
    assert m.EulerPhi(12) == 4
    assert m.MoebiusMu(30) == -1
    assert m.GCD(12, 18) == 6
    assert m.LCM(4, 6) == 12
    assert m.PowerMod(2, 10, 1000) == 24
    assert m.ModularInverse(3, 7) == 5
    assert m.ModularInverse(4, 6) is None
    assert m.ChineseRemainder([2, 3], [3, 5]) == (8, 15)
    assert m.ChineseRemainder([1, 0], [2, 4]) is None
    assert m.JacobiSymbol(2, 15) == 1
    assert m.PrimitiveRoot(7) == 3
    assert m.PrimitiveRoot(8) is None
    assert m.MultiplicativeOrder(2, 7) == 3
    assert m.NextPrime(10) == 11
    assert m.Prime(10) == 29
    assert m.PrimePi(10) == 4


def test_continued_fraction_takes_a_fraction_or_a_pair() -> None:
    from fractions import Fraction

    assert m.ContinuedFraction((22, 7)) == [3, 7]
    assert m.ContinuedFraction(Fraction(22, 7)) == [3, 7]


def test_combinatorics_verbs() -> None:
    assert m.Binomial(5, 2) == 10
    assert m.Binomial(5, 9) == 0
    assert m.Fibonacci(30) == 832040
    assert m.Fibonacci(200) is None  # i128 overflow is a value
    assert m.LucasL(10) == 123
    assert m.CatalanNumber(10) == 16796
    assert m.BellB(5) == 52
    assert m.PartitionsP(10) == 42
    assert m.StirlingS1(5, 2) == 50
    assert m.StirlingS2(5, 2) == 15


def test_bernoulli_verb_uses_the_first_kind_convention() -> None:
    from fractions import Fraction

    assert m.BernoulliB(1) == Fraction(-1, 2)
    assert m.BernoulliB(2) == Fraction(1, 6)
    assert "first kind" in (m.BernoulliB.__doc__ or "")


def test_statistics_verbs_default_to_the_sample_form() -> None:
    from fractions import Fraction

    data = [1, 2, 3, 4]
    assert m.Mean(data) == Fraction(5, 2)
    assert m.Median(data) == Fraction(5, 2)
    assert m.Variance(data) == Fraction(5, 3)  # sample, as in Mathematica
    assert m.Variance(data, population=True) == Fraction(5, 4)
    assert m.Mean([]) is None
    sigma = m.StandardDeviation(data)
    assert sigma is not None
    assert cas.equal(sigma * sigma, cas.Expr.rat(5, 3)).equal is True


def test_special_function_verbs() -> None:
    from fractions import Fraction

    assert str(m.Zeta(2)) == "(1/6)*pi^2"
    assert m.Zeta(3) is None  # no closed form: a decided None
    assert str(m.Gamma(4)) == "6"
    assert m.Gamma(Fraction(1, 3)) is None
    assert m.Beta(Fraction(2), Fraction(3)) is not None
    assert m.show(m.LegendreP(1)) == "x"
    assert m.show(m.ChebyshevT(2)) == "2*x^2 - 1"
    assert m.ChebyshevU(2) is not None
    assert m.HermiteH(2) is not None
    assert m.LaguerreL(2) is not None


def test_transform_verbs_round_trip() -> None:
    assert str(m.LaplaceTransform("t^2")) == "2/s^3"
    assert m.LaplaceTransform("ln(t)") is None  # outside the table
    back = m.InverseLaplaceTransform("2/s^3")
    assert back is not None
    assert cas.equal(back, m.parse("t^2")).equal is True
    forward = m.ZTransform("n")
    assert forward is not None and str(forward) == "z/(z - 1)^2"
    assert m.InverseZTransform(forward) is not None


def matrix_of(rows: list[list[int]]) -> cas.Matrix:
    built = cas.Matrix.from_rows([[cas.Expr.int(v) for v in row] for row in rows])
    assert built is not None
    return built


def test_matrix_decomposition_verbs_return_their_factors() -> None:
    a = matrix_of([[5, 4], [1, 2]])
    jordan = m.JordanDecomposition(a)
    assert jordan is not None
    p, j = jordan
    left, right = a.mul(p), p.mul(j)
    assert left is not None and right is not None
    assert all(
        cas.equal(left.get(r, c), right.get(r, c)).equal is True for r in range(2) for c in range(2)
    )
    assert m.JordanDecomposition(matrix_of([[0, 1], [-1, 0]])) is None
    assert m.MatrixExp(a) is not None
    hermite = m.HermiteDecomposition(a)
    assert hermite is not None
    smith = m.SmithDecomposition(a)
    assert smith is not None and len(smith) == 3
    qr = m.QRDecomposition(matrix_of([[1, 0], [0, 1]]))
    assert qr is not None
    assert m.CholeskyDecomposition(matrix_of([[2, 1], [1, 2]])) is not None


def test_every_new_verb_is_exported() -> None:
    for name in (
        "PrimeQ",
        "FactorInteger",
        "Binomial",
        "BernoulliB",
        "LaplaceTransform",
        "JordanDecomposition",
        "HermiteDecomposition",
        "SmithDecomposition",
        "Zeta",
        "Mean",
    ):
        assert name in m.__all__
        assert getattr(m, name).__doc__, f"{name} has no docstring"
