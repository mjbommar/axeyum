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
