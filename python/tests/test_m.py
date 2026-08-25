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
