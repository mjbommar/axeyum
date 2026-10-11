"""Distinguished mathematical pi and ordinary variables must keep separate semantics."""
import math
from fractions import Fraction

import pytest
from axeyum import cas


def test_constant_and_variable_keep_distinct_binding_and_substitution() -> None:
    pi, variable = cas.Expr.pi(), cas.Expr.var("pi")
    assert pi.variables() == []
    assert variable.variables() == ["pi"]
    assert pi.differentiate("pi").eval({}) == Fraction(0)
    assert variable.differentiate("pi").eval({}) == Fraction(1)
    assert cas.evalf(pi.substitute("pi", cas.Expr.int(2)), {"pi": 2.0}) == math.pi
    assert variable.substitute("pi", cas.Expr.int(2)).eval({}) == Fraction(2)
    assert pi.eval({"pi": 2}) is None
    assert variable.eval({"pi": 2}) == Fraction(2)
    assert cas.evalf(variable, {}) is None


@pytest.mark.parametrize("text", ["pi", "π", "(pi)", "π+0", "pi^1"])
def test_parser_constructs_constant_without_a_free_variable(text: str) -> None:
    expression = cas.parse(text)
    assert expression.variables() == []
    assert cas.evalf(expression, {"pi": 2.0}) == math.pi
    assert expression.eval({"pi": 2}) is None


def test_exact_trig_recognizes_only_the_constant() -> None:
    assert cas.evaluate_trig(cas.Expr.pi().sin()).eval({}) == Fraction(0)
    source = cas.Expr.var("pi").sin()
    rewritten = cas.evaluate_trig(source)
    assert cas.evalf(rewritten, {"pi": 2.0}) == math.sin(2.0)
    source = (2 * cas.Expr.var("pi")).cos()
    assert cas.evalf(cas.evaluate_trig(source), {"pi": 2.0}) == math.cos(4.0)


def test_constant_and_named_variable_can_coexist() -> None:
    expression = cas.parse("pi+x") + cas.Expr.var("pi")
    assert expression.variables() == ["pi", "x"]
    assert cas.evalf(expression, {"pi": 2.0, "x": 1.0}) == math.pi + 3.0


def test_pi_value_inequalities_are_not_polynomial_certificates() -> None:
    pi = cas.Expr.pi()
    for left, right in [(pi.pow(2), cas.Expr.int(0)),
                        (pi.exp(), cas.Expr.int(2)),
                        (pi.sin(), cas.Expr.int(1))]:
        result = cas.equal(left, right)
        assert result.kind == "unknown"
        assert result.equal is None
    identity = cas.equal(pi + pi, 2 * pi)
    assert identity.equal is True
    assert identity.witness is not None
    assert identity.witness.is_zero()


def test_internal_atom_spelling_cannot_replace_a_constant_expression() -> None:
    result = cas.equal(cas.Expr.pi().exp(), cas.Expr.var("\0exp:Pi"))
    assert result.kind == "unknown"
    assert result.equal is None
