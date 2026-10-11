"""Public approximation must accept promoted constants without a panic."""
from fractions import Fraction
import math
import pytest
from axeyum import cas


@pytest.mark.parametrize('value', [Fraction(1 << 192), Fraction(1, 1 << 192), Fraction((1 << 4096) + 1, 3 * (1 << 4096) + 1), Fraction(-((1 << 4096) + 1), 3 * (1 << 4096) + 1)])
def test_promoted_approximation_matches_independent_fraction(value):
    expression = cas.Expr.rat(value.numerator, value.denominator)
    approximation = cas.evalf(expression, {})
    assert math.isfinite(approximation)
    assert approximation == float(value)
    assert cas.evalf(expression.sin(), {}) == math.sin(float(value))


def test_wide_payment_approximation_preserves_exact_result():
    rate = Fraction(1, 240)
    exact = 300000 * rate / (1 - (1 + rate)**-360)
    expression = cas.Expr.rat(exact.numerator, exact.denominator)
    assert cas.evalf(expression, {}) == float(exact)
    assert expression.eval({}) == exact
    assert cas.evalf(cas.Expr.var('missing'), {}) is None
