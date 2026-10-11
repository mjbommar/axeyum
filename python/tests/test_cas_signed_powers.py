"""Signed powers preserve partial rational semantics and existing limits."""
from fractions import Fraction
import pytest
from axeyum import BudgetExceeded, cas


@pytest.mark.parametrize("base,exponent", [(2, -3), (-2, -3), (Fraction(2, 3), -3), (Fraction(-2, 3), -2), (Fraction(2, 3), 4), (0, 0)])
def test_signed_power_exact_value_and_operator_agree(base, exponent):
    expression = cas.Expr.rat(base.numerator, base.denominator)
    expected = Fraction(base) ** exponent
    assert expression.pow(exponent).eval({}) == expected
    assert (expression ** exponent).eval({}) == expected
    assert expression.pow(exponent) == expression ** exponent


def test_symbolic_inverse_requires_nonzero_concrete_binding():
    inverse = cas.Expr.var("x") ** -3
    assert inverse.eval({}) is None
    assert inverse.eval({"x": 0}) is None
    assert inverse.eval({"x": -2}) == Fraction(-1, 8)
    assert (cas.Expr.int(0) ** -1).eval({}) is None
    assert ((cas.Expr.int(1) / 0) ** 0).eval({}) is None


def test_thirty_year_payment_uses_negative_power_directly():
    principal, rate = 300000, Fraction(1, 240)
    expected = principal * rate / (1 - (1 + rate) ** -360)
    payment = cas.Expr.int(principal) * rate / (1 - (cas.Expr.rat(241, 240) ** -360))
    assert payment.eval({}) == expected
    assert expected.numerator.bit_length() > 128
    witness = cas.equal(payment, cas.Expr.rat(expected.numerator, expected.denominator))
    assert witness.equal is True
    assert witness.kind in ("certified", "certified-big")


def test_signed_exponent_limits_and_types_are_explicit():
    one = cas.Expr.int(1)
    for exponent in (4294967295, -4294967295):
        assert one.pow(exponent).eval({}) == 1
        assert (one ** exponent).eval({}) == 1
    for exponent in (4294967296, -4294967296, -(1 << 63), (1 << 63) - 1):
        with pytest.raises(ValueError, match="4294967295"):
            one.pow(exponent)
        with pytest.raises(ValueError, match="4294967295"):
            one ** exponent
    with pytest.raises(OverflowError):
        one.pow(1 << 200)
    with pytest.raises(TypeError):
        one.pow(Fraction(1, 2))
    with pytest.raises(TypeError):
        one ** 0.5
    with pytest.raises(TypeError):
        pow(one, -1, 7)
    with pytest.raises(BudgetExceeded):
        (cas.Expr.int(2) ** -20000).eval({})


def test_seeded_fraction_fuzz_includes_degenerate_power_domains():
    import random
    rng = random.Random(0x3000)
    cases = [(Fraction(0), -1), (Fraction(0), -10), (Fraction(0), 0)]
    cases += [(Fraction(rng.randint(-20, 20), rng.randint(1, 20)), rng.randint(-10, 10)) for _ in range(256)]
    assert any(base == 0 and exponent < 0 for base, exponent in cases)
    for base, exponent in cases:
        expression = cas.Expr.rat(base.numerator, base.denominator) ** exponent
        expected = None if base == 0 and exponent < 0 else base ** exponent
        assert expression.eval({}) == expected
    # Guaranteed seed classes beyond a concrete zero base.
    assert ((cas.Expr.int(1) / 0) ** 0).eval({}) is None
    assert (cas.Expr.var("missing") ** 0).eval({}) is None
