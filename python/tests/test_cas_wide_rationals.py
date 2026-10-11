"""Wide exact transport, independent payment oracle, and negative controls."""
from fractions import Fraction
import sys

import pytest
from axeyum import BudgetExceeded, cas


@pytest.mark.parametrize("num,den", [(2**193 + 7, 2**151 + 3), (-(2**193 + 7), 2**151 + 3), (2**193 + 7, -(2**151 + 3)), (0, 2**300 + 1)])
def test_wide_rational_round_trip(num, den):
    expected = Fraction(num, den)
    value = cas.Rational(num, den)
    assert (value.numerator, value.denominator) == (expected.numerator, expected.denominator)
    assert value.to_fraction() == expected
    assert cas.Rational.coerce(expected).to_fraction() == expected
    assert repr(value) == f"Rational({expected.numerator}, {expected.denominator})"
    assert str(value) == str(expected)
    assert hash(value) == hash(expected)
    assert {value: "exact"}[expected] == "exact"


def test_integer_constructor_default_and_numeric_hash_agree():
    number = 2**300 + 11
    value = cas.Rational(number)
    assert value.numerator == number
    assert value.denominator == 1
    assert value == number
    assert hash(value) == hash(number)
    assert cas.Expr.int(number).eval({}) == number
    assert cas.Expr.rat(number).eval({}) == number


def test_wide_expression_operands_environment_and_rendering():
    number = 2**193 + 7
    ratio = Fraction(number, 2**151 + 3)
    x = cas.Expr.var("x")
    expression = (x + number) * ratio / cas.Rational(number)
    assert expression.eval({"x": ratio}) == (ratio + number) * ratio / number
    assert cas.Expr.rat(ratio.numerator, ratio.denominator).eval({}) == ratio
    assert str(cas.Expr.int(-number)) == str(-number)
    assert str(cas.Expr.rat(ratio.numerator, ratio.denominator)) == str(ratio)


def test_thirty_year_payment_matches_independent_fraction_oracle():
    principal = 300000
    rate = Fraction(1, 240)
    expected = principal * rate / (1 - (1 + rate) ** -360)
    factor = cas.Expr.rat(241, 240).pow(360)
    payment = cas.Expr.int(principal) * rate * factor / (factor - 1)
    result = payment.eval({})
    assert result == expected
    assert result.numerator.bit_length() > 128
    assert result.denominator.bit_length() > 128
    assert cas.Rational.coerce(result).to_fraction() == expected
    assert (cas.Expr.int(principal) / 360).eval({}) == Fraction(principal, 360)


def test_transport_ignores_python_decimal_string_limit():
    previous = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640)
        number = 2**3000 + 7
        assert cas.Rational(number, 3).to_fraction() == Fraction(number, 3)
        assert cas.Expr.int(number).eval({}) == number
    finally:
        sys.set_int_max_str_digits(previous)


def test_invalid_and_resource_inputs_fail_explicitly():
    for constructor in (cas.Rational, cas.Expr.rat):
        with pytest.raises(ValueError):
            constructor(1, 0)
        with pytest.raises(TypeError):
            constructor(1.5, 2)
        with pytest.raises(ValueError, match="16384"):
            constructor(1 << 16384, 1)
        with pytest.raises(ValueError, match="16384"):
            constructor(1, 1 << 16384)
    with pytest.raises(ValueError, match="16384"):
        cas.Expr.var("x") + (1 << 16384)


def test_integer_subclass_methods_cannot_change_transported_value():
    class MisleadingInt(int):
        def bit_length(self):
            return 0
        def to_bytes(self, *args, **kwargs):
            return b"\x01"
    number = MisleadingInt(2**200 + 3)
    assert cas.Rational(number).to_fraction() == Fraction(2**200 + 3)
    assert cas.Rational.coerce(number).to_fraction() == Fraction(2**200 + 3)
    with pytest.raises(ValueError, match="16384"):
        cas.Rational(MisleadingInt(1 << 16384))


def test_output_resource_and_undefined_values_remain_distinct():
    with pytest.raises(BudgetExceeded, match="16384"):
        cas.Expr.int(2).pow(20000).eval({})
    assert (cas.Expr.int(1) / 0).eval({}) is None
    assert cas.Expr.var("missing").eval({}) is None


@pytest.mark.parametrize("value", [Fraction(2**200 + 7, 3), Fraction(-(2**200 + 7), 3), Fraction(-(2**127))])
def test_wide_constant_unary_folds_and_negative_product_render(value):
    expression = cas.Expr.rat(value.numerator, value.denominator)
    assert expression.abs().eval({}) == abs(value)
    assert expression.sign().eval({}) == (value > 0) - (value < 0)
    assert expression.floor().eval({}) == value.numerator // value.denominator
    assert expression.ceiling().eval({}) == -(-value.numerator // value.denominator)
    negative = cas.Expr.rat(-abs(value.numerator), value.denominator)
    rendered = str(negative * cas.Expr.var("x"))
    assert rendered.startswith("-")
    assert "x" in rendered
