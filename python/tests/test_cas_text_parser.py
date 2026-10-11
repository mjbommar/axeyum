"""Text input agrees with exact arithmetic and preserves partial domains."""
from fractions import Fraction
import pytest
from axeyum import cas


@pytest.mark.parametrize('text,value', [('-2^2', -4), ('(-2)^2', 4), ('2^-3', Fraction(1, 8)), ('8/2/2', 2), ('0.1 + 0.2', Fraction(3, 10)), ('2**+3', 8), ('0^0', 1)])
def test_exact_precedence_and_literals(text, value):
    assert cas.parse(text).eval({}) == value


def test_constructor_agreement_and_amortization():
    x = cas.Expr.var('x')
    assert cas.parse('sin(x) + x^-2') == x.sin() + x.pow(-2)
    expected = 300000 * Fraction(1, 240) / (1 - Fraction(241, 240)**-360)
    assert cas.parse('300000*(1/240)/(1-(1+1/240)^-360)').eval({}) == expected
    assert cas.parse('x^-1').eval({'x': 0}) is None
    assert cas.parse('1/0').eval({}) is None
    assert cas.parse('(1/0)^0').eval({}) is None
    assert cas.parse('x^-1').eval({}) is None


@pytest.mark.parametrize('text', ['', '1+', '2x', 'x.y', 'x[0]', 'f(x)', 'sin(x,y)', '2^0.5', '2^2^3', '1e3', '__import__(x)', '(' * 34 + '1' + ')' * 34, '1+' * 33 + '1', '9'*1025, ' '*8193, '+'*513, '2^4294967296'])
def test_malformed_and_resource_inputs_have_spans(text):
    with pytest.raises(cas.ParseError) as error:
        cas.parse(text)
    assert 0 <= error.value.start <= error.value.end <= len(text)


def test_zero_divisor_seed_class_fraction_differential():
    import random
    rng = random.Random(3100)
    cases = [(1, 0, -1), (0, 1, 0)] + [(rng.randint(-20, 20), rng.randint(0, 20), rng.randint(-4, 4)) for _ in range(80)]
    assert any(den == 0 for _, den, _ in cases)
    for num, den, exponent in cases:
        expected = None if den == 0 or (num == 0 and exponent < 0) else (Fraction(num, den) ** exponent)
        assert cas.parse(f'({num}/{den})^{exponent}').eval({}) == expected
