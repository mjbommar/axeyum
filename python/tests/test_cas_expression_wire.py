"""Canonical source transport is separate from human display and certification."""
import json
from fractions import Fraction

import pytest
from axeyum import BudgetExceeded
from axeyum.cas import Expr


def test_pi_variable_and_wide_exact_source_round_trip():
    pi, variable = Expr.pi(), Expr.var("pi")
    assert str(pi) == str(variable)
    assert pi.to_json() == '{"version":1,"expression":{"kind":"pi"}}'
    assert pi.to_json() != variable.to_json()
    value = Fraction((1 << 512) + 1, 7)
    expr = pi + variable + Expr.rat(value.numerator, value.denominator)
    restored = Expr.from_json(expr.to_json())
    assert restored == expr
    assert restored.to_json() == expr.to_json()
    assert Expr.from_json(variable.to_json()).eval({"pi": 2}) == 2
    assert Expr.from_json(pi.to_json()).eval({"pi": 2}) is None
    assert Expr.from_json(Expr.rat(value.numerator, value.denominator).to_json()).eval({}) == value


def test_operators_and_reserved_names_preserve_syntax():
    name = '\0constant:pi"\\\nπ'
    expressions = [Expr.var(name), -Expr.pi(), Expr.pi().pow(-3),
                   Expr.var("x").sin(), Expr.var("x").exp(),
                   Expr.var("x") / Expr.int(0)]
    for expr in expressions:
        restored = Expr.from_json(expr.to_json())
        assert restored == expr
        assert restored.to_json() == expr.to_json()
    assert Expr.from_json(expressions[0].to_json()).eval({name: 7}) == 7


@pytest.mark.parametrize("encoded", [
    '{"version":1,"version":1,"expression":{"kind":"pi"}}',
    '{"version":2,"expression":{"kind":"pi"}}',
    '{"version":1,"expression":{"kind":"pi","args":"pi"}}',
    '{"version":1,"expression":{"kind":"const","args":{"numerator":"2","denominator":"4"}}}',
    '{"version":1,"expression":{"kind":"const","args":{"numerator":"1","denominator":"0"}}}',
])
def test_invalid_encoding_rejects(encoded):
    with pytest.raises(ValueError):
        Expr.from_json(encoded)


def test_resource_caps_reject_both_directions():
    with pytest.raises(BudgetExceeded):
        Expr.from_json(" " * 1_048_577)
    e = Expr.pi()
    for _ in range(31):
        e = -e
    assert Expr.from_json(e.to_json()) == e
    with pytest.raises(BudgetExceeded):
        (-e).to_json()
    wire = json.loads(e.to_json())
    wire["expression"] = {"kind": "neg", "args": wire["expression"]}
    with pytest.raises(BudgetExceeded):
        Expr.from_json(json.dumps(wire))
    with pytest.raises(BudgetExceeded):
        Expr.var("a" * 1025).to_json()
