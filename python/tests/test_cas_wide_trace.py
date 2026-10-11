"""Wide traces certify exact arithmetic and every constant-divisor domain."""
from fractions import Fraction
import json
import os
import subprocess
import sys

import pytest
from axeyum import cas


def payment_expression(principal, rate, periods):
    if rate == 0:
        return cas.Expr.int(principal) / periods
    factor = 1 + cas.Expr.rat(rate.numerator, rate.denominator)
    return cas.Expr.int(principal) * rate / (1 - factor ** -periods)


@pytest.mark.parametrize("principal,rate", [(300000, Fraction(1, 240)), (0, Fraction(1, 240)),
                                          (300000, Fraction(-1, 240)), (300000, Fraction(0))])
def test_amortization_matches_independent_exact_fractions(principal, rate):
    source = payment_expression(principal, rate, 360)
    outcome = cas.normalize_trace(source, wide=True)
    assert outcome.status == "produced" and outcome.trace is not None
    trace = outcome.trace
    expected = Fraction(principal, 360) if rate == 0 else principal * rate / (1 - (1 + rate) ** -360)
    assert trace.result.eval({}) == expected
    assert str(trace.input) == str(source)
    assert trace.replay(source, trace.result).status == "checked"
    data = json.loads(trace.to_json())
    assert data["version"] == "cas-polynomial-trace-v2"
    divisions = [step for step in data["steps"] if step["rule"] == "rational.div.constant.v2"]
    assert len(divisions) == (1 if rate == 0 else 2)
    assert all(len(step["side_conditions"]) == 1 for step in divisions)
    assert cas.replay_trace(trace.to_json(), source, trace.result).status == "checked"
    if principal and rate:
        assert expected.numerator.bit_length() > 128 and expected.denominator.bit_length() > 128


def test_wide_is_explicit_and_narrow_behavior_is_preserved():
    x = cas.Expr.var("x")
    source = cas.Expr.rat(2**200, 3) * (x + x)
    assert cas.normalize_trace(source).status == "resource_limited"
    outcome = cas.normalize_trace(source, wide=True)
    assert outcome.status == "produced"
    assert outcome.trace.result.eval({"x": Fraction(2, 5)}) == Fraction(2**202, 15)
    assert cas.replay_trace(outcome.trace.to_json(), source, outcome.trace.result).status == "checked"


@pytest.mark.parametrize("change", ["condition", "witness", "context", "version", "canonical", "truncate"])
def test_corrupted_wide_evidence_is_rejected(change):
    source = cas.Expr.int(1) / 2
    trace = cas.normalize_trace(source, wide=True).trace
    data = json.loads(trace.to_json())
    if change == "condition":
        data["steps"][0]["side_conditions"] = []
    elif change == "witness":
        data["steps"][0]["witness"] = {"kind": "const", "args": {"numerator": "2", "denominator": "1"}}
    elif change == "context":
        data["steps"][0]["context"] = "empty-v1"
    elif change == "version":
        data["version"] = "cas-polynomial-trace-v1"
    elif change == "canonical":
        data["steps"][0]["witness"]["args"]["numerator"] = "01"
    else:
        data["steps"] = []
    outcome = cas.replay_trace(json.dumps(data), source, trace.result)
    assert outcome.status in {"rejected", "unsupported"} and outcome.trace is None


def test_zero_divisor_symbolic_divisor_and_resource_limits_decline():
    assert cas.normalize_trace(cas.Expr.int(1) / 0, wide=True).status == "rejected"
    assert cas.normalize_trace(cas.Expr.int(1) / cas.Expr.var("x"), wide=True).status == "unsupported"
    assert cas.normalize_trace(cas.Expr.int(2**16383) * 2, wide=True).status == "resource_limited"
    assert cas.normalize_trace(cas.Expr.int(2)**513, wide=True).status == "resource_limited"
    assert cas.normalize_trace(cas.Expr.var("x")**33, wide=True).status == "resource_limited"
    assert cas.normalize_trace(cas.Expr.int(1) / 2, wide=True, max_work=0).status == "resource_limited"


def test_separate_process_replays_wide_bytes_without_the_producer(tmp_path):
    source = payment_expression(300000, Fraction(1, 240), 360)
    trace = cas.normalize_trace(source, wide=True).trace
    path = tmp_path / "payment-trace.json"
    path.write_text(trace.to_json())
    code = """from pathlib import Path
from fractions import Fraction
import sys
from axeyum import cas
r = Fraction(1,240)
source = cas.Expr.int(300000)*r/(1-(1+cas.Expr.rat(1,240))**-360)
expected = 300000*r/(1-(1+r)**-360)
def forbidden(*args, **kwargs):
    raise AssertionError('trace producer must not run during replay')
cas.normalize_trace = forbidden
outcome = cas.replay_trace(Path(sys.argv[1]).read_text(), source,
                           cas.Expr.rat(expected.numerator, expected.denominator))
assert outcome.status == 'checked' and outcome.trace.result.eval({}) == expected
print('exact wide payment checked')
"""
    result = subprocess.run([sys.executable, "-c", code, str(path)], env=os.environ.copy(),
                            capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "exact wide payment checked"
