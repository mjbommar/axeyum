"""Wide conditional traces bind the exact subject, endpoint and nonzero context."""
import json
import os
import subprocess
import sys
from fractions import Fraction

import pytest
from axeyum import cas


def fixture():
    x = cas.Expr.var("x")
    coefficient = Fraction(2**200, 3)
    numerator = x * coefficient
    outcome = cas.cancel_trace(numerator, x, nonzero=[x], wide=True)
    assert outcome.status == "produced", outcome.detail
    assert outcome.trace is not None
    return x, numerator, coefficient, outcome.trace


def test_exact_wide_endpoint_and_serialized_conditional_replay():
    x, numerator, coefficient, trace = fixture()
    assert trace.result.eval({}) == coefficient
    assert [str(p) for p in trace.nonzero_assumptions] == ["x"]
    assert cas.cancel_trace(numerator, x, nonzero=[x]).status != "produced"
    wire = json.loads(trace.to_json())
    assert wire["version"] == "cas-guarded-quotient-v2"
    for key in ["numerator_identity", "product_identity"]:
        assert wire[key]["version"] == "cas-polynomial-trace-v2"
    expected = cas.Expr.rat(coefficient.numerator, coefficient.denominator)
    checked = cas.replay_guarded_trace(trace.to_json(), numerator, x, expected, nonzero=[x])
    assert checked.status == "checked", checked.detail
    assert checked.trace.result.eval({}) == coefficient
    assert cas.cancel_trace(numerator, x, nonzero=[x], wide=True).trace.to_json() == trace.to_json()


@pytest.mark.parametrize("change", ["context", "result", "subject", "version", "identity_version", "premise", "witness"])
def test_external_and_carried_corruptions_reject(change):
    x, numerator, coefficient, trace = fixture()
    wire = json.loads(trace.to_json())
    expected = cas.Expr.rat(coefficient.numerator, coefficient.denominator)
    context = [x]
    if change == "context":
        context.append(cas.Expr.var("y"))
    elif change == "result":
        expected = expected + 1
    elif change == "subject":
        numerator = numerator + 1
    elif change == "version":
        wire["version"] = "cas-guarded-quotient-v1"
    elif change == "identity_version":
        wire["numerator_identity"]["version"] = "cas-polynomial-trace-v1"
    elif change == "premise":
        wire["denominator_premise"] = 99
    else:
        wire["product_identity"]["result"] = {"kind": "var", "args": "forged"}
    outcome = cas.replay_guarded_trace(json.dumps(wire), numerator, x, expected, nonzero=context)
    assert outcome.status in {"rejected", "unsupported"}, outcome.detail
    assert outcome.trace is None


def test_wide_zero_domain_and_resource_controls():
    x, numerator, _, _ = fixture()
    for zero in [cas.Expr.int(0), x - x]:
        outcome = cas.cancel_trace(zero, zero, nonzero=[zero], wide=True)
        assert outcome.status == "rejected" and outcome.trace is None
    assert cas.cancel_trace(numerator, x, nonzero=[], wide=True).status == "rejected"
    assert cas.cancel_trace(numerator, x, nonzero=[x], wide=True, max_work=0).status == "resource_limited"


def test_wide_bytes_replay_in_another_process_without_the_producer():
    _, _, _, trace = fixture()
    script = '''
import sys
from axeyum import cas
x = cas.Expr.var("x")
expected = cas.Expr.rat(2**200, 3)
def forbidden(*args, **kwargs):
    raise AssertionError("replay called producer")
cas.cancel_trace = forbidden
result = cas.replay_guarded_trace(sys.stdin.read(), x * expected, x, expected, nonzero=[x])
assert result.status == "checked", result.detail
assert result.trace.result.eval({}) == expected.eval({})
print("wide-guarded-replayed")
'''
    result = subprocess.run([sys.executable, "-c", script], input=trace.to_json(), text=True,
                            capture_output=True, env=os.environ.copy(), timeout=30)
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "wide-guarded-replayed"
