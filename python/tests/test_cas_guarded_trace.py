"""Quotient evidence is conditional on explicit caller-bound nonzero facts."""
import json
import os
import subprocess
import sys

import pytest
from axeyum import cas


def fixture():
    x = cas.Expr.var("x")
    numerator = x * x
    produced = cas.cancel_trace(numerator, x, nonzero=[x])
    assert produced.status == "produced" and produced.trace is not None
    return x, numerator, produced.trace


def test_conditional_cancellation_has_replayable_polynomial_premises():
    x, numerator, trace = fixture()
    assert str(trace.result) == str(x)
    assert [str(p) for p in trace.nonzero_assumptions] == ["x"]
    assert trace.step_count >= 3
    data = json.loads(trace.to_json())
    assert data["version"] == "cas-guarded-quotient-v1"
    assert data["denominator_premise"] == 0
    assert data["numerator_identity"]["steps"]
    assert data["product_identity"]["steps"]
    checked = cas.replay_guarded_trace(trace.to_json(), numerator, x, trace.result, nonzero=[x])
    assert checked.status == "checked" and checked.trace is not None
    assert cas.cancel_trace(numerator, x, nonzero=[x]).trace.to_json() == trace.to_json()
    # The unconditional API still refuses to turn a domain restriction into an identity.
    assert cas.normalize_trace(numerator / x).status == "unsupported"


@pytest.mark.parametrize("change", ["missing", "different", "additional", "result", "numerator", "denominator"])
def test_external_subject_result_and_context_are_bound(change):
    x, numerator, trace = fixture()
    y = cas.Expr.var("y")
    context, denominator, result = [x], x, trace.result
    if change == "missing":
        context = []
    elif change == "different":
        context = [y]
    elif change == "additional":
        context = [x, y]
    elif change == "result":
        result = y
    elif change == "numerator":
        numerator = x * y
    else:
        denominator = y
    outcome = cas.replay_guarded_trace(trace.to_json(), numerator, denominator, result, nonzero=context)
    assert outcome.status == "rejected" and outcome.trace is None and outcome.detail


def test_zero_denominator_missing_assumption_and_work_limits_decline():
    x = cas.Expr.var("x")
    for denominator in [cas.Expr.int(0), x - x]:
        outcome = cas.cancel_trace(denominator, denominator, nonzero=[denominator])
        assert outcome.status == "rejected" and outcome.trace is None
    assert cas.cancel_trace(x * x, x, nonzero=[]).status == "rejected"
    assert cas.cancel_trace(x * x, x, nonzero=[x], max_work=0).status == "resource_limited"
    assert cas.cancel_trace(x * x, x, nonzero=[x], max_steps=0).status == "resource_limited"


@pytest.mark.parametrize("change", ["premise", "witness", "unknown", "duplicate", "bytes"])
def test_changed_premise_and_malformed_transport_fail(change):
    x, numerator, trace = fixture()
    data = json.loads(trace.to_json())
    if change == "premise":
        data["denominator_premise"] = 999
    elif change == "witness":
        data["product_identity"]["steps"][0]["witness"] = {"kind": "var", "args": "forged"}
    elif change == "unknown":
        data["accepted"] = True
    text = json.dumps(data)
    if change == "duplicate":
        text = text.replace('"denominator_premise": 0', '"denominator_premise": 0, "denominator_premise": 0')
    elif change == "bytes":
        text = " " * 1048577
    outcome = cas.replay_guarded_trace(text, numerator, x, trace.result, nonzero=[x])
    assert outcome.status in {"rejected", "resource_limited"}
    assert outcome.trace is None


def test_separate_process_replay_never_runs_cancellation_search(tmp_path):
    _, _, trace = fixture()
    path = tmp_path / "guarded.json"
    path.write_text(trace.to_json())
    code = """from pathlib import Path
import sys
from axeyum import cas
x = cas.Expr.var('x')
def forbidden(*args, **kwargs):
    raise AssertionError('producer must not run during replay')
cas.cancel_trace = forbidden
checked = cas.replay_guarded_trace(Path(sys.argv[1]).read_text(), x*x, x, x, nonzero=[x])
assert checked.status == 'checked' and checked.trace.step_count >= 3
print('conditional equality checked')
"""
    result = subprocess.run([sys.executable, "-c", code, str(path)], env=os.environ.copy(),
                            capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "conditional equality checked"
