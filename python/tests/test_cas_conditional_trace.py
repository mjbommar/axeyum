"""Nested conditional rewrites bind the whole expression and external context."""
import json
import subprocess
import sys

import pytest
from axeyum import cas


def fixture():
    x = cas.Expr.var("x")
    quotient = (x * x) / x
    source = quotient + (-quotient)
    outcome = cas.cancel_nested_trace(source, nonzero=[x])
    assert outcome.status == "produced" and outcome.json is not None
    assert outcome.result is not None and outcome.step_count == 2
    return x, source, outcome


def test_nested_conditional_source_and_serialized_replay():
    x, source, produced = fixture()
    replay = cas.replay_conditional_trace(produced.json, source, produced.result, nonzero=[x])
    assert replay.status == "checked" and replay.step_count == 2
    assert replay.json == produced.json
    assert cas.cancel_nested_trace(source, nonzero=[x]).json == produced.json
    missing = cas.replay_conditional_trace(produced.json, source, produced.result, nonzero=[])
    assert missing.status == "rejected" and missing.json is None and missing.result is None


@pytest.mark.parametrize("mutation", ["path", "order", "delete", "surrounding", "premise", "version"])
def test_corrupted_nested_steps_reject(mutation):
    x, source, produced = fixture()
    data = json.loads(produced.json)
    if mutation == "path":
        data["steps"][0]["location"] = [1]
    elif mutation == "order":
        data["steps"].reverse()
    elif mutation == "delete":
        data["steps"].pop()
    elif mutation == "surrounding":
        data["steps"][0]["after"] = {"kind": "var", "args": "forged"}
    elif mutation == "premise":
        data["steps"][0]["witness"]["denominator_premise"] = 999
    else:
        data["version"] = "unknown"
    outcome = cas.replay_conditional_trace(json.dumps(data), source, produced.result, nonzero=[x])
    assert outcome.status in {"rejected", "unsupported"}
    assert outcome.json is None and outcome.result is None


def test_limits_zero_and_source_substitution_are_explicit():
    x, source, produced = fixture()
    for limits in ({"max_steps": 1}, {"max_work": 1}):
        checked = cas.replay_conditional_trace(produced.json, source, produced.result, nonzero=[x], **limits)
        assert checked.status == "resource_limited" and checked.json is None
    zero = cas.Expr.int(0)
    declined = cas.cancel_nested_trace(zero / zero, nonzero=[zero])
    assert declined.status == "rejected" and declined.json is None
    changed = cas.replay_conditional_trace(produced.json, x, produced.result, nonzero=[x])
    assert changed.status == "rejected" and changed.json is None


def test_child_replays_nested_bytes_with_production_disabled(tmp_path):
    _, _, produced = fixture()
    path = tmp_path / "conditional.json"
    path.write_text(produced.json)
    code = '''from pathlib import Path
import sys
from axeyum import cas
x=cas.Expr.var("x")
q=(x*x)/x
source=q+(-q)
def forbidden(*args, **kwargs):
    raise AssertionError("replay invoked production")
cas.cancel_nested_trace=forbidden
checked=cas.replay_conditional_trace(Path(sys.argv[1]).read_text(),source,x+(-x),nonzero=[x])
assert checked.status=="checked" and checked.step_count==2
print("NESTED_CONDITIONAL_REPLAY_OK")
'''
    checked = subprocess.run([sys.executable, "-c", code, str(path)], capture_output=True, text=True, timeout=30)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert "NESTED_CONDITIONAL_REPLAY_OK" in checked.stdout


def test_wide_surrounding_coefficient_survives_nested_replay():
    """Conditional transport must preserve the wide CAS surface end to end."""
    x = cas.Expr.var("x")
    numerator, denominator = 2**200 + 17, 2**181 + 3
    coefficient = cas.Expr.rat(numerator, denominator)
    source = coefficient * ((x * x) / x)
    expected = coefficient * x
    produced = cas.cancel_nested_trace(source, nonzero=[x])
    assert produced.status == "produced" and produced.step_count == 1
    assert produced.result is not None and produced.json is not None
    checked = cas.replay_conditional_trace(produced.json, source, expected, nonzero=[x])
    assert checked.status == "checked" and checked.step_count == 1
    assert checked.json == produced.json
    changed = cas.Expr.rat(numerator + 1, denominator) * x
    rejected = cas.replay_conditional_trace(produced.json, source, changed, nonzero=[x])
    assert rejected.status == "rejected"
    assert rejected.json is None and rejected.result is None
