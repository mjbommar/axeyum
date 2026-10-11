"""Per-step proof logs, source binding, and honest production/checking outcomes."""
import json
import pytest
from axeyum import cas


def expression():
    x = cas.Expr.var("x")
    return (x + 1 + 2) * (-(-(x + 1)))


def test_trace_has_per_step_witnesses_and_deterministic_export():
    source = expression()
    produced = cas.normalize_trace(source)
    assert produced.status == "produced"
    assert produced.detail == ""
    trace = produced.trace
    assert trace is not None
    assert trace.step_count >= 3
    data = json.loads(trace.to_json())
    assert len(data["steps"]) == trace.step_count
    for index, step in enumerate(data["steps"]):
        assert step["id"] == index
        assert step["witness"] is not None
        assert step["context"] == "empty-v1"
        assert step["side_conditions"] == []
    assert cas.normalize_trace(source).trace.to_json() == trace.to_json()
    checked = cas.replay_trace(trace.to_json(), source, trace.result)
    assert checked.status == "checked"
    assert checked.trace is not None
    assert trace.replay(source, trace.result).status == "checked"
    assert cas.replay_trace(trace.to_json(), cas.Expr.var("different"), trace.result).status == "rejected"


@pytest.mark.parametrize("corruption", ["context", "witness", "malformed_witness", "missing", "truncate"])
def test_trace_rejects_corrupted_export_with_a_concrete_reason(corruption):
    source = expression()
    trace = cas.normalize_trace(source).trace
    data = json.loads(trace.to_json())
    if corruption == "context":
        data["steps"][0]["context"] = "unproved_assumption"
    elif corruption == "witness":
        data["steps"][0]["witness"] = {"kind": "const", "args": {"numerator": "99", "denominator": "1"}}
    elif corruption == "malformed_witness":
        data["steps"][0]["witness"] = {"kind": "const", "args": {"numerator": "not_a_number", "denominator": "1"}}
    elif corruption == "missing":
        del data["steps"][0]["witness"]
    else:
        data["steps"].pop()
    checked = cas.replay_trace(json.dumps(data), source, trace.result)
    assert checked.status == "rejected"
    assert checked.trace is None
    assert checked.detail
    if corruption in ("context", "witness", "malformed_witness"):
        assert checked.failing_step == 0


def test_unsupported_cancellation_and_resource_exhaustion_are_distinct():
    x = cas.Expr.var("x")
    declined = cas.normalize_trace((x * x) / x)
    assert declined.status == "unsupported"
    assert declined.trace is None
    for options in ({"max_work": 0}, {"max_steps": 0}, {"max_steps": 999999}):
        exhausted = cas.normalize_trace(expression(), **options)
        assert exhausted.status == "resource_limited"
        assert exhausted.trace is None
    trace = cas.normalize_trace(expression()).trace
    assert cas.replay_trace(trace.to_json(), expression(), trace.result, max_work=0).status == "resource_limited"
