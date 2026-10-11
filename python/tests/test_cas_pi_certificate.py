"""Pi evidence byte transport must verify the original distinguished source."""
import json
import os
import subprocess
import sys
from fractions import Fraction

import pytest
from axeyum import BudgetExceeded, cas


def test_pi_bounds_replay_and_round_trip():
    certificate = cas.enclose_pi(256)
    assert isinstance(certificate.lower, Fraction)
    assert 3 < certificate.lower <= certificate.upper < Fraction(22, 7)
    assert certificate.upper - certificate.lower <= Fraction(1, 1 << 256)
    parsed = cas.PiEnclosure.from_json(certificate.to_json())
    assert parsed.to_json() == certificate.to_json()
    report = parsed.check(cas.Expr.pi())
    assert report.accepted and report.examined == report.discharged == 1
    assert report.reason is None
    assert not parsed.check(cas.Expr.var("pi")).accepted


def test_carried_source_and_each_numerical_distinction_reject():
    original = json.loads(cas.enclose_pi(16).to_json())
    for field, value in [("source_expression", cas.Expr.var("pi").to_json()),
                         ("order", 0), ("precision", 32),
                         ("remainder", {"numerator": "0", "denominator": "1"})]:
        wire = {**original, field: value}
        report = cas.PiEnclosure.from_json(json.dumps(wire)).check(cas.Expr.pi())
        assert not report.accepted and report.discharged == 0 and report.reason
    for field in ("lower", "upper"):
        wire = {**original, field: {"numerator": "4", "denominator": "1"}}
        try:
            certificate = cas.PiEnclosure.from_json(json.dumps(wire))
        except ValueError:
            continue
        assert not certificate.check(cas.Expr.pi()).accepted


def test_limits_and_malformed_wire_are_distinct():
    with pytest.raises(BudgetExceeded):
        cas.enclose_pi(257)
    with pytest.raises(BudgetExceeded):
        cas.PiEnclosure.from_json(" " * 65537)
    original = cas.enclose_pi(16).to_json()
    with pytest.raises(ValueError):
        cas.PiEnclosure.from_json(original.replace('"version":1', '"version":1,"version":1'))
    wire = json.loads(original)
    wire["lower"] = {"numerator": "2", "denominator": "4"}
    with pytest.raises(ValueError):
        cas.PiEnclosure.from_json(json.dumps(wire))


def test_export_replays_in_a_separate_process():
    script = """import sys
from axeyum import cas
c = cas.PiEnclosure.from_json(sys.stdin.read())
r = c.check(cas.Expr.pi())
assert r.accepted and r.discharged == 1
assert not c.check(cas.Expr.var('pi')).accepted
print('PI_REPLAY|examined=1|discharged=1')
"""
    process = subprocess.run([sys.executable, "-c", script], input=cas.enclose_pi(16).to_json(),
                             text=True, capture_output=True, timeout=15, env=os.environ.copy())
    assert process.returncode == 0, process.stderr
    assert "PI_REPLAY|examined=1|discharged=1" in process.stdout
