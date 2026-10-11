"""Portable OMT checks bind evidence to the original query without search."""
import json
import os
import subprocess
import sys

import pytest
from axeyum import AxeyumError, smt

SOURCE = """(declare-const x Int)(declare-const y Int)
(assert (and (>= x 0) (<= x 10) (>= y 0) (<= y 3) (<= (+ x y) 10)))
(maximize x)(maximize y)(check-sat)"""


@pytest.mark.parametrize("mode,count", [("box", 2), ("lex", 4)])
def test_export_replays_nonzero_obligations(mode, count):
    certificate = smt.optimize(SOURCE, mode=mode)[1].certificate_json()
    report = smt.check_optimization_certificate(certificate, SOURCE)
    assert report.accepted and report.reason is None
    assert report.examined == report.discharged == count
    with pytest.raises(AttributeError):
        report.accepted = False
    mismatch = smt.check_optimization_certificate(certificate, SOURCE + " ")
    assert not mismatch.accepted and mismatch.examined == mismatch.discharged == 0


def test_changed_subject_and_witness_do_not_receive_gold():
    certificate = smt.optimize(SOURCE)[1].certificate_json()
    data = json.loads(certificate)
    data["source"] = SOURCE.replace("(<= x 10)", "(<= x 11)")
    assert not smt.check_optimization_certificate(json.dumps(data), data["source"]).accepted
    data = json.loads(certificate)
    data["rows"][0]["value"] = "9"
    assert not smt.check_optimization_certificate(json.dumps(data), SOURCE).accepted
    data = json.loads(certificate)
    data["rows"].pop(0)
    assert not smt.check_optimization_certificate(json.dumps(data), SOURCE).accepted


def test_strict_input_and_missing_evidence_decline():
    certificate = smt.optimize(SOURCE)[0].certificate_json()
    data = json.loads(certificate)
    data["accepted"] = True
    with pytest.raises(AxeyumError):
        smt.check_optimization_certificate(json.dumps(data), SOURCE)
    with pytest.raises(AxeyumError):
        smt.check_optimization_certificate(" " * 262145, SOURCE)
    row = smt.optimize("(declare-const x Int)(assert (<= (* 2 x) 1))(maximize x)(check-sat)")[0]
    assert row.value == 0 and not row.gold_eligible
    with pytest.raises(AxeyumError):
        row.certificate_json()


def test_replay_in_a_separate_process_without_optimizer(tmp_path):
    path = tmp_path / "certificate.json"
    path.write_text(smt.optimize(SOURCE)[1].certificate_json())
    subject = tmp_path / "subject.smt2"
    subject.write_text(SOURCE)
    code = """from pathlib import Path
import sys
from axeyum import smt
def forbidden(*args, **kwargs):
    raise AssertionError('optimization must not run during replay')
smt.optimize = forbidden
report = smt.check_optimization_certificate(Path(sys.argv[1]).read_text(), Path(sys.argv[2]).read_text())
assert report.accepted and report.examined == report.discharged == 4
print('checked 4 obligations')
"""
    result = subprocess.run([sys.executable, "-c", code, str(path), str(subject)],
                            env=os.environ.copy(), capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "checked 4 obligations"


def test_portable_replay_timeout_is_explicitly_inconclusive():
    certificate = smt.optimize(SOURCE)[1].certificate_json()
    limited = smt.check_optimization_certificate(certificate, SOURCE, timeout_ms=0)
    assert not limited.accepted and limited.resource_limited
    assert limited.examined == limited.discharged == 0 and limited.reason
    checked = smt.check_optimization_certificate(certificate, SOURCE, timeout_ms=2000)
    assert checked.accepted and not checked.resource_limited
    assert checked.examined == checked.discharged == 4
