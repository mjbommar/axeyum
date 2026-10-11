"""Public proof regressions for the user-reported Boolean and negative-real gaps."""
import pytest
from axeyum import smt


@pytest.mark.parametrize("body", [
    "(declare-const p Bool) (assert p) (assert (not p))",
    "(declare-const p Bool) (declare-const x Int) (assert (or p (>= x 1))) (assert (not p)) (assert (<= x 0))",
    "(declare-const p Bool) (declare-const x Int) (assert (or p (= (* 2 x) 1))) (assert (not p))",
    "(declare-const p Bool) (declare-const q Bool) (assert (=> p q)) (assert p) (assert (not q))",
    "(declare-const x Real) (assert (> x 0.0)) (assert (> (* (- 1.0) x) 0.0))",
    "(declare-const x Real) (assert (> x 0.0)) (assert (> (* (- (- (- 1.0))) x) 0.0))",
])
def test_reported_unsat_routes_require_proof_text(body):
    query = body + " (check-sat)"
    assert smt.solve(query, timeout_ms=1500).status == "unsat"
    proof = smt.get_proof(query, timeout_ms=1500)
    assert isinstance(proof, str)
    assert "(cl)" in proof
    assert ":rule hole" not in proof
    assert smt.get_proof(query, timeout_ms=1500) == proof


def test_positive_coefficient_control_has_a_model_and_no_refutation():
    query = "(declare-const x Real) (assert (> x 0.0)) (assert (> (* 1.0 x) 0.0)) (check-sat)"
    outcome = smt.solve(query, timeout_ms=1500)
    assert outcome.status == "sat"
    assert outcome.replay() is True
    assert smt.get_proof(query, timeout_ms=1500) is None
