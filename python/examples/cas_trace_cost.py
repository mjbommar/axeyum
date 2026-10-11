"""Measure bounded CAS trace production/replay; print reproducible JSON results.

Use a fresh extension. Timings are local diagnostics, not solver parity results.
The wide workload compares exact evaluation with certified normalization because
ordinary polynomial normalization still has narrower coefficient limits.
"""
import hashlib
import json
import statistics
import time
from fractions import Fraction
from pathlib import Path

from axeyum import cas
import axeyum._native as native


def measure(operation, samples=7):
    operation()  # Warm once; correctness is checked by each operation below.
    values = []
    for _ in range(samples):
        start = time.perf_counter_ns()
        operation()
        values.append(time.perf_counter_ns() - start)
    return {"samples": samples, "median_ns": int(statistics.median(values)),
            "min_ns": min(values), "max_ns": max(values)}


def workload(name, expression, expected, wide):
    outcome = cas.normalize_trace(expression, wide=wide)
    assert outcome.status == "produced", outcome.detail
    trace = outcome.trace
    assert trace is not None
    encoded = trace.to_json()
    expected_expression = cas.Expr.rat(expected.numerator, expected.denominator)

    def evaluate():
        assert expression.eval({}) == expected

    def produce():
        result = cas.normalize_trace(expression, wide=wide)
        assert result.status == "produced", result.detail
        assert result.trace is not None
        assert result.trace.result.eval({}) == expected
        assert result.trace.to_json() == encoded

    def replay():
        result = cas.replay_trace(encoded, expression, expected_expression)
        assert result.status == "checked", result.detail

    wire = json.loads(encoded)
    return {"name": name, "wide": wide, "json_bytes": len(encoded.encode()),
            "steps": len(wire["steps"]), "exact_evaluation": measure(evaluate),
            "trace_production": measure(produce), "byte_replay": measure(replay)}


if __name__ == "__main__":
    small = (cas.Expr.rat(2, 3) + cas.Expr.rat(7, 5)) ** 4
    rate = Fraction(1, 240)
    payment = cas.Expr.int(300000) * rate / (1 - cas.Expr.rat(241, 240) ** -360)
    expected = 300000 * rate / (1 - (1 + rate) ** -360)
    path = Path(native.__file__).resolve()
    print(json.dumps({"native_path": str(path),
                      "native_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                      "workloads": [workload("closed-rational", small, Fraction(31, 15) ** 4, False),
                                    workload("amortization-360", payment, expected, True)]},
                     indent=2, sort_keys=True))
