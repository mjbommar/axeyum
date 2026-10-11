"""Measure small trace workloads; run against an explicitly selected native build."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from statistics import median
from time import perf_counter_ns

from axeyum import _native, cas


def measure():
    x, y = cas.Expr.var("x"), cas.Expr.var("y")
    workloads = {
        "rational_polynomial": (x + cas.Expr.rat(1, 2) + cas.Expr.rat(1, 3)) * (x + 1),
        "power_expansion": ((x + 1) * (x - 1)) ** 3,
        "two_variables": (x + y + 1) * (x - y + 2),
    }
    rows = []
    for name, source in workloads.items():
        ordinary = cas.normalize(source)
        assert ordinary is not None, name
        produced = cas.normalize_trace(source)
        assert produced.status == "produced" and produced.trace is not None, name
        trace = produced.trace
        assert trace.step_count > 0, name
        assert cas.normalize(trace.result) == ordinary, name
        encoded = trace.to_json()
        assert cas.replay_trace(encoded, source, trace.result).status == "checked", name
        samples = {"ordinary_ns": [], "trace_ns": []}
        for _ in range(5):
            start = perf_counter_ns()
            for _ in range(10):
                assert cas.normalize(source) == ordinary, name
            samples["ordinary_ns"].append((perf_counter_ns() - start) / 10)
            start = perf_counter_ns()
            for _ in range(10):
                outcome = cas.normalize_trace(source)
                assert outcome.status == "produced" and outcome.trace is not None, name
            samples["trace_ns"].append((perf_counter_ns() - start) / 10)
        rows.append({"name": name, "steps": trace.step_count,
                     "json_bytes": len(encoded.encode("utf-8")),
                     "median_ns_per_call": {key: median(values) for key, values in samples.items()},
                     "samples_ns_per_call": samples})
    native = Path(_native.__file__).resolve()
    return {"schema": "cas-small-trace-cost-v1", "native_path": str(native),
            "native_sha256": hashlib.sha256(native.read_bytes()).hexdigest(),
            "trials": 5, "calls_per_trial": 10,
            "scope": "small narrow polynomial normalization; host-sensitive diagnostics",
            "rows": rows}


if __name__ == "__main__":
    print(json.dumps(measure(), indent=2, sort_keys=True))
