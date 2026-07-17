#!/usr/bin/env python3

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "analyze-glaurung-paired-traces.py"
SPEC = importlib.util.spec_from_file_location("paired", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
paired = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = paired
SPEC.loader.exec_module(paired)


def write_trace(
    root: pathlib.Path,
    repetition: int,
    *,
    query_suffix: str = "0",
    execution: str = "warm-retained",
    z3_outcomes: tuple[str, ...] = ("sat", "unsat", "unknown"),
    axeyum_outcomes: tuple[str, ...] = ("sat", "unsat", "sat"),
    z3_scale: int = 2,
    axeyum_scale: int = 1,
) -> pathlib.Path:
    trace = root / f"trace-{repetition}"
    trace.mkdir()
    events = []
    query_entries = []
    queries = trace / "queries"
    queries.mkdir()
    for index, (z3_outcome, axeyum_outcome) in enumerate(
        zip(z3_outcomes, axeyum_outcomes)
    ):
        query_bytes = f"query-{index}-{query_suffix}\n".encode()
        query_sha256 = hashlib.sha256(query_bytes).hexdigest()
        query_path = f"queries/{query_sha256}.smt2"
        (trace / query_path).write_bytes(query_bytes)
        events.append(
            {
                "event_seq": index,
                "event": "check",
                "check_id": f"check-{index}",
                "path_id": "path-0",
                "query_sha256": query_sha256,
                "purpose": "fixture",
                "scope_digest": f"scope-{index}",
                "active_constraint_count": index + 1,
                "outcome": z3_outcome,
                "z3_nanos": z3_scale * (index + 1) * 100,
                "axeyum_nanos": axeyum_scale * (index + 1) * 100,
                "z3_outcome": z3_outcome,
                "axeyum_outcome": axeyum_outcome,
                "axeyum_execution": execution,
            }
        )
        query_entries.append(
            {
                "content_hash": query_sha256,
                "path": query_path,
                "outcomes": [z3_outcome],
                "occurrences": [
                    {
                        "event_seq": index,
                        "check_id": f"check-{index}",
                        "path_id": "path-0",
                    }
                ],
            }
        )
    events_bytes = b"".join(
        (json.dumps(event, sort_keys=True) + "\n").encode() for event in events
    )
    (trace / "events-v1.ndjson").write_bytes(events_bytes)
    query_index_bytes = (
        json.dumps({"version": 1, "queries": query_entries}, sort_keys=True) + "\n"
    ).encode()
    (trace / "query-index-v1.json").write_bytes(query_index_bytes)
    manifest = {
        "schema": "glaurung-ordered-trace-v1",
        "version": 1,
        "check_measurement_schema": "glaurung-ordered-check-measurement-v1",
        "source": {"revision": "a" * 40, "dirty": False},
        "driver": {"path": "fixture.sys", "sha256": "d" * 64},
        "analysis_command": ["ioctlance", "fixture.sys"],
        "analysis_configuration": {
            "GLAURUNG_ORDERED_TRACE_DIR": str(trace),
            "GLAURUNG_SHADOW_DIFF": "1",
        },
        "solver_features": ["solver-z3", "solver-axeyum"],
        "trusted_oracle": {"backend": "z3"},
        "toolchain": "rustc fixture",
        "host_identity": {"hostname": "fixture"},
        "worker_count": 1,
        "event_count": len(events),
        "events_sha256": hashlib.sha256(events_bytes).hexdigest(),
        "query_count": len(query_entries),
        "query_index_sha256": hashlib.sha256(query_index_bytes).hexdigest(),
    }
    (trace / "trace-manifest-v1.json").write_text(json.dumps(manifest))
    return trace


class PairedTraceAnalysisTests(unittest.TestCase):
    def test_reports_geomean_ci_buckets_and_warm_partition(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(5)]
            report = paired.analyze(traces, bootstrap_samples=100, seed=7)
        self.assertEqual(report["repetitions"], 5)
        self.assertEqual(report["stable_both_decided_occurrences"], 2)
        self.assertEqual(report["excluded_from_primary_for_any_nondecision"], 1)
        self.assertEqual(
            report["outcome_buckets_per_repetition"][0],
            {
                "both_decided": 2,
                "z3_only": 0,
                "axeyum_only": 1,
                "neither": 0,
            },
        )
        primary = report["primary_both_decided"]
        self.assertAlmostEqual(primary["per_occurrence_geomean_speedup"], 2.0)
        self.assertEqual(primary["bootstrap_95_percent_ci"], [2.0, 2.0])
        self.assertEqual(report["pure_warm_execution_rate"], 1.0)
        self.assertEqual(report["retained_warm_execution_rate"], 1.0)
        self.assertEqual(
            report["input_measurement_schema"],
            "glaurung-ordered-check-measurement-v1",
        )
        self.assertEqual(
            report["configuration_identity"]["analysis_configuration"],
            {"GLAURUNG_SHADOW_DIFF": "1"},
        )
        self.assertFalse(report["methodology"]["ratio_of_sums_reported"])

    def test_rejects_too_few_repetitions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(4)]
            with self.assertRaisesRegex(paired.AnalysisError, "at least 5"):
                paired.analyze(traces)

    def test_rejects_fixed_work_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(4)]
            traces.append(write_trace(root, 4, query_suffix="f"))
            with self.assertRaisesRegex(paired.AnalysisError, "fixed-work"):
                paired.analyze(traces)

    def test_rejects_execution_population_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(4)]
            traces.append(write_trace(root, 4, execution="fallback-path-cap"))
            with self.assertRaisesRegex(paired.AnalysisError, "fixed-work"):
                paired.analyze(traces)

    def test_rejects_operational_backend_results(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(4)]
            traces.append(
                write_trace(
                    root,
                    4,
                    axeyum_outcomes=("sat", "unsat", "error"),
                )
            )
            with self.assertRaisesRegex(paired.AnalysisError, "operational"):
                paired.analyze(traces)

    def test_rejects_query_content_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(5)]
            query = next((traces[-1] / "queries").iterdir())
            query.write_text("mutated query bytes\n")
            with self.assertRaisesRegex(paired.AnalysisError, "query content SHA-256"):
                paired.analyze(traces)

    @unittest.skipUnless(
        importlib.util.find_spec("matplotlib") is not None,
        "matplotlib is optional",
    )
    def test_writes_csv_and_png_cdf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [write_trace(root, repetition) for repetition in range(5)]
            report = paired.analyze(traces, bootstrap_samples=10, seed=7)
            output = root / "cdf"
            paired.write_cdf(report, output)
            csv_bytes = (output / "fixture.sys-latency-cdf.csv").read_bytes()
            self.assertGreater(len(csv_bytes), 0)
            self.assertNotIn(b"\r\n", csv_bytes)
            self.assertGreater((output / "fixture.sys-latency-cdf.png").stat().st_size, 0)


if __name__ == "__main__":
    unittest.main()
