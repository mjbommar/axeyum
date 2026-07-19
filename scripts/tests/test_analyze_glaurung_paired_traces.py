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
    four_cell: bool = False,
    six_cell: bool = False,
    work_bounded: bool = False,
    bitwuzla_outcomes: tuple[str, ...] | None = None,
    bitwuzla_execution: str = "warm-retained",
) -> pathlib.Path:
    if four_cell and six_cell:
        raise ValueError("fixture cannot be both four-cell and six-cell")
    if work_bounded and not six_cell:
        raise ValueError("work-bounded fixture must be six-cell")
    if bitwuzla_outcomes is None:
        bitwuzla_outcomes = z3_outcomes
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
        event = {
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
        if four_cell or six_cell:
            event.update(
                {
                    "z3_cold_nanos": z3_scale * (index + 1) * 100,
                    "z3_warm_nanos": (index + 1) * 100,
                    "axeyum_cold_nanos": 3 * (index + 1) * 100,
                    "axeyum_warm_nanos": axeyum_scale * (index + 1) * 100,
                    "z3_cold_outcome": z3_outcome,
                    "z3_warm_outcome": z3_outcome,
                    "axeyum_cold_outcome": axeyum_outcome,
                    "axeyum_warm_outcome": axeyum_outcome,
                    "z3_warm_execution": "warm-retained",
                    "axeyum_warm_execution": execution,
                }
            )
        if six_cell:
            bitwuzla_outcome = bitwuzla_outcomes[index]
            event.update(
                {
                    "bitwuzla_cold_nanos": 4 * (index + 1) * 100,
                    "bitwuzla_warm_nanos": 2 * (index + 1) * 100,
                    "bitwuzla_cold_outcome": bitwuzla_outcome,
                    "bitwuzla_warm_outcome": bitwuzla_outcome,
                    "bitwuzla_warm_execution": bitwuzla_execution,
                }
            )
        if work_bounded:
            event["resource_counters"] = {
                cell: {
                    "unit": unit,
                    "limit": limit,
                    "stop_reason": (
                        "resource-limit"
                        if event[f"{cell}_outcome"] == "unknown"
                        else None
                    ),
                }
                for cell, unit, limit in (
                    ("z3_cold", "z3-rlimit", 2),
                    ("z3_warm", "z3-rlimit", 2),
                    ("axeyum_cold", "axeyum-progress-checks", 3),
                    ("axeyum_warm", "axeyum-progress-checks", 3),
                    ("bitwuzla_cold", "bitwuzla-termination-polls", 5),
                    ("bitwuzla_warm", "bitwuzla-termination-polls", 5),
                )
            }
        events.append(event)
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
        "check_measurement_schema": (
            "glaurung-ordered-check-measurement-v4"
            if work_bounded
            else (
                "glaurung-ordered-check-measurement-v3"
                if six_cell
                else (
                    "glaurung-ordered-check-measurement-v2"
                    if four_cell
                    else "glaurung-ordered-check-measurement-v1"
                )
            )
        ),
        "source": {"revision": "a" * 40, "dirty": False},
        "driver": {"path": "fixture.sys", "sha256": "d" * 64},
        "analysis_command": ["ioctlance", "fixture.sys"],
        "analysis_configuration": {
            "GLAURUNG_ORDERED_TRACE_DIR": str(trace),
            "GLAURUNG_SHADOW_DIFF": "1",
        },
        "solver_features": (
            ["symbolic", "solver-z3", "solver-axeyum", "solver-bitwuzla"]
            if six_cell
            else ["solver-z3", "solver-axeyum"]
        ),
        "trusted_oracle": {"backend": "z3"},
        "neutral_measurement_backend": (
            {
                "backend": "bitwuzla",
                "runtime_version": "0.9.1",
                "authoritative_in_shadow_mode": False,
                "role": "benchmark-only-neutral",
            }
            if six_cell
            else None
        ),
        "toolchain": "rustc fixture",
        "host_identity": {"hostname": "fixture"},
        "worker_count": 1,
        "event_count": len(events),
        "events_sha256": hashlib.sha256(events_bytes).hexdigest(),
        "query_count": len(query_entries),
        "query_index_sha256": hashlib.sha256(query_index_bytes).hexdigest(),
    }
    if work_bounded:
        manifest["solver_work_budgets"] = {
            "z3": {"unit": "z3-rlimit", "limit": 2},
            "axeyum": {"unit": "axeyum-progress-checks", "limit": 3},
            "bitwuzla": {"unit": "bitwuzla-termination-polls", "limit": 5},
            "cross_backend_unit_equivalence": False,
            "wall_safety_cap_ms": 60_000,
        }
    (trace / "trace-manifest-v1.json").write_text(json.dumps(manifest))
    return trace


class PairedTraceAnalysisTests(unittest.TestCase):
    def test_accepts_work_bounded_v4_with_named_units_and_stop_reasons(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, six_cell=True, work_bounded=True)
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=100, seed=7)

        self.assertEqual(
            report["configuration_identity"]["solver_work_budgets"]["z3"],
            {"unit": "z3-rlimit", "limit": 2},
        )
        self.assertEqual(report["stable_all_six_decided_occurrences"], 2)

    def test_rejects_v4_cross_backend_unit_equivalence_claim(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, six_cell=True, work_bounded=True)
                for repetition in range(5)
            ]
            manifest_path = traces[-1] / "trace-manifest-v1.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["solver_work_budgets"]["cross_backend_unit_equivalence"] = True
            manifest_path.write_text(json.dumps(manifest))

            with self.assertRaisesRegex(paired.AnalysisError, "unit.*equivalence"):
                paired.analyze(traces, bootstrap_samples=100, seed=7)

    def test_rejects_v4_unknown_without_a_typed_stop_reason(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, six_cell=True, work_bounded=True)
                for repetition in range(5)
            ]
            events_path = traces[-1] / "events-v1.ndjson"
            events = [json.loads(line) for line in events_path.read_text().splitlines()]
            events[-1]["resource_counters"]["z3_cold"]["stop_reason"] = None
            events_bytes = b"".join(
                (json.dumps(event, sort_keys=True) + "\n").encode() for event in events
            )
            events_path.write_bytes(events_bytes)
            manifest_path = traces[-1] / "trace-manifest-v1.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["events_sha256"] = hashlib.sha256(events_bytes).hexdigest()
            manifest_path.write_text(json.dumps(manifest))

            with self.assertRaisesRegex(paired.AnalysisError, "outcome/stop-reason"):
                paired.analyze(traces, bootstrap_samples=100, seed=7)

    def test_reports_six_cell_neutral_contrasts_and_acceptance_gate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, six_cell=True)
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=100, seed=7)
        comparisons = report["six_cell_comparisons"]
        self.assertEqual(len(comparisons), 9)
        self.assertAlmostEqual(
            comparisons["cold_z3_over_bitwuzla"][
                "per_occurrence_geomean_speedup"
            ],
            0.5,
        )
        self.assertAlmostEqual(
            comparisons["warm_axeyum_over_bitwuzla"][
                "per_occurrence_geomean_speedup"
            ],
            0.5,
        )
        self.assertAlmostEqual(
            comparisons["bitwuzla_cold_over_warm"][
                "per_occurrence_geomean_speedup"
            ],
            2.0,
        )
        self.assertEqual(report["stable_all_six_decided_occurrences"], 2)
        self.assertEqual(
            report["six_cell_outcome_counts_per_repetition"][0],
            {"all_six_decided": 2, "any_nondecision": 1},
        )
        self.assertEqual(
            report["configuration_identity"]["neutral_measurement_backend"]
            ["backend"],
            "bitwuzla",
        )
        self.assertEqual(
            report["neutral_regime_gate"], {"accepted": False, "reasons": [
                "not_all_occurrences_six_way_decided"
            ]}
        )

    def test_rejects_invalid_v3_neutral_backend_identity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, six_cell=True)
                for repetition in range(5)
            ]
            manifest_path = traces[-1] / "trace-manifest-v1.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["neutral_measurement_backend"]["runtime_version"] = "0.8.0"
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(paired.AnalysisError, "neutral.*identity"):
                paired.analyze(traces, bootstrap_samples=100, seed=7)

    def test_six_cell_fallback_marks_neutral_gate_inconclusive(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(
                    root,
                    repetition,
                    six_cell=True,
                    z3_outcomes=("sat", "unsat"),
                    axeyum_outcomes=("sat", "unsat"),
                    bitwuzla_execution="fallback-missing-delta",
                )
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=100, seed=7)
        self.assertFalse(report["neutral_regime_gate"]["accepted"])
        self.assertIn(
            "non_pure_warm_execution:bitwuzla",
            report["neutral_regime_gate"]["reasons"],
        )

    def test_accepts_complete_stable_six_cell_fixture(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(
                    root,
                    repetition,
                    six_cell=True,
                    z3_outcomes=("sat", "unsat"),
                    axeyum_outcomes=("sat", "unsat"),
                )
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=100, seed=7)
        self.assertEqual(
            report["neutral_regime_gate"], {"accepted": True, "reasons": []}
        )
        self.assertEqual(report["stable_all_six_decided_occurrences"], 2)
        self.assertEqual(
            report["warm_execution_counts_per_repetition"][0],
            {
                "z3": {"warm-retained": 2},
                "axeyum": {"warm-retained": 2},
                "bitwuzla": {"warm-retained": 2},
            },
        )

    def test_rejects_six_cell_decided_disagreement(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(
                    root,
                    repetition,
                    six_cell=True,
                    bitwuzla_outcomes=("unsat", "unsat", "unknown"),
                )
                for repetition in range(5)
            ]
            with self.assertRaisesRegex(paired.AnalysisError, "fair-cell disagreement"):
                paired.analyze(traces, bootstrap_samples=100, seed=7)

    def test_rejects_six_cell_operational_result(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(
                    root,
                    repetition,
                    six_cell=True,
                    bitwuzla_outcomes=("sat", "unsat", "error"),
                )
                for repetition in range(5)
            ]
            with self.assertRaisesRegex(paired.AnalysisError, "operational bitwuzla"):
                paired.analyze(traces, bootstrap_samples=100, seed=7)

    def test_rejects_decided_outcome_drift_across_repetitions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, four_cell=True)
                for repetition in range(4)
            ]
            traces.append(
                write_trace(
                    root,
                    4,
                    z3_outcomes=("unsat", "unsat", "sat"),
                    axeyum_outcomes=("unsat", "unsat", "sat"),
                    four_cell=True,
                )
            )
            with self.assertRaisesRegex(paired.AnalysisError, "decided outcome drift"):
                paired.analyze(traces, bootstrap_samples=100, seed=7)

    def test_reports_four_cell_cold_warm_contrasts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, four_cell=True)
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=100, seed=7)
        comparisons = report["four_cell_comparisons"]
        self.assertAlmostEqual(
            comparisons["cold_z3_over_axeyum"]["per_occurrence_geomean_speedup"],
            2.0 / 3.0,
        )
        self.assertAlmostEqual(
            comparisons["warm_z3_over_axeyum"]["per_occurrence_geomean_speedup"],
            1.0,
        )
        self.assertAlmostEqual(
            comparisons["z3_cold_over_warm"]["per_occurrence_geomean_speedup"],
            2.0,
        )
        self.assertAlmostEqual(
            comparisons["axeyum_cold_over_warm"]["per_occurrence_geomean_speedup"],
            3.0,
        )

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

    @unittest.skipUnless(
        importlib.util.find_spec("matplotlib") is not None,
        "matplotlib is optional",
    )
    def test_writes_four_cell_csv_and_png_cdf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(root, repetition, four_cell=True)
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=10, seed=7)
            output = root / "cdf"
            paired.write_cdf(report, output)
            csv_path = output / "fixture.sys-four-cell-latency-cdf.csv"
            png_path = output / "fixture.sys-four-cell-latency-cdf.png"
            self.assertIn(b"z3_cold", csv_path.read_bytes())
            self.assertIn(b"axeyum_warm", csv_path.read_bytes())
            self.assertGreater(png_path.stat().st_size, 0)

    @unittest.skipUnless(
        importlib.util.find_spec("matplotlib") is not None,
        "matplotlib is optional",
    )
    def test_writes_six_cell_csv_and_png_cdf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            traces = [
                write_trace(
                    root,
                    repetition,
                    six_cell=True,
                    z3_outcomes=("sat", "unsat"),
                    axeyum_outcomes=("sat", "unsat"),
                )
                for repetition in range(5)
            ]
            report = paired.analyze(traces, bootstrap_samples=10, seed=7)
            output = root / "cdf"
            paired.write_cdf(report, output)
            csv_path = output / "fixture.sys-six-cell-latency-cdf.csv"
            png_path = output / "fixture.sys-six-cell-latency-cdf.png"
            self.assertIn(b"z3_cold", csv_path.read_bytes())
            self.assertIn(b"bitwuzla_warm", csv_path.read_bytes())
            self.assertGreater(png_path.stat().st_size, 0)


if __name__ == "__main__":
    unittest.main()
