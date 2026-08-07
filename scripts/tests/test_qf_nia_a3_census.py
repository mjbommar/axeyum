#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import pathlib

import pytest


SCRIPT = pathlib.Path(__file__).parents[1] / "qf_nia_a3_census.py"
SPEC = importlib.util.spec_from_file_location("qf_nia_a3_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CENSUS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CENSUS)


def fixture(tmp_path: pathlib.Path) -> tuple[pathlib.Path, pathlib.Path]:
    first = tmp_path / "first.smt2"
    second = tmp_path / "second.smt2"
    first.write_text("(set-logic QF_NIA)\n", encoding="utf-8")
    second.write_text("(set-logic QF_NIA)\n", encoding="utf-8")
    population = tmp_path / "population.txt"
    population.write_text(f"{first}\n{second}\n", encoding="utf-8")
    sidecar = tmp_path / "sidecar.tsv"
    sidecar.write_text(
        "file\taxeyum\treference\tdeclared\n"
        "first.smt2\tunsolved\tunsat\tunsat\n"
        "second.smt2\tsat\tsat\tsat\n",
        encoding="utf-8",
    )
    return population, sidecar


def test_extract_binds_unique_basenames_in_population_order(tmp_path: pathlib.Path) -> None:
    population, sidecar = fixture(tmp_path)
    residual, summary = CENSUS.extract(
        population,
        sidecar,
        expected_population_sha256=CENSUS.sha256_file(population),
        expected_sidecar_sha256=CENSUS.sha256_file(sidecar),
        expected_rows=2,
        expected_reference_only=1,
    )
    assert residual == [str(tmp_path / "first.smt2")]
    assert summary["status_counts"] == {"sat/sat": 1, "unsolved/unsat": 1}


def test_extract_rejects_digest_or_count_drift(tmp_path: pathlib.Path) -> None:
    population, sidecar = fixture(tmp_path)
    with pytest.raises(CENSUS.CensusError, match="population SHA-256 differs"):
        CENSUS.extract(
            population,
            sidecar,
            expected_population_sha256="0" * 64,
            expected_sidecar_sha256=CENSUS.sha256_file(sidecar),
            expected_rows=2,
            expected_reference_only=1,
        )
    with pytest.raises(CENSUS.CensusError, match="expected 2 reference-only rows"):
        CENSUS.extract(
            population,
            sidecar,
            expected_population_sha256=CENSUS.sha256_file(population),
            expected_sidecar_sha256=CENSUS.sha256_file(sidecar),
            expected_rows=2,
            expected_reference_only=2,
        )


def test_extract_rejects_ambiguous_basename_binding(tmp_path: pathlib.Path) -> None:
    left = tmp_path / "left"
    right = tmp_path / "right"
    left.mkdir()
    right.mkdir()
    (left / "same.smt2").write_text("", encoding="utf-8")
    (right / "same.smt2").write_text("", encoding="utf-8")
    population = tmp_path / "population.txt"
    population.write_text(f"{left / 'same.smt2'}\n{right / 'same.smt2'}\n", encoding="utf-8")
    with pytest.raises(CENSUS.CensusError, match="cannot bind a basename sidecar uniquely"):
        CENSUS.read_population(population)


def test_first_causal_decline_skips_shape_and_support_misses() -> None:
    trace = {
        "attempts": [
            {"route": "probe", "outcome": "probe"},
            {"route": "dl-online", "outcome": "declined", "reason": "not-applicable"},
            {"route": "lia-simplex", "outcome": "declined", "reason": "unsupported"},
            {
                "route": "nia-linearize",
                "outcome": "declined",
                "reason": "budget",
                "detail": "timeout",
            },
        ]
    }
    assert CENSUS.first_causal_decline(trace) == {
        "route": "nia-linearize",
        "reason": "budget",
        "detail": "timeout",
    }


def test_analyze_traces_requires_exact_population_order(tmp_path: pathlib.Path) -> None:
    trace_path = tmp_path / "trace.jsonl"
    trace_path.write_text(
        '{"file":"second.smt2","status":"decided","verdict":"unknown",'
        '"trace":{"schema_version":1,"attempts":[]}}\n',
        encoding="utf-8",
    )
    with pytest.raises(CENSUS.CensusError, match="trace identity/order differs"):
        CENSUS.analyze_traces(["first.smt2"], trace_path)


def test_analyze_traces_classifies_ingest_resource_limit_without_route_trace(
    tmp_path: pathlib.Path,
) -> None:
    trace_path = tmp_path / "trace.jsonl"
    trace_path.write_text(
        '{"file":"first.smt2","status":"ingest-resource-limit",'
        '"verdict":"unknown","detail":"distinct pair ceiling"}\n',
        encoding="utf-8",
    )
    result = CENSUS.analyze_traces(["first.smt2"], trace_path)
    assert result["schema"] == "axeyum-qf-nia-a3-causal-census-v2"
    assert result["buckets"] == [
        {
            "route": "smtlib-ingest",
            "reason": "resource-limit",
            "kind": "ResourceLimit",
            "count": 1,
        }
    ]
    assert result["cases"][0]["trace"] is None
    assert result["cases"][0]["first_causal_decline"]["detail"] == "distinct pair ceiling"


def test_analyze_traces_rejects_malformed_resource_record(tmp_path: pathlib.Path) -> None:
    trace_path = tmp_path / "trace.jsonl"
    trace_path.write_text(
        '{"file":"first.smt2","status":"ingest-resource-limit",'
        '"verdict":"unknown","detail":"distinct pair ceiling",'
        '"trace":{"schema_version":1,"attempts":[]}}\n',
        encoding="utf-8",
    )
    with pytest.raises(CENSUS.CensusError, match="unexpectedly has a route trace"):
        CENSUS.analyze_traces(["first.smt2"], trace_path)
