#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import json
import pathlib

import pytest


SCRIPT = pathlib.Path(__file__).parents[1] / "qf_uflia_a4_census.py"
SPEC = importlib.util.spec_from_file_location("qf_uflia_a4_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CENSUS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CENSUS)


def attempt(
    route: str,
    reason: str,
    detail: str = "",
    kind: str | None = None,
) -> dict[str, object]:
    row: dict[str, object] = {
        "route": route,
        "outcome": "declined",
        "reason": reason,
    }
    if detail:
        row["detail"] = detail
    if kind is not None:
        row["kind"] = kind
    return row


def axeyum_record(file: pathlib.Path, verdict: str, final: dict[str, object]) -> dict[str, object]:
    return {
        "file": str(file),
        "status": "decided",
        "verdict": verdict,
        "trace": {
            "schema_version": 1,
            "attempts": [
                {"route": "probe", "outcome": "probe", "detail": "fragment {int,uf}"},
                {"route": "euf-online", "outcome": "declined", "reason": "unsupported"},
                final,
            ],
        },
    }


def reference_record(file: pathlib.Path, outcome: str) -> dict[str, object]:
    return {
        "file": str(file),
        "outcome": outcome,
        "elapsed_ms": 3,
        "exit_code": 124 if outcome == "timeout" else 0,
    }


def fixture(tmp_path: pathlib.Path):
    sat = tmp_path / "sat.smt2"
    residual = tmp_path / "residual.smt2"
    timeout = tmp_path / "timeout.smt2"
    sat.write_text('(set-info :status sat)\n(assert (= "forall" "forall"))\n', encoding="utf-8")
    residual.write_text(
        "; forall is a comment\n(set-info :status unsat)\n(assert (not (= (f 0) 1)))\n",
        encoding="utf-8",
    )
    timeout.write_text("(set-logic QF_UFLIA)\n", encoding="utf-8")
    population = [str(sat), str(residual), str(timeout)]
    axeyum = [
        axeyum_record(sat, "sat", {"route": "uf-arithmetic", "outcome": "decided", "verdict": "sat"}),
        axeyum_record(
            residual,
            "unknown",
            attempt("uf-arithmetic", "incomplete", "model projection failed replay", "incomplete"),
        ),
        axeyum_record(
            timeout,
            "unknown",
            attempt("uf-arith-online", "budget", "timeout after 24 rounds"),
        ),
    ]
    reference = [
        reference_record(sat, "sat"),
        reference_record(residual, "unsat"),
        reference_record(timeout, "timeout"),
    ]
    expected = {
        "rows": 3,
        "axeyum_solved": 1,
        "reference_solved": 2,
        "both": 1,
        "axeyum_only": 0,
        "reference_only": 1,
        "disagreements": 0,
    }
    return population, axeyum, reference, expected


def test_smtlib_tokenizer_ignores_comments_strings_and_quoted_symbols() -> None:
    text = '; forall\n(assert (= "exists" |forall|)) (assert (forall ((x Int)) true))\n'
    tokens = CENSUS.smtlib_tokens(text)
    assert tokens.count("forall") == 1
    assert "exists" not in tokens


def test_parse_reference_result_is_fail_closed() -> None:
    assert CENSUS.parse_reference_result(0, b"sat\n", b"") == "sat"
    assert CENSUS.parse_reference_result(124, b"", b"") == "timeout"
    with pytest.raises(CENSUS.CensusError, match="operational failure"):
        CENSUS.parse_reference_result(137, b"", b"killed")
    with pytest.raises(CENSUS.CensusError, match="2 standalone verdicts"):
        CENSUS.parse_reference_result(0, b"sat\nunsat\n", b"")
    with pytest.raises(CENSUS.CensusError, match="timed-out.*emitted a verdict"):
        CENSUS.parse_reference_result(124, b"sat\n", b"")


def test_validate_and_derive_reproduces_counts_and_replay_bucket(
    tmp_path: pathlib.Path,
) -> None:
    population, axeyum, reference, expected = fixture(tmp_path)
    counts, sidecar, residual, census = CENSUS.validate_and_derive(
        population, axeyum, reference, expected_counts=expected
    )
    assert counts == expected
    assert residual == [str(tmp_path / "residual.smt2")]
    assert "\tunsolved\tunsat\tunsat\n" in sidecar
    assert census["bucket_counts"] == {"replay": 1}
    assert census["selection_candidates"] == []
    case = census["cases"][0]
    assert case["first_substantive_decline"]["route"] == "uf-arithmetic"
    assert case["normalized_detail_family"] == "model projection failed replay"


def test_validate_rejects_incomplete_axeyum_record(tmp_path: pathlib.Path) -> None:
    population, axeyum, reference, expected = fixture(tmp_path)
    axeyum[1].pop("trace")
    with pytest.raises(CENSUS.CensusError, match="missing schema-1 route trace"):
        CENSUS.validate_and_derive(population, axeyum, reference, expected_counts=expected)


def test_validate_rejects_operational_reference_outcome(tmp_path: pathlib.Path) -> None:
    population, axeyum, reference, expected = fixture(tmp_path)
    reference[1]["outcome"] = "error"
    reference[1]["exit_code"] = 2
    with pytest.raises(CENSUS.CensusError, match="invalid reference outcome"):
        CENSUS.validate_and_derive(population, axeyum, reference, expected_counts=expected)


def test_validate_rejects_aggregate_drift(tmp_path: pathlib.Path) -> None:
    population, axeyum, reference, expected = fixture(tmp_path)
    wrong = dict(expected)
    wrong["reference_only"] = 2
    with pytest.raises(CENSUS.CensusError, match="aggregate mismatch"):
        CENSUS.validate_and_derive(population, axeyum, reference, expected_counts=wrong)


def test_bucket_priority_and_detail_normalization() -> None:
    trace = {
        "attempts": [
            attempt("euf-online", "incomplete", "candidate model did not replay"),
            attempt("uf-arithmetic", "budget", "timeout after 123 rounds at /tmp/query.smt2"),
        ]
    }
    bucket, declines = CENSUS.classify_case(trace, False)
    assert bucket == "replay"
    assert declines[-1]["route"] == "uf-arithmetic"
    assert CENSUS.normalize_detail(declines[-1]["detail"]) == (
        "timeout after <n> rounds at <path>"
    )


def test_three_identical_lossless_rows_become_selection_candidate() -> None:
    cases = []
    for index in range(3):
        terminal = attempt("uf-arithmetic", "budget", "timeout after 1 round")
        cases.append(
            {
                "file": f"case-{index}.smt2",
                "bucket": "budget-routing",
                "reference": "sat",
                "terminal_substantive_decline": terminal,
                "normalized_detail_family": "timeout after <n> round",
            }
        )
    census = CENSUS.build_census(cases)
    assert census["selection_candidates"][0]["count"] == 3
    assert census["selection_candidates"][0]["files"] == [
        "case-0.smt2",
        "case-1.smt2",
        "case-2.smt2",
    ]


def test_read_jsonl_rejects_blank_rows(tmp_path: pathlib.Path) -> None:
    path = tmp_path / "rows.jsonl"
    path.write_text(json.dumps({"file": "a"}) + "\n\n", encoding="utf-8")
    with pytest.raises(CENSUS.CensusError, match="blank JSONL row"):
        CENSUS.read_jsonl(path)
