#!/usr/bin/env python3

from __future__ import annotations

import dataclasses
import importlib.util
import io
import pathlib
import sys

import pytest


SCRIPT = pathlib.Path(__file__).parents[1] / "qf_linear_a5_census.py"
SPEC = importlib.util.spec_from_file_location("qf_linear_a5_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CENSUS = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CENSUS
SPEC.loader.exec_module(CENSUS)


def attempt(
    route: str,
    reason: str,
    detail: str = "",
    kind: str | None = None,
) -> dict[str, object]:
    row: dict[str, object] = {"route": route, "outcome": "declined", "reason": reason}
    if detail:
        row["detail"] = detail
    if kind is not None:
        row["kind"] = kind
    return row


def current(file: str, verdict: str, decline: dict[str, object] | None = None) -> dict[str, object]:
    attempts: list[dict[str, object]] = [
        {"route": "auto", "outcome": "probe", "detail": "fragment {real}"}
    ]
    if verdict in {"sat", "unsat"}:
        attempts.append({"route": "lra", "outcome": "decided", "verdict": verdict})
    else:
        attempts.append(decline or attempt("lra", "budget", "query deadline expired", "timeout"))
    return {
        "file": file,
        "status": "decided",
        "verdict": verdict,
        "trace": {"schema_version": 1, "attempts": attempts},
    }


def historical(file: str, axeyum: str, reference: str, declared: str) -> dict[str, str]:
    return {"file": file, "axeyum": axeyum, "reference": reference, "declared": declared}


def test_smtlib_tokenizer_ignores_comments_strings_and_quoted_symbols() -> None:
    text = '; :status sat\n(set-info :status unsat) (assert (= ":status sat" |:status|))\n'
    assert CENSUS.smtlib_tokens(text).count(":status") == 1


def test_validate_trace_requires_typed_complete_attempts() -> None:
    trace = {"schema_version": 1, "attempts": [attempt("lra", "budget", "deadline")]}
    assert CENSUS.validate_trace(trace, "case.smt2") == trace
    trace["attempts"][0]["reason"] = "mystery"
    with pytest.raises(CENSUS.CensusError, match="typed reason"):
        CENSUS.validate_trace(trace, "case.smt2")


def make_historical_fixture(tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch):
    monkeypatch.setattr(CENSUS, "ROOT", tmp_path)
    monkeypatch.setattr(CENSUS, "FROZEN_ROWS", 3)
    list_dir = tmp_path / "bench-results/parity-lists"
    list_dir.mkdir(parents=True)
    files = []
    for index, status in enumerate(("sat", "unsat", "unknown"), 1):
        file = tmp_path / "corpus" / "QF_RDL" / "family" / f"case-{index}.smt2"
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(f"(set-info :status {status})\n", encoding="utf-8")
        files.append(str(file))
    list_path = list_dir / "QF_RDL.txt"
    list_path.write_text("".join(f"{file}\n" for file in files), encoding="utf-8")
    rows = [
        historical(files[0], "sat", "sat", "sat"),
        historical(files[1], "unsolved", "unsat", "unsat"),
        historical(files[2], "unsolved", "unsolved", "unknown"),
    ]
    stream = io.StringIO(newline="")
    writer = __import__("csv").DictWriter(
        stream, fieldnames=CENSUS.HEADER, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(rows)
    raw = stream.getvalue().encode()
    sidecar = tmp_path / "QF_RDL.tsv"
    sidecar.write_bytes(raw)
    spec = CENSUS.DivisionSpec(
        "QF_RDL", CENSUS.sha256_file(list_path), CENSUS.sha256_bytes(raw),
        1, 2, 1, 0, 1, 0, "deadbeef", "2026-08-07T00:00:00Z",
    )
    return spec, sidecar, rows, files


def test_historical_validator_reproduces_digest_order_matrix_and_status(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    spec, sidecar, rows, _ = make_historical_fixture(tmp_path, monkeypatch)
    raw, actual = CENSUS.validate_historical_sidecar(spec, sidecar)
    assert CENSUS.sha256_bytes(raw) == spec.sidecar_sha256
    assert actual == rows
    assert CENSUS.matrix(actual) == CENSUS.expected_matrix(spec)


def test_historical_validator_rejects_order_drift_even_without_digest_gate(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    spec, sidecar, _, _ = make_historical_fixture(tmp_path, monkeypatch)
    lines = sidecar.read_text().splitlines()
    sidecar.write_text("\n".join([lines[0], lines[2], lines[1], lines[3]]) + "\n")
    with pytest.raises(CENSUS.CensusError, match="order differs"):
        CENSUS.validate_historical_sidecar(spec, sidecar, require_digest=False)


def test_historical_validator_rejects_matrix_drift(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    spec, sidecar, _, _ = make_historical_fixture(tmp_path, monkeypatch)
    text = sidecar.read_text().replace("\tunsolved\tunsat\tunsat", "\tunsat\tunsat\tunsat")
    sidecar.write_text(text)
    with pytest.raises(CENSUS.CensusError, match="historical matrix"):
        CENSUS.validate_historical_sidecar(spec, sidecar, require_digest=False)


def test_validate_current_rejects_missing_trace_and_decision_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec = dataclasses.replace(CENSUS.SPECS["QF_RDL"])
    files = ["/corpus/QF_RDL/f/a.smt2"]
    monkeypatch.setattr(CENSUS, "read_population", lambda _spec: files)
    row = current(files[0], "sat")
    row.pop("trace")
    with pytest.raises(CENSUS.CensusError, match="schema-1"):
        CENSUS.validate_current_records(spec, [row])
    row = current(files[0], "sat")
    row["trace"]["attempts"][-1]["verdict"] = "unsat"
    with pytest.raises(CENSUS.CensusError, match="matching terminal decision"):
        CENSUS.validate_current_records(spec, [row])


def test_join_is_monotone_and_allows_only_agreeing_gain(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = dataclasses.replace(CENSUS.SPECS["QF_RDL"], axeyum_solved=1)
    files = [
        "/corpus/QF_RDL/f/a.smt2",
        "/corpus/QF_RDL/f/b.smt2",
        "/corpus/QF_RDL/f/c.smt2",
    ]
    monkeypatch.setattr(CENSUS, "read_population", lambda _spec: files)
    old = [
        historical(files[0], "sat", "sat", "sat"),
        historical(files[1], "unsolved", "unsat", "unsat"),
        historical(files[2], "unsolved", "unsolved", "unknown"),
    ]
    now = [current(files[0], "sat"), current(files[1], "unsat"), current(files[2], "unknown")]
    result = CENSUS.join_division(spec, old, now)
    assert result["current_solved"] == 2
    assert result["gains"] == [{"file": files[1], "current": "unsat", "reference": "unsat"}]
    assert result["losses"] == []
    assert result["wrongs"] == []


def test_join_rejects_historical_loss(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = CENSUS.SPECS["QF_RDL"]
    file = "/corpus/QF_RDL/f/a.smt2"
    monkeypatch.setattr(CENSUS, "read_population", lambda _spec: [file])
    with pytest.raises(CENSUS.CensusError, match="historical solved losses"):
        CENSUS.join_division(
            spec, [historical(file, "sat", "sat", "sat")], [current(file, "unknown")]
        )


def test_join_rejects_wrong_new_solve(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = CENSUS.SPECS["QF_RDL"]
    file = "/corpus/QF_RDL/f/a.smt2"
    monkeypatch.setattr(CENSUS, "read_population", lambda _spec: [file])
    with pytest.raises(CENSUS.CensusError, match="wrong current verdicts"):
        CENSUS.join_division(
            spec, [historical(file, "unsolved", "unsat", "unsat")], [current(file, "sat")]
        )


@pytest.mark.parametrize(
    ("decline", "bucket"),
    [
        (attempt("lra", "verifier-rejected", "candidate model failed replay"), "model-replay"),
        (attempt("lra", "budget", "normalization coefficient work exhausted", "resource-limit"), "normalization-resource"),
        (attempt("dl-online", "incomplete", "non-unit coefficient difference shape"), "unsupported-dl-shape"),
        (attempt("dl-online", "incomplete", "numeric disequality skeleton"), "disequality-boolean-structure"),
        (attempt("lra", "incomplete", "explanation core too large"), "explanation-core"),
        (attempt("lra", "budget", "query deadline expired", "timeout"), "search-budget"),
        (attempt("lra", "unsupported", "operator outside fragment"), "other-unsupported"),
    ],
)
def test_classification_priority(decline: dict[str, object], bucket: str) -> None:
    trace = {"schema_version": 1, "attempts": [decline]}
    assert CENSUS.classify(trace)[0] == bucket


def test_lossless_group_requires_three_identical_rows() -> None:
    rows = []
    for index in range(3):
        terminal = attempt("lra", "budget", "deadline after 123 rounds", "timeout")
        rows.append({
            "division": "QF_LRA", "source_family": "sc/family", "bucket": "search-budget",
            "terminal_substantive_decline": terminal,
            "normalized_detail_family": CENSUS.normalize_detail(str(terminal["detail"])),
            "reference": "unsat", "file": f"case-{index}.smt2",
        })
    groups = CENSUS.lossless_groups(rows)
    assert groups[0]["count"] == 3
    assert groups[0]["selection_eligible"] is True


def test_lra_sc39_control_requires_typed_resource_boundary(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = CENSUS.SPECS["QF_LRA"]
    file = "/corpus/QF_LRA/sc/sc-39.base.cvc.smt2"
    monkeypatch.setattr(CENSUS, "read_population", lambda _spec: [file])
    old = [historical(file, "unsolved", "unsolved", "unknown")]
    good = current(
        file, "unknown",
        attempt("lra-online", "budget", "normalization coefficient work exhausted", "resource-limit"),
    )
    assert CENSUS.join_division(spec, old, [good])["controls"]["sc39"]["bucket"] == "normalization-resource"
    bad = current(file, "unknown", attempt("lra", "budget", "query deadline expired", "timeout"))
    with pytest.raises(CENSUS.CensusError, match="sc-39 control bucket"):
        CENSUS.join_division(spec, old, [bad])


def test_idl_lpsat_control_must_retain_unsat(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = CENSUS.SPECS["QF_IDL"]
    file = "/corpus/QF_IDL/sal/lpsat/lpsat-goal-18.smt2"
    monkeypatch.setattr(CENSUS, "read_population", lambda _spec: [file])
    old = [historical(file, "unsat", "unsat", "unsat")]
    assert CENSUS.join_division(spec, old, [current(file, "unsat")])["controls"]
    with pytest.raises(CENSUS.CensusError, match="historical solved losses"):
        CENSUS.join_division(spec, old, [current(file, "unknown")])


def test_source_family_is_stable_and_bounded() -> None:
    file = "/root/non-incremental/QF_IDL/sal/lpsat/lpsat-goal-18.smt2"
    assert CENSUS.source_family("QF_IDL", file) == "sal/lpsat"


def test_capture_parser_requires_all_paths() -> None:
    parsed = CENSUS.parser().parse_args(
        [
            "capture", "--logic", "QF_LRA", "--binary", "/tmp/bin",
            "--output", "/tmp/out", "--metadata", "/tmp/meta",
            "--failure-metadata", "/tmp/failure",
        ]
    )
    assert parsed.logic == "QF_LRA"
