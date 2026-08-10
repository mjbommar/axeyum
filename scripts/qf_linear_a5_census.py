#!/usr/bin/env python3
"""Validate, capture, and derive the preregistered A5 linear census."""

from __future__ import annotations

import argparse
import contextlib
import csv
import dataclasses
import datetime as dt
import fcntl
import hashlib
import io
import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile
import time
from collections import Counter, defaultdict
from typing import Any, Iterator, Sequence


ROOT = pathlib.Path(__file__).resolve().parents[1]
TIMEOUT_MS = 24_000
MEMORY_GB = 8
FROZEN_ROWS = 200
MAX_START_LOAD = 12.0
ALLOWED_VERDICTS = {"sat", "unsat", "unknown"}
SIDECAR_OUTCOMES = {"sat", "unsat", "unsolved"}
HEADER = ["file", "axeyum", "reference", "declared"]


@dataclasses.dataclass(frozen=True)
class DivisionSpec:
    logic: str
    list_sha256: str
    sidecar_sha256: str
    axeyum_solved: int
    reference_solved: int
    both: int
    axeyum_only: int
    reference_only: int
    disagreements: int
    solver_commit: str
    timestamp_utc: str

    @property
    def list_path(self) -> pathlib.Path:
        return ROOT / f"bench-results/parity-lists/{self.logic}.txt"


SPECS = {
    "QF_LRA": DivisionSpec(
        "QF_LRA",
        "b636239947db1e65f2665a62fca8f852acdcd459c799a9bb326c718a1d1d8da5",
        "106913be84886cdb2e83894cdde8d327ea7c3cad75504e397d8a6876a88e9add",
        86, 146, 86, 0, 60, 0, "8ea6a7cad", "2026-08-06T12:44:30Z",
    ),
    "QF_RDL": DivisionSpec(
        "QF_RDL",
        "9dc32e2c5dfbd2d05f79d67ee80683d6941a6dab5e0bc0cc9936dc3ba8e4f149",
        "be59cfacc18eab60225d5f0990e6614d1b55299a60f809c77992ca56d034aab1",
        105, 155, 105, 0, 50, 0, "b353419e7", "2026-08-06T13:54:23Z",
    ),
    "QF_IDL": DivisionSpec(
        "QF_IDL",
        "d7c9713a0280a9ec0cb03e7072acd2cc01a089613c05349984cc1a4f4c6a431d",
        "2debb3525937eefd6a1b0a62c4aedb406766f80f0a558393ade9df7594a0d862",
        68, 124, 68, 0, 56, 0, "198f2dc1b", "2026-08-06T20:47:11Z",
    ),
}

SC39_SUFFIX = "/QF_LRA/sc/sc-39.base.cvc.smt2"
LPSAT_SUFFIX = "/QF_IDL/sal/lpsat/lpsat-goal-18.smt2"


class CensusError(ValueError):
    """An input or capture violates the preregistered A5 contract."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def json_text(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def atomic_write_bytes(path: pathlib.Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as sink:
            sink.write(data)
            sink.flush()
            os.fsync(sink.fileno())
        os.replace(temporary, path)
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(temporary)
        raise


def atomic_write_text(path: pathlib.Path, text: str) -> None:
    atomic_write_bytes(path, text.encode("utf-8"))


def read_population(spec: DivisionSpec, *, require_files: bool = True) -> list[str]:
    actual = sha256_file(spec.list_path)
    if actual != spec.list_sha256:
        raise CensusError(f"{spec.logic}: list digest {actual} != {spec.list_sha256}")
    rows = [line.strip() for line in spec.list_path.read_text(encoding="utf-8").splitlines()]
    if any(not row for row in rows):
        raise CensusError(f"{spec.logic}: frozen list contains a blank row")
    if len(rows) != FROZEN_ROWS:
        raise CensusError(f"{spec.logic}: expected {FROZEN_ROWS} rows, got {len(rows)}")
    duplicates = sorted(path for path, count in Counter(rows).items() if count > 1)
    if duplicates:
        raise CensusError(f"{spec.logic}: duplicate population path {duplicates[0]}")
    if require_files:
        missing = [row for row in rows if not pathlib.Path(row).is_file()]
        if missing:
            raise CensusError(f"{spec.logic}: missing corpus path {missing[0]}")
    return rows


def smtlib_tokens(text: str) -> list[str]:
    cleaned: list[str] = []
    index = 0
    state = "normal"
    while index < len(text):
        char = text[index]
        if state == "comment":
            if char == "\n":
                state = "normal"
                cleaned.append(" ")
            index += 1
            continue
        if state == "string":
            if char == '"':
                if index + 1 < len(text) and text[index + 1] == '"':
                    index += 2
                    continue
                state = "normal"
            index += 1
            continue
        if state == "quoted":
            if char == "|":
                state = "normal"
            index += 1
            continue
        if char == ";":
            state = "comment"
        elif char == '"':
            state = "string"
        elif char == "|":
            state = "quoted"
        elif char in "()":
            cleaned.append(" ")
        else:
            cleaned.append(char)
        index += 1
    return "".join(cleaned).split()


def declared_status(path: pathlib.Path) -> str | None:
    tokens = smtlib_tokens(path.read_text(encoding="utf-8"))
    for index, token in enumerate(tokens[:-1]):
        if token == ":status" and tokens[index + 1] in ALLOWED_VERDICTS:
            return tokens[index + 1]
    return None


def expected_matrix(spec: DivisionSpec) -> dict[str, int]:
    return {
        "rows": FROZEN_ROWS,
        "axeyum_solved": spec.axeyum_solved,
        "reference_solved": spec.reference_solved,
        "both": spec.both,
        "axeyum_only": spec.axeyum_only,
        "reference_only": spec.reference_only,
        "disagreements": spec.disagreements,
    }


def matrix(rows: Sequence[dict[str, str]]) -> dict[str, int]:
    counts = {
        "rows": len(rows), "axeyum_solved": 0, "reference_solved": 0,
        "both": 0, "axeyum_only": 0, "reference_only": 0, "disagreements": 0,
    }
    for row in rows:
        a = row["axeyum"]
        r = row["reference"]
        a_solved = a in {"sat", "unsat"}
        r_solved = r in {"sat", "unsat"}
        counts["axeyum_solved"] += int(a_solved)
        counts["reference_solved"] += int(r_solved)
        counts["both"] += int(a_solved and r_solved)
        counts["axeyum_only"] += int(a_solved and not r_solved)
        counts["reference_only"] += int(r_solved and not a_solved)
        counts["disagreements"] += int(a_solved and r_solved and a != r)
    return counts


def validate_historical_sidecar(
    spec: DivisionSpec, path: pathlib.Path, *, require_digest: bool = True
) -> tuple[bytes, list[dict[str, str]]]:
    raw = path.read_bytes()
    if require_digest and sha256_bytes(raw) != spec.sidecar_sha256:
        raise CensusError(
            f"{spec.logic}: historical sidecar digest {sha256_bytes(raw)} "
            f"!= {spec.sidecar_sha256}"
        )
    population = read_population(spec)
    reader = csv.DictReader(io.StringIO(raw.decode("utf-8")), delimiter="\t")
    if reader.fieldnames != HEADER:
        raise CensusError(f"{spec.logic}: historical header {reader.fieldnames!r} != {HEADER!r}")
    rows = list(reader)
    if len(rows) != FROZEN_ROWS:
        raise CensusError(f"{spec.logic}: historical rows {len(rows)} != {FROZEN_ROWS}")
    identities = [row["file"] for row in rows]
    if identities != population:
        for index, (actual, expected) in enumerate(zip(identities, population, strict=False), 1):
            if actual != expected:
                raise CensusError(
                    f"{spec.logic}: historical order differs at row {index}: "
                    f"{actual!r} != {expected!r}"
                )
        raise CensusError(f"{spec.logic}: historical identity count differs")
    for row in rows:
        file = row["file"]
        if row["axeyum"] not in SIDECAR_OUTCOMES:
            raise CensusError(f"{file}: invalid historical Axeyum outcome {row['axeyum']!r}")
        if row["reference"] not in SIDECAR_OUTCOMES:
            raise CensusError(f"{file}: invalid historical reference outcome {row['reference']!r}")
        if row["declared"] not in ALLOWED_VERDICTS:
            raise CensusError(f"{file}: invalid historical declared status {row['declared']!r}")
        source_declared = declared_status(pathlib.Path(file))
        if source_declared != row["declared"]:
            raise CensusError(
                f"{file}: historical declared {row['declared']!r} != source {source_declared!r}"
            )
        for owner in ("axeyum", "reference"):
            verdict = row[owner]
            if (
                verdict in {"sat", "unsat"}
                and row["declared"] in {"sat", "unsat"}
                and verdict != row["declared"]
            ):
                raise CensusError(
                    f"{file}: historical {owner} verdict {verdict} disagrees with declared "
                    f"{row['declared']}"
                )
    actual_matrix = matrix(rows)
    if actual_matrix != expected_matrix(spec):
        raise CensusError(
            f"{spec.logic}: historical matrix {actual_matrix} != {expected_matrix(spec)}"
        )
    return raw, rows


def retain_historical(source_dir: pathlib.Path, output_dir: pathlib.Path) -> dict[str, Any]:
    manifest: dict[str, Any] = {"schema": "axeyum-qf-linear-a5-historical-v1", "divisions": {}}
    validated: list[tuple[DivisionSpec, bytes]] = []
    for spec in SPECS.values():
        source = source_dir / f"{spec.logic}.tsv"
        raw, rows = validate_historical_sidecar(spec, source)
        validated.append((spec, raw))
        manifest["divisions"][spec.logic] = {
            "list": str(spec.list_path.relative_to(ROOT)),
            "list_sha256": spec.list_sha256,
            "sidecar": f"{spec.logic}.tsv",
            "sidecar_sha256": sha256_bytes(raw),
            "matrix": matrix(rows),
            "solver_commit": spec.solver_commit,
            "timestamp_utc": spec.timestamp_utc,
        }
    for spec, raw in validated:
        atomic_write_bytes(output_dir / f"{spec.logic}.tsv", raw)
    atomic_write_text(output_dir / "manifest.json", json_text(manifest))
    return manifest


def read_jsonl(path: pathlib.Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            raise CensusError(f"blank JSONL row at {path}:{line_number}")
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise CensusError(f"invalid JSON at {path}:{line_number}: {error}") from error
        if not isinstance(record, dict):
            raise CensusError(f"JSONL row is not an object at {path}:{line_number}")
        records.append(record)
    return records


def validate_trace(trace: object, file: str) -> dict[str, Any]:
    if not isinstance(trace, dict) or trace.get("schema_version") != 1:
        raise CensusError(f"{file}: missing schema-1 route trace")
    attempts = trace.get("attempts")
    if not isinstance(attempts, list) or not attempts:
        raise CensusError(f"{file}: route trace has no attempts")
    for index, attempt in enumerate(attempts, 1):
        if not isinstance(attempt, dict) or not isinstance(attempt.get("route"), str):
            raise CensusError(f"{file}: malformed trace attempt {index}")
        outcome = attempt.get("outcome")
        if outcome not in {"probe", "decided", "declined"}:
            raise CensusError(f"{file}: invalid trace outcome {outcome!r}")
        if outcome == "decided" and attempt.get("verdict") not in {"sat", "unsat"}:
            raise CensusError(f"{file}: decided trace attempt lacks verdict")
        if outcome == "declined" and attempt.get("reason") not in {
            "unsupported", "not-applicable", "budget", "incomplete", "verifier-rejected"
        }:
            raise CensusError(f"{file}: declined trace attempt lacks typed reason")
    return trace


def validate_current_records(
    spec: DivisionSpec, records: Sequence[dict[str, Any]]
) -> list[str]:
    population = read_population(spec)
    identities = [record.get("file") for record in records]
    if identities != population:
        for index, (actual, expected) in enumerate(zip(identities, population, strict=False), 1):
            if actual != expected:
                raise CensusError(
                    f"{spec.logic}: current order differs at row {index}: {actual!r} != {expected!r}"
                )
        raise CensusError(f"{spec.logic}: current row count {len(records)} != {len(population)}")
    for record in records:
        file = str(record["file"])
        if record.get("status") != "decided":
            raise CensusError(f"{file}: current status {record.get('status')!r} != 'decided'")
        verdict = record.get("verdict")
        if verdict not in ALLOWED_VERDICTS:
            raise CensusError(f"{file}: invalid current verdict {verdict!r}")
        trace = validate_trace(record.get("trace"), file)
        decisions = [attempt for attempt in trace["attempts"] if attempt["outcome"] == "decided"]
        if verdict in {"sat", "unsat"}:
            if not decisions or decisions[-1]["verdict"] != verdict:
                raise CensusError(f"{file}: top-level {verdict} lacks matching terminal decision")
    return population


def normalize_detail(detail: str) -> str:
    normalized = detail.lower()
    normalized = re.sub(r"(?:/[^\s,;()]+)+", "<path>", normalized)
    normalized = re.sub(r"\b0x[0-9a-f]+\b", "<hex>", normalized)
    normalized = re.sub(r"\b\d+(?:\.\d+)?\b", "<n>", normalized)
    return " ".join(normalized.split())


def source_family(logic: str, file: str) -> str:
    parts = pathlib.PurePosixPath(file).parts
    try:
        index = parts.index(logic)
    except ValueError as error:
        raise CensusError(f"{file}: path does not contain logic component {logic}") from error
    suffix = parts[index + 1 : -1]
    return "/".join(suffix[:2]) if suffix else "."


def substantive_declines(trace: dict[str, Any]) -> list[dict[str, Any]]:
    declines = [dict(a) for a in trace["attempts"] if a.get("outcome") == "declined"]
    typed = [a for a in declines if a.get("reason") not in {"unsupported", "not-applicable"}]
    return typed or declines


def classify(trace: dict[str, Any]) -> tuple[str, list[dict[str, Any]]]:
    declines = substantive_declines(trace)
    if not declines:
        raise CensusError("reference-only trace has no decline boundary")
    text = "\n".join(
        " ".join(str(a.get(key, "")) for key in ("route", "reason", "kind", "detail"))
        for a in declines
    ).lower()
    if "verifier-rejected" in text or any(word in text for word in ("replay", "model did not", "verification")):
        return "model-replay", declines
    # Route-trace schema v1 intentionally serializes every timeout and
    # deterministic resource kind as `reason: budget`. Preserve the exact
    # production spelling of the online-LRA normalization admission ceiling so
    # it does not collapse into a later coarse bucket.
    if any(
        word in text
        for word in (
            "normaliz", "resource-limit", "coefficient work", "memo", "node visit",
            "atom cap exceeded",
        )
    ):
        return "normalization-resource", declines
    if any(word in text for word in ("difference shape", "difference-logic", "non-unit coefficient", "dl shape")):
        return "unsupported-dl-shape", declines
    if any(word in text for word in ("disequal", "boolean skeleton", "equality gate", "tseitin")):
        return "disequality-boolean-structure", declines
    if any(word in text for word in ("explanation", "core", "lemma", "farkas")):
        return "explanation-core", declines
    terminal = declines[-1]
    if terminal.get("reason") == "budget" or any(
        word in text for word in ("timeout", "deadline", "budget", "round limit", "node limit")
    ):
        return "search-budget", declines
    return "other-unsupported", declines


def join_division(
    spec: DivisionSpec,
    historical: Sequence[dict[str, str]],
    current: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    population = validate_current_records(spec, current)
    if [row["file"] for row in historical] != population:
        raise CensusError(f"{spec.logic}: historical/current populations differ")
    losses: list[dict[str, str]] = []
    gains: list[dict[str, str]] = []
    wrongs: list[dict[str, str]] = []
    residuals: list[dict[str, Any]] = []
    solved = 0
    for old, now in zip(historical, current, strict=True):
        file = old["file"]
        before = old["axeyum"]
        verdict = str(now["verdict"])
        reference = old["reference"]
        declared = old["declared"]
        if before in {"sat", "unsat"} and verdict != before:
            losses.append({"file": file, "historical": before, "current": verdict})
        if verdict in {"sat", "unsat"}:
            solved += 1
            if before == "unsolved":
                gains.append({"file": file, "current": verdict, "reference": reference})
            if reference in {"sat", "unsat"} and verdict != reference:
                wrongs.append({"file": file, "current": verdict, "authority": reference})
            if declared in {"sat", "unsat"} and verdict != declared:
                wrongs.append({"file": file, "current": verdict, "authority": declared})
        if verdict == "unknown" and reference in {"sat", "unsat"}:
            trace = validate_trace(now["trace"], file)
            bucket, declines = classify(trace)
            terminal = declines[-1]
            residuals.append({
                "division": spec.logic,
                "file": file,
                "source_family": source_family(spec.logic, file),
                "declared": declared,
                "axeyum": verdict,
                "reference": reference,
                "bucket": bucket,
                "first_substantive_decline": declines[0],
                "terminal_substantive_decline": terminal,
                "normalized_detail_family": normalize_detail(str(terminal.get("detail", ""))),
                "trace": trace,
            })
    if losses:
        raise CensusError(f"{spec.logic}: {len(losses)} historical solved losses; first={losses[0]}")
    if wrongs:
        raise CensusError(f"{spec.logic}: {len(wrongs)} wrong current verdicts; first={wrongs[0]}")
    sc39 = [record for record in current if str(record["file"]).endswith(SC39_SUFFIX)]
    lpsat = [record for record in current if str(record["file"]).endswith(LPSAT_SUFFIX)]
    controls: dict[str, Any] = {}
    if spec.logic == "QF_LRA":
        if len(sc39) != 1 or sc39[0]["verdict"] != "unknown":
            raise CensusError("QF_LRA: sc-39 control did not return bounded unknown")
        bucket, declines = classify(validate_trace(sc39[0]["trace"], str(sc39[0]["file"])))
        if bucket != "normalization-resource":
            raise CensusError(f"QF_LRA: sc-39 control bucket is {bucket!r}")
        controls["sc39"] = {"file": sc39[0]["file"], "verdict": "unknown", "bucket": bucket, "terminal": declines[-1]}
    if spec.logic == "QF_IDL":
        if len(lpsat) != 1 or lpsat[0]["verdict"] != "unsat":
            raise CensusError("QF_IDL: lpsat-goal-18 control did not retain UNSAT")
        controls["lpsat_goal_18"] = {"file": lpsat[0]["file"], "verdict": "unsat"}
    return {
        "logic": spec.logic,
        "rows": len(current),
        "historical_solved": spec.axeyum_solved,
        "current_solved": solved,
        "gains": gains,
        "losses": losses,
        "wrongs": wrongs,
        "reference_only": len(residuals),
        "controls": controls,
        "residuals": residuals,
    }


def lossless_groups(residuals: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    groups: dict[tuple[str, ...], list[str]] = defaultdict(list)
    for case in residuals:
        terminal = case["terminal_substantive_decline"]
        key = (
            case["division"], case["source_family"], case["bucket"],
            str(terminal.get("route", "")), str(terminal.get("reason", "")),
            str(terminal.get("kind", "")), case["normalized_detail_family"], case["reference"],
        )
        groups[key].append(case["file"])
    rows = []
    for key, files in groups.items():
        division, family, bucket, route, reason, kind, detail, reference = key
        rows.append({
            "division": division, "source_family": family, "bucket": bucket,
            "terminal_route": route, "reason": reason, "kind": kind or None,
            "normalized_detail_family": detail, "reference_verdict": reference,
            "count": len(files), "selection_eligible": len(files) >= 3, "files": files,
        })
    rows.sort(key=lambda row: (-row["count"], row["division"], row["source_family"], row["bucket"], row["files"]))
    return rows


def derive(historical_dir: pathlib.Path, capture_dir: pathlib.Path, output_dir: pathlib.Path) -> dict[str, Any]:
    divisions = []
    all_residuals: list[dict[str, Any]] = []
    inputs: dict[str, Any] = {}
    for spec in SPECS.values():
        historical_path = historical_dir / f"{spec.logic}.tsv"
        raw, historical = validate_historical_sidecar(spec, historical_path)
        capture_path = capture_dir / f"{spec.logic}.axeyum.jsonl"
        current = read_jsonl(capture_path)
        result = join_division(spec, historical, current)
        all_residuals.extend(result.pop("residuals"))
        divisions.append(result)
        inputs[spec.logic] = {
            "list_sha256": spec.list_sha256,
            "historical_sha256": sha256_bytes(raw),
            "capture_sha256": sha256_file(capture_path),
        }
    groups = lossless_groups(all_residuals)
    census = {
        "schema": "axeyum-qf-linear-a5-census-v1",
        "divisions": divisions,
        "bucket_counts": dict(sorted(Counter(row["bucket"] for row in all_residuals).items())),
        "lossless_groups": groups,
        "selection_candidates": [row for row in groups if row["selection_eligible"]],
        "residuals": all_residuals,
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    atomic_write_text(output_dir / "census.json", json_text(census))
    for spec in SPECS.values():
        files = [row["file"] for row in all_residuals if row["division"] == spec.logic]
        atomic_write_text(output_dir / f"{spec.logic}.reference-only.txt", "".join(f"{file}\n" for file in files))
    outputs = {
        path.name: {"sha256": sha256_file(path), "bytes": path.stat().st_size}
        for path in sorted(output_dir.glob("*")) if path.name != "manifest.json"
    }
    manifest = {
        "schema": "axeyum-qf-linear-a5-derivation-manifest-v1",
        "inputs": inputs,
        "outputs": outputs,
    }
    atomic_write_text(output_dir / "manifest.json", json_text(manifest))
    return census


def load_average() -> str:
    try:
        return " ".join(pathlib.Path("/proc/loadavg").read_text().split()[:3])
    except OSError as error:
        raise CensusError(f"cannot read /proc/loadavg: {error}") from error


def require_capture_host() -> None:
    if os.cpu_count() != 24:
        raise CensusError(f"capture requires 24 cores, found {os.cpu_count()}")
    load = float(load_average().split()[0])
    if load > MAX_START_LOAD:
        raise CensusError(f"one-minute load {load:.2f} exceeds {MAX_START_LOAD:.2f}")


@contextlib.contextmanager
def capture_lock() -> Iterator[None]:
    with pathlib.Path("/tmp/axeyum-qf-linear-a5-capture.lock").open("a+b") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise CensusError("another A5 linear capture is running") from error
        yield


def git_capture_identity() -> dict[str, Any]:
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=ROOT,
        check=True, stdout=subprocess.PIPE, text=True,
    ).stdout
    if status:
        raise CensusError("tracked worktree is not clean; commit before capture")
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True,
    ).stdout.strip()
    upstream = subprocess.run(
        ["git", "rev-parse", "@{upstream}"], cwd=ROOT, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    ).stdout.strip()
    if commit != upstream:
        raise CensusError(f"capture commit is not pushed exactly: {commit} != {upstream}")
    return {"git_commit": commit, "git_upstream": upstream, "tracked_tree_clean": True}


def capture_axeyum(
    spec: DivisionSpec,
    binary: pathlib.Path,
    output: pathlib.Path,
    metadata_path: pathlib.Path,
    failure_path: pathlib.Path,
) -> None:
    population = read_population(spec)
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise CensusError(f"capture binary is not executable: {binary}")
    timeout_bin = shutil.which("timeout")
    if timeout_bin is None:
        raise CensusError("GNU timeout is required")
    command = [
        timeout_bin, "--signal=TERM", "--kill-after=5s", "6000", "env",
        f"MEM_LIMIT_GB={MEMORY_GB}", str(ROOT / "scripts/mem-run.sh"), str(binary),
        "--list", str(spec.list_path), str(TIMEOUT_MS), "--json",
    ]
    identity = git_capture_identity()
    require_capture_host()
    base = {
        **identity, "logic": spec.logic, "command": command, "binary": str(binary),
        "binary_sha256": sha256_file(binary), "binary_bytes": binary.stat().st_size,
        "list": str(spec.list_path.relative_to(ROOT)), "list_sha256": spec.list_sha256,
        "list_rows": FROZEN_ROWS, "timeout_ms": TIMEOUT_MS, "memory_gb": MEMORY_GB,
        "host_cores": os.cpu_count(),
        "process_topology": "sequential-isolated-per-file-v1",
        "active_worker_limit": 1,
        "memory_scope": "inherited-per-process-address-space",
        "aggregate_memory_enforcement": "not-enforced",
    }
    started_utc = utc_now()
    started = time.monotonic()
    load_start = load_average()
    with capture_lock(), tempfile.TemporaryDirectory(prefix=f"axeyum-a5-{spec.logic.lower()}-") as temporary:
        stdout_path = pathlib.Path(temporary) / "stdout.jsonl"
        stderr_path = pathlib.Path(temporary) / "stderr.bin"
        result: subprocess.CompletedProcess[bytes] | None = None
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                result = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr, timeout=6010, check=False)
            stdout_raw = stdout_path.read_bytes()
            stderr_raw = stderr_path.read_bytes()
            if result.returncode != 0:
                raise CensusError(f"capture exited {result.returncode}")
            if stderr_raw:
                raise CensusError(f"capture emitted {len(stderr_raw)} stderr bytes")
            records = read_jsonl(stdout_path)
            validate_current_records(spec, records)
        except (CensusError, OSError, subprocess.SubprocessError) as error:
            stdout_raw = stdout_path.read_bytes() if stdout_path.is_file() else b""
            stderr_raw = stderr_path.read_bytes() if stderr_path.is_file() else b""
            failure = {
                "schema": "axeyum-qf-linear-a5-capture-failure-v2", **base,
                "started_utc": started_utc, "ended_utc": utc_now(),
                "elapsed_ms": round((time.monotonic() - started) * 1000),
                "load_start": load_start, "load_end": load_average(),
                "exit_code": None if result is None else result.returncode,
                "emitted_rows": stdout_raw.count(b"\n"), "first_validator_error": str(error),
                "stdout_sha256": sha256_bytes(stdout_raw), "stdout_bytes": len(stdout_raw),
                "stderr_sha256": sha256_bytes(stderr_raw), "stderr_bytes": len(stderr_raw),
                "credited": False,
            }
            atomic_write_text(failure_path, json_text(failure))
            raise
    metadata = {
        "schema": "axeyum-qf-linear-a5-capture-v2", **base,
        "started_utc": started_utc, "ended_utc": utc_now(),
        "elapsed_ms": round((time.monotonic() - started) * 1000),
        "load_start": load_start, "load_end": load_average(), "exit_code": 0,
        "records": len(records), "stdout_sha256": sha256_bytes(stdout_raw),
        "stdout_bytes": len(stdout_raw), "stderr_sha256": sha256_bytes(stderr_raw),
        "stderr_bytes": len(stderr_raw),
    }
    atomic_write_bytes(output, stdout_raw)
    atomic_write_text(metadata_path, json_text(metadata))
    failure_path.unlink(missing_ok=True)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    historical = sub.add_parser("validate-historical")
    historical.add_argument("--source-dir", type=pathlib.Path, required=True)
    historical.add_argument("--output-dir", type=pathlib.Path, required=True)
    capture = sub.add_parser("capture")
    capture.add_argument("--logic", choices=sorted(SPECS), required=True)
    capture.add_argument("--binary", type=pathlib.Path, required=True)
    capture.add_argument("--output", type=pathlib.Path, required=True)
    capture.add_argument("--metadata", type=pathlib.Path, required=True)
    capture.add_argument("--failure-metadata", type=pathlib.Path, required=True)
    derive_parser = sub.add_parser("derive")
    derive_parser.add_argument("--historical-dir", type=pathlib.Path, required=True)
    derive_parser.add_argument("--capture-dir", type=pathlib.Path, required=True)
    derive_parser.add_argument("--output-dir", type=pathlib.Path, required=True)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "validate-historical":
            result = retain_historical(args.source_dir, args.output_dir)
        elif args.command == "capture":
            capture_axeyum(
                SPECS[args.logic], args.binary.resolve(), args.output.resolve(),
                args.metadata.resolve(), args.failure_metadata.resolve(),
            )
            result = {"logic": args.logic, "status": "captured"}
        else:
            result = derive(args.historical_dir, args.capture_dir, args.output_dir)
    except (CensusError, OSError, subprocess.SubprocessError) as error:
        print(f"qf_linear_a5_census: {error}", file=os.sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
