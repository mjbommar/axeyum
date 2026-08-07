#!/usr/bin/env python3
"""Capture and validate the preregistered QF_UFLIA A4 causal census."""

from __future__ import annotations

import argparse
import contextlib
import csv
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
import sys
import tempfile
import time
from collections import Counter, defaultdict
from typing import Any, Iterator, Sequence


ROOT = pathlib.Path(__file__).resolve().parents[1]
FROZEN_LIST = ROOT / "bench-results/parity-lists/QF_UFLIA.txt"
FROZEN_LIST_SHA256 = "f88e67890fae78fb27bb35ecc0f19532dc3bc77fd7f1ac7453fcda343b36fb35"
FROZEN_ROWS = 200
EXPECTED_INGEST_ROWS = 26
REFERENCE_BINARY = pathlib.Path("/nas3/data/axeyum/harness/bin/cvc5")
REFERENCE_SHA256 = "7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee"
REFERENCE_VERSION = "cvc5 1.3.4 [git f3b21c4 on branch HEAD]"
TIMEOUT_MS = 24_000
MEMORY_GB = 8
OUTER_MARGIN_SECONDS = 5
MAX_START_LOAD = 12.0
EXPECTED_COUNTS = {
    "rows": 200,
    "axeyum_solved": 94,
    "reference_solved": 180,
    "both": 94,
    "axeyum_only": 0,
    "reference_only": 86,
    "disagreements": 0,
}
ALLOWED_VERDICTS = {"sat", "unsat", "unknown"}
ALLOWED_REFERENCE_OUTCOMES = ALLOWED_VERDICTS | {"timeout"}
NON_CAUSAL_REASONS = {"unsupported", "not-applicable"}
REPLAY_WORDS = (
    "replay",
    "re-check",
    "verify",
    "verification",
    "original assertion",
    "rejected candidate",
)
MODEL_WORDS = (
    "model",
    "candidate",
    "reconstruct",
    "projection",
    "function table",
    "assignment",
)
ARITHMETIC_WORDS = (
    "arith",
    "lia",
    "simplex",
    "branch-and-bound",
    "gomory",
    "farkas",
    "integer",
)
ARITHMETIC_ROUTES = {
    "uf-arith-online",
    "uf-arithmetic",
    "uf-arith-lazy-overbound",
    "uf-arith-lazy-overbound-pre-lia",
}
WIDE_INTEGER_DETAIL = re.compile(
    r"^integer literal `([0-9]+)` exceeds the modeled `Int` range$"
)
BUDGET_KINDS = {
    "timeout",
    "resource-limit",
    "memory-limit",
    "node-budget",
    "encoding-budget",
}


class CensusError(ValueError):
    """The capture does not satisfy the preregistered A4 contract."""


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_text(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def load_average() -> str:
    try:
        return " ".join(pathlib.Path("/proc/loadavg").read_text().split()[:3])
    except OSError as error:
        raise CensusError(f"cannot read /proc/loadavg: {error}") from error


def one_minute_load() -> float:
    try:
        return float(load_average().split()[0])
    except (ValueError, IndexError) as error:
        raise CensusError("/proc/loadavg has no numeric one-minute load") from error


def require_capture_host() -> None:
    cores = os.cpu_count()
    if cores != 24:
        raise CensusError(f"capture requires the preregistered 24-core host, found {cores}")
    load = one_minute_load()
    if load > MAX_START_LOAD:
        raise CensusError(
            f"one-minute load {load:.2f} exceeds preregistered start ceiling {MAX_START_LOAD:.2f}"
        )


@contextlib.contextmanager
def capture_lock() -> Iterator[None]:
    lock_path = pathlib.Path("/tmp/axeyum-qf-uflia-a4-capture.lock")
    with lock_path.open("a+b") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise CensusError("another QF_UFLIA A4 capture is running") from error
        yield


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


def read_population(
    path: pathlib.Path,
    *,
    expected_sha256: str | None = FROZEN_LIST_SHA256,
    expected_rows: int | None = FROZEN_ROWS,
) -> list[str]:
    if expected_sha256 is not None:
        actual = sha256_file(path)
        if actual != expected_sha256:
            raise CensusError(f"population SHA-256 differs: {actual} != {expected_sha256}")
    entries = [line.strip() for line in path.read_text(encoding="utf-8").splitlines()]
    entries = [entry for entry in entries if entry]
    if expected_rows is not None and len(entries) != expected_rows:
        raise CensusError(f"expected {expected_rows} population rows, got {len(entries)}")
    if not entries:
        raise CensusError("population is empty")
    duplicates = sorted(path for path, count in Counter(entries).items() if count > 1)
    if duplicates:
        raise CensusError(f"population contains duplicate path: {duplicates[0]}")
    missing = [entry for entry in entries if not pathlib.Path(entry).is_file()]
    if missing:
        raise CensusError(f"population path is missing: {missing[0]}")
    return entries


def read_jsonl(path: pathlib.Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
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


def validate_order(records: Sequence[dict[str, Any]], population: Sequence[str], label: str) -> None:
    identities = [record.get("file") for record in records]
    if identities != list(population):
        for index, (expected, actual) in enumerate(
            zip(population, identities, strict=False), start=1
        ):
            if expected != actual:
                raise CensusError(
                    f"{label} identity/order differs at row {index}: {actual!r} != {expected!r}"
                )
        raise CensusError(
            f"{label} row count differs: got {len(records)}, expected {len(population)}"
        )


def validate_trace(trace: object, file: str) -> dict[str, Any]:
    if not isinstance(trace, dict) or trace.get("schema_version") != 1:
        raise CensusError(f"{file}: missing schema-1 route trace")
    attempts = trace.get("attempts")
    if not isinstance(attempts, list) or not attempts:
        raise CensusError(f"{file}: route trace has no attempts")
    for index, attempt in enumerate(attempts, start=1):
        if not isinstance(attempt, dict):
            raise CensusError(f"{file}: trace attempt {index} is not an object")
        if not isinstance(attempt.get("route"), str):
            raise CensusError(f"{file}: trace attempt {index} lacks a route")
        outcome = attempt.get("outcome")
        if outcome not in {"probe", "decided", "declined"}:
            raise CensusError(f"{file}: trace attempt {index} has invalid outcome {outcome!r}")
        if outcome == "decided" and attempt.get("verdict") not in {"sat", "unsat"}:
            raise CensusError(f"{file}: decided trace attempt {index} lacks a verdict")
        if outcome == "declined" and attempt.get("reason") not in {
            "unsupported",
            "not-applicable",
            "budget",
            "incomplete",
            "verifier-rejected",
        }:
            raise CensusError(f"{file}: declined trace attempt {index} lacks a typed reason")
    return trace


def validate_axeyum_records(
    records: Sequence[dict[str, Any]],
    population: Sequence[str],
    *,
    expected_ingest_rows: int = EXPECTED_INGEST_ROWS,
) -> None:
    validate_order(records, population, "Axeyum stream")
    ingest_indexes = []
    for index, record in enumerate(records):
        file = str(record["file"])
        if record.get("status") == "ingest-unsupported":
            expected = {
                "file",
                "status",
                "verdict",
                "route",
                "reason",
                "kind",
                "detail",
            }
            if set(record) != expected:
                raise CensusError(f"{file}: typed ingest record has unexpected fields")
            if (
                record.get("verdict") != "unknown"
                or record.get("route") != "smtlib-ingest"
                or record.get("reason") != "unsupported"
                or record.get("kind") != "wide-integer-literal"
                or not isinstance(record.get("detail"), str)
                or WIDE_INTEGER_DETAIL.fullmatch(record["detail"]) is None
            ):
                raise CensusError(f"{file}: invalid typed wide-integer ingest record")
            ingest_indexes.append(index)
            continue
        if record.get("status") != "decided":
            raise CensusError(
                f"{file}: Axeyum status is neither decided nor typed ingest: "
                f"{record.get('status')!r}"
            )
        if record.get("verdict") not in ALLOWED_VERDICTS:
            raise CensusError(f"{file}: invalid Axeyum verdict {record.get('verdict')!r}")
        validate_trace(record.get("trace"), file)
    expected_indexes = list(range(expected_ingest_rows))
    if ingest_indexes != expected_indexes:
        raise CensusError(
            "typed wide-integer ingest rows differ: "
            f"got {[index + 1 for index in ingest_indexes]}, "
            f"expected rows 1..{expected_ingest_rows}"
        )


def validate_reference_records(
    records: Sequence[dict[str, Any]], population: Sequence[str]
) -> None:
    validate_order(records, population, "reference stream")
    for record in records:
        file = str(record["file"])
        outcome = record.get("outcome")
        if outcome not in ALLOWED_REFERENCE_OUTCOMES:
            raise CensusError(f"{file}: invalid reference outcome {outcome!r}")
        elapsed = record.get("elapsed_ms")
        if not isinstance(elapsed, int) or elapsed < 0:
            raise CensusError(f"{file}: invalid reference elapsed_ms {elapsed!r}")
        exit_code = record.get("exit_code")
        expected_exit = 124 if outcome == "timeout" else 0
        if exit_code != expected_exit:
            raise CensusError(
                f"{file}: {outcome} reference row has exit {exit_code!r}, expected {expected_exit}"
            )


def smtlib_tokens(text: str) -> list[str]:
    """Return tokens outside comments, strings, and quoted symbols."""

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


def declared_status_and_quantifier(path: pathlib.Path) -> tuple[str | None, bool]:
    tokens = smtlib_tokens(path.read_text(encoding="utf-8"))
    declared: str | None = None
    for index, token in enumerate(tokens[:-1]):
        if token == ":status" and tokens[index + 1] in ALLOWED_VERDICTS:
            declared = tokens[index + 1]
            break
    return declared, any(token in {"forall", "exists"} for token in tokens)


def substantive_declines(trace: dict[str, Any]) -> list[dict[str, Any]]:
    result = []
    for attempt in trace["attempts"]:
        if attempt.get("outcome") != "declined":
            continue
        if attempt.get("reason") in NON_CAUSAL_REASONS:
            continue
        result.append(dict(attempt))
    return result


def normalize_detail(detail: str) -> str:
    normalized = detail.lower()
    normalized = re.sub(r"(?:/[^\s,;()]+)+", "<path>", normalized)
    normalized = re.sub(r"\b0x[0-9a-f]+\b", "<hex>", normalized)
    normalized = re.sub(r"\b\d+(?:\.\d+)?\b", "<n>", normalized)
    return " ".join(normalized.split())


def detail_contains(attempts: Sequence[dict[str, Any]], words: Sequence[str]) -> bool:
    details = "\n".join(
        str(attempt.get("detail", "")).lower() for attempt in attempts
    )
    return any(word in details for word in words)


def classify_case(
    trace: dict[str, Any], source_has_quantifier: bool
) -> tuple[str, list[dict[str, Any]]]:
    declines = substantive_declines(trace)
    if not declines:
        raise CensusError("reference-only trace has no substantive decline")
    all_attempts = trace["attempts"]
    terminal = declines[-1]
    if source_has_quantifier or detail_contains(all_attempts, ("quantifier",)):
        return "quantifier-discovery", declines
    if any(attempt.get("reason") == "verifier-rejected" for attempt in declines) or detail_contains(
        declines, REPLAY_WORDS
    ):
        return "replay", declines
    uf_declines = [
        attempt
        for attempt in declines
        if str(attempt.get("route", "")).startswith(("uf", "euf"))
    ]
    if detail_contains(uf_declines, MODEL_WORDS):
        return "uf-model-construction", declines
    if terminal.get("reason") == "budget" or terminal.get("kind") in BUDGET_KINDS:
        return "budget-routing", declines
    terminal_route = str(terminal.get("route", ""))
    if (
        terminal_route in ARITHMETIC_ROUTES
        or terminal_route.startswith(("lia", "int-"))
        or detail_contains([terminal], ARITHMETIC_WORDS)
    ):
        return "arithmetic-participation", declines
    if terminal_route.startswith(("uf", "euf")):
        return "uf-model-construction", declines
    return "unclassified", declines


def lossless_key(case: dict[str, Any]) -> tuple[str, str, str, str, str]:
    terminal = case["terminal_substantive_decline"]
    return (
        case["bucket"],
        str(terminal["route"]),
        str(terminal["reason"]),
        str(terminal.get("kind") or ""),
        case["normalized_detail_family"],
    )


def build_census(cases: Sequence[dict[str, Any]]) -> dict[str, Any]:
    bucket_counts = Counter(case["bucket"] for case in cases)
    unclassified = bucket_counts.get("unclassified", 0)
    if unclassified:
        raise CensusError(f"causal census has {unclassified} unclassified rows")

    groups: dict[tuple[str, str, str, str, str, str], list[dict[str, Any]]] = defaultdict(list)
    for case in cases:
        groups[lossless_key(case) + (case["reference"],)].append(case)
    group_rows = []
    for key, grouped_cases in groups.items():
        bucket, route, reason, kind, detail, reference = key
        files = [case["file"] for case in grouped_cases]
        eligible = all(case.get("selection_eligible", True) for case in grouped_cases)
        ineligible_reasons = sorted(
            {
                str(case["selection_ineligible_reason"])
                for case in grouped_cases
                if not case.get("selection_eligible", True)
            }
        )
        group_rows.append(
            {
                "bucket": bucket,
                "terminal_route": route,
                "reason": reason,
                "kind": kind or None,
                "normalized_detail_family": detail,
                "reference_verdict": reference,
                "count": len(files),
                "files": files,
                "selection_eligible": eligible,
                "selection_ineligible_reasons": ineligible_reasons,
            }
        )
    group_rows.sort(
        key=lambda row: (
            -row["count"],
            row["bucket"],
            row["terminal_route"],
            row["reason"],
            row["kind"] or "",
            row["normalized_detail_family"],
            row["reference_verdict"],
            row["files"],
        )
    )
    return {
        "schema": "axeyum-qf-uflia-a4-causal-census-v1",
        "rows": len(cases),
        "bucket_counts": dict(sorted(bucket_counts.items())),
        "lossless_groups": group_rows,
        "selection_candidates": [
            row for row in group_rows if row["count"] >= 3 and row["selection_eligible"]
        ],
        "cases": list(cases),
    }


def validate_and_derive(
    population: Sequence[str],
    axeyum_records: Sequence[dict[str, Any]],
    reference_records: Sequence[dict[str, Any]],
    *,
    expected_counts: dict[str, int] = EXPECTED_COUNTS,
    expected_ingest_rows: int = EXPECTED_INGEST_ROWS,
) -> tuple[dict[str, int], str, list[str], dict[str, Any]]:
    validate_axeyum_records(
        axeyum_records, population, expected_ingest_rows=expected_ingest_rows
    )
    validate_reference_records(reference_records, population)

    counts = {
        "rows": len(population),
        "axeyum_solved": 0,
        "reference_solved": 0,
        "both": 0,
        "axeyum_only": 0,
        "reference_only": 0,
        "disagreements": 0,
    }
    sidecar = io.StringIO(newline="")
    writer = csv.writer(sidecar, delimiter="\t", lineterminator="\n")
    writer.writerow(["file", "axeyum", "reference", "declared"])
    reference_only_paths: list[str] = []
    causal_cases: list[dict[str, Any]] = []

    for file, axeyum, reference in zip(
        population, axeyum_records, reference_records, strict=True
    ):
        declared, source_has_quantifier = declared_status_and_quantifier(pathlib.Path(file))
        a = str(axeyum["verdict"])
        r = str(reference["outcome"])
        a_solved = a in {"sat", "unsat"}
        r_solved = r in {"sat", "unsat"}
        counts["axeyum_solved"] += int(a_solved)
        counts["reference_solved"] += int(r_solved)
        if a_solved and r_solved:
            counts["both"] += 1
        elif a_solved:
            counts["axeyum_only"] += 1
        elif r_solved:
            counts["reference_only"] += 1
            reference_only_paths.append(file)
        if a_solved and declared in {"sat", "unsat"} and a != declared:
            raise CensusError(f"Axeyum disagreement with declared status for {file}: {a}/{declared}")
        if r_solved and declared in {"sat", "unsat"} and r != declared:
            raise CensusError(f"cvc5 disagreement with declared status for {file}: {r}/{declared}")
        if a_solved and r_solved and a != r:
            raise CensusError(f"Axeyum/cvc5 disagreement for {file}: {a}/{r}")
        writer.writerow(
            [
                file,
                a if a_solved else "unsolved",
                r if r_solved else "unsolved",
                declared or "none",
            ]
        )
        if not a_solved and r_solved:
            if axeyum["status"] == "ingest-unsupported":
                boundary = {
                    "route": "smtlib-ingest",
                    "outcome": "declined",
                    "reason": "unsupported",
                    "kind": "wide-integer-literal",
                    "detail": axeyum["detail"],
                }
                trace = None
                bucket = "arithmetic-participation"
                declines = [boundary]
                selection_eligible = False
                selection_ineligible_reason = "ADR-0376 measured non-cause"
            else:
                trace = validate_trace(axeyum["trace"], file)
                bucket, declines = classify_case(trace, source_has_quantifier)
                selection_eligible = True
                selection_ineligible_reason = None
            terminal = declines[-1]
            causal_cases.append(
                {
                    "file": file,
                    "declared": declared,
                    "axeyum": a,
                    "reference": r,
                    "source_has_quantifier": source_has_quantifier,
                    "first_substantive_decline": declines[0],
                    "terminal_substantive_decline": terminal,
                    "normalized_detail_family": normalize_detail(
                        str(terminal.get("detail", ""))
                    ),
                    "bucket": bucket,
                    "trace": trace,
                    "selection_eligible": selection_eligible,
                    "selection_ineligible_reason": selection_ineligible_reason,
                }
            )

    if counts != expected_counts:
        raise CensusError(f"aggregate mismatch: {counts} != {expected_counts}")
    census = build_census(causal_cases)
    return counts, sidecar.getvalue(), reference_only_paths, census


def git_capture_identity() -> dict[str, Any]:
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    if status:
        raise CensusError("tracked worktree is not clean; commit before capture")
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True
    ).stdout.strip()
    upstream = subprocess.run(
        ["git", "rev-parse", "@{upstream}"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    if commit != upstream:
        raise CensusError(f"capture commit is not pushed exactly: HEAD={commit}, upstream={upstream}")
    return {"git_commit": commit, "git_upstream": upstream, "tracked_tree_clean": True}


def metadata_base(
    command: Sequence[str], binary: pathlib.Path, identity: dict[str, Any]
) -> dict[str, Any]:
    return {
        **identity,
        "command": list(command),
        "binary": str(binary),
        "binary_sha256": sha256_file(binary),
        "binary_bytes": binary.stat().st_size,
        "list": str(FROZEN_LIST.relative_to(ROOT)),
        "list_sha256": sha256_file(FROZEN_LIST),
        "list_rows": FROZEN_ROWS,
        "timeout_ms": TIMEOUT_MS,
        "memory_gb": MEMORY_GB,
        "host_cores": os.cpu_count(),
    }


def write_failure_metadata(
    path: pathlib.Path,
    *,
    schema: str,
    base: dict[str, Any],
    started_utc: str,
    started_monotonic: float,
    load_start: str,
    error: BaseException,
    stdout: bytes,
    stderr: bytes,
    exit_code: int | None,
    emitted_rows: int,
) -> None:
    record = {
        "schema": schema,
        **base,
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "elapsed_ms": round((time.monotonic() - started_monotonic) * 1000),
        "load_start": load_start,
        "load_end": load_average(),
        "exit_code": exit_code,
        "emitted_rows": emitted_rows,
        "first_validator_error": str(error),
        "stdout_sha256": sha256_bytes(stdout),
        "stdout_bytes": len(stdout),
        "stderr_sha256": sha256_bytes(stderr),
        "stderr_bytes": len(stderr),
        "credited": False,
    }
    atomic_write_text(path, json_text(record))


def capture_axeyum(
    binary: pathlib.Path,
    output: pathlib.Path,
    metadata_path: pathlib.Path,
    failure_metadata_path: pathlib.Path,
) -> None:
    population = read_population(FROZEN_LIST)
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise CensusError(f"Axeyum capture binary is not executable: {binary}")
    timeout_bin = shutil.which("timeout")
    if timeout_bin is None:
        raise CensusError("GNU timeout is required")
    command = [
        timeout_bin,
        "--signal=TERM",
        "--kill-after=5s",
        "6000",
        "env",
        f"MEM_LIMIT_GB={MEMORY_GB}",
        str(ROOT / "scripts/mem-run.sh"),
        str(binary),
        "--list",
        str(FROZEN_LIST),
        str(TIMEOUT_MS),
        "--json",
    ]
    identity = git_capture_identity()
    base = metadata_base(command, binary, identity)
    require_capture_host()
    started_utc = utc_now()
    load_start = load_average()
    started = time.monotonic()
    with capture_lock(), tempfile.TemporaryDirectory(prefix="axeyum-uflia-a4-") as temporary:
        stdout_path = pathlib.Path(temporary) / "stdout.jsonl"
        stderr_path = pathlib.Path(temporary) / "stderr.bin"
        result: subprocess.CompletedProcess[bytes] | None = None
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                result = subprocess.run(
                    command,
                    cwd=ROOT,
                    stdout=stdout,
                    stderr=stderr,
                    timeout=6010,
                    check=False,
                )
            if result.returncode != 0:
                raise CensusError(f"Axeyum capture exited {result.returncode}")
            records = read_jsonl(stdout_path)
            validate_axeyum_records(records, population)
            raw = stdout_path.read_bytes()
            stderr_raw = stderr_path.read_bytes()
        except (CensusError, OSError, subprocess.SubprocessError) as error:
            failure_stdout = stdout_path.read_bytes() if stdout_path.is_file() else b""
            failure_stderr = stderr_path.read_bytes() if stderr_path.is_file() else b""
            write_failure_metadata(
                failure_metadata_path,
                schema="axeyum-qf-uflia-a4-axeyum-failure-v2",
                base=base,
                started_utc=started_utc,
                started_monotonic=started,
                load_start=load_start,
                error=error,
                stdout=failure_stdout,
                stderr=failure_stderr,
                exit_code=None if result is None else result.returncode,
                emitted_rows=failure_stdout.count(b"\n"),
            )
            raise
    metadata = {
        "schema": "axeyum-qf-uflia-a4-axeyum-capture-v2",
        **base,
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "elapsed_ms": round((time.monotonic() - started) * 1000),
        "load_start": load_start,
        "load_end": load_average(),
        "records": len(records),
        "ingest_unsupported_records": sum(
            record["status"] == "ingest-unsupported" for record in records
        ),
        "stdout_sha256": sha256_bytes(raw),
        "stdout_bytes": len(raw),
        "stderr_sha256": sha256_bytes(stderr_raw),
        "stderr_bytes": len(stderr_raw),
    }
    atomic_write_bytes(output, raw)
    atomic_write_text(metadata_path, json_text(metadata))
    failure_metadata_path.unlink(missing_ok=True)


def parse_reference_result(returncode: int, stdout: bytes, stderr: bytes) -> str:
    verdicts = [
        line.strip()
        for line in stdout.decode("utf-8", errors="replace").splitlines()
        if line.strip() in ALLOWED_VERDICTS
    ]
    if returncode == 124:
        if verdicts:
            raise CensusError("timed-out cvc5 process emitted a verdict")
        return "timeout"
    if returncode != 0:
        detail = stderr.decode("utf-8", errors="replace").strip()[:200]
        raise CensusError(f"cvc5 operational failure exit={returncode}: {detail}")
    if len(verdicts) != 1:
        raise CensusError(f"cvc5 emitted {len(verdicts)} standalone verdicts")
    return verdicts[0]


def reference_base_command(binary: pathlib.Path, timeout_bin: str) -> list[str]:
    """Build the frozen cvc5 invocation; per-query limits exit cleanly on timeout."""
    return [
        timeout_bin,
        "--signal=TERM",
        "--kill-after=1s",
        str(TIMEOUT_MS // 1000 + OUTER_MARGIN_SECONDS),
        "env",
        f"MEM_LIMIT_GB={MEMORY_GB}",
        str(ROOT / "scripts/mem-run.sh"),
        str(binary),
        f"--tlimit-per={TIMEOUT_MS}",
    ]


def capture_reference(
    binary: pathlib.Path,
    output: pathlib.Path,
    metadata_path: pathlib.Path,
    failure_metadata_path: pathlib.Path,
) -> None:
    population = read_population(FROZEN_LIST)
    if sha256_file(binary) != REFERENCE_SHA256:
        raise CensusError("cvc5 binary SHA-256 differs from preregistration")
    version = subprocess.run(
        [str(binary), "--version"], check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    ).stdout.decode("utf-8", errors="replace").splitlines()[0]
    if version != REFERENCE_VERSION:
        raise CensusError(f"cvc5 version differs: {version!r}")
    timeout_bin = shutil.which("timeout")
    if timeout_bin is None:
        raise CensusError("GNU timeout is required")
    base_command = reference_base_command(binary, timeout_bin)
    identity = git_capture_identity()
    command_template = [*base_command, "FILE"]
    base = metadata_base(command_template, binary, identity)
    require_capture_host()
    started_utc = utc_now()
    load_start = load_average()
    started = time.monotonic()
    records = []
    last_stderr = b""
    last_exit_code: int | None = None
    try:
        with capture_lock():
            for index, file in enumerate(population, start=1):
                command = [*base_command, file]
                row_started = time.monotonic()
                result = subprocess.run(
                    command,
                    cwd=ROOT,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=TIMEOUT_MS / 1000 + OUTER_MARGIN_SECONDS + 3,
                    check=False,
                )
                last_stderr = result.stderr
                last_exit_code = result.returncode
                elapsed_ms = round((time.monotonic() - row_started) * 1000)
                outcome = parse_reference_result(result.returncode, result.stdout, result.stderr)
                records.append(
                    {
                        "file": file,
                        "outcome": outcome,
                        "elapsed_ms": elapsed_ms,
                        "exit_code": result.returncode,
                        "stdout_sha256": sha256_bytes(result.stdout),
                        "stderr_sha256": sha256_bytes(result.stderr),
                        "stdout_bytes": len(result.stdout),
                        "stderr_bytes": len(result.stderr),
                    }
                )
                print(
                    f"reference {index}/{len(population)} {outcome} {elapsed_ms}ms",
                    file=sys.stderr,
                )
        validate_reference_records(records, population)
    except (CensusError, OSError, subprocess.SubprocessError) as error:
        partial = "".join(
            json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
            for row in records
        ).encode("utf-8")
        write_failure_metadata(
            failure_metadata_path,
            schema="axeyum-qf-uflia-a4-reference-failure-v2",
            base=base,
            started_utc=started_utc,
            started_monotonic=started,
            load_start=load_start,
            error=error,
            stdout=partial,
            stderr=last_stderr,
            exit_code=last_exit_code,
            emitted_rows=len(records),
        )
        raise
    raw = "".join(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in records)
    metadata = {
        "schema": "axeyum-qf-uflia-a4-reference-capture-v2",
        **base,
        "reference_version": version,
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "elapsed_ms": round((time.monotonic() - started) * 1000),
        "load_start": load_start,
        "load_end": load_average(),
        "records": len(records),
        "outcome_counts": dict(sorted(Counter(row["outcome"] for row in records).items())),
        "stdout_sha256": sha256_bytes(raw.encode("utf-8")),
        "stdout_bytes": len(raw.encode("utf-8")),
    }
    atomic_write_text(output, raw)
    atomic_write_text(metadata_path, json_text(metadata))
    failure_metadata_path.unlink(missing_ok=True)


def validate_metadata(
    path: pathlib.Path, expected_schema: str, raw_path: pathlib.Path
) -> dict[str, Any]:
    metadata = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(metadata, dict) or metadata.get("schema") != expected_schema:
        raise CensusError(f"invalid capture metadata schema: {path}")
    if metadata.get("list_sha256") != FROZEN_LIST_SHA256 or metadata.get("list_rows") != FROZEN_ROWS:
        raise CensusError(f"capture metadata population drift: {path}")
    if metadata.get("timeout_ms") != TIMEOUT_MS or metadata.get("memory_gb") != MEMORY_GB:
        raise CensusError(f"capture metadata budget drift: {path}")
    if metadata.get("stdout_sha256") != sha256_file(raw_path):
        raise CensusError(f"capture metadata/raw hash mismatch: {path}")
    if metadata.get("git_commit") != metadata.get("git_upstream"):
        raise CensusError(f"capture metadata is not from an exactly pushed commit: {path}")
    return metadata


def retain_capture(
    axeyum_path: pathlib.Path,
    axeyum_metadata_path: pathlib.Path,
    reference_path: pathlib.Path,
    reference_metadata_path: pathlib.Path,
    sidecar_path: pathlib.Path,
    evidence_dir: pathlib.Path,
) -> dict[str, Any]:
    population = read_population(FROZEN_LIST)
    axeyum_records = read_jsonl(axeyum_path)
    reference_records = read_jsonl(reference_path)
    axeyum_metadata = validate_metadata(
        axeyum_metadata_path, "axeyum-qf-uflia-a4-axeyum-capture-v2", axeyum_path
    )
    reference_metadata = validate_metadata(
        reference_metadata_path,
        "axeyum-qf-uflia-a4-reference-capture-v2",
        reference_path,
    )
    if axeyum_metadata["git_commit"] != reference_metadata["git_commit"]:
        raise CensusError("Axeyum and reference streams were not captured at the same commit")
    counts, sidecar, residual, census = validate_and_derive(
        population, axeyum_records, reference_records
    )

    evidence_dir.mkdir(parents=True, exist_ok=True)
    retained_axeyum = evidence_dir / "axeyum-traces-v1.jsonl"
    retained_reference = evidence_dir / "reference-outcomes-v1.jsonl"
    residual_path = evidence_dir / "reference-only-v1.txt"
    census_path = evidence_dir / "causal-census-v1.json"
    manifest_path = evidence_dir / "capture-manifest-v1.json"

    atomic_write_bytes(retained_axeyum, axeyum_path.read_bytes())
    atomic_write_bytes(retained_reference, reference_path.read_bytes())
    atomic_write_text(sidecar_path, sidecar)
    atomic_write_text(residual_path, "".join(f"{file}\n" for file in residual))
    atomic_write_text(census_path, json_text(census))
    artifact_paths = [
        retained_axeyum,
        retained_reference,
        sidecar_path,
        residual_path,
        census_path,
    ]
    manifest = {
        "schema": "axeyum-qf-uflia-a4-capture-manifest-v2",
        "population": {
            "path": str(FROZEN_LIST.relative_to(ROOT)),
            "sha256": FROZEN_LIST_SHA256,
            "rows": FROZEN_ROWS,
        },
        "counts": counts,
        "axeyum_capture": axeyum_metadata,
        "reference_capture": reference_metadata,
        "artifacts": {
            str(path.relative_to(ROOT)): {"sha256": sha256_file(path), "bytes": path.stat().st_size}
            for path in artifact_paths
        },
    }
    atomic_write_text(manifest_path, json_text(manifest))
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    axeyum = subparsers.add_parser("capture-axeyum")
    axeyum.add_argument("--binary", type=pathlib.Path, required=True)
    axeyum.add_argument("--output", type=pathlib.Path, required=True)
    axeyum.add_argument("--metadata", type=pathlib.Path, required=True)
    axeyum.add_argument("--failure-metadata", type=pathlib.Path, required=True)

    reference = subparsers.add_parser("capture-reference")
    reference.add_argument("--binary", type=pathlib.Path, default=REFERENCE_BINARY)
    reference.add_argument("--output", type=pathlib.Path, required=True)
    reference.add_argument("--metadata", type=pathlib.Path, required=True)
    reference.add_argument("--failure-metadata", type=pathlib.Path, required=True)

    validate = subparsers.add_parser("validate")
    validate.add_argument("--axeyum", type=pathlib.Path, required=True)
    validate.add_argument("--axeyum-metadata", type=pathlib.Path, required=True)
    validate.add_argument("--reference", type=pathlib.Path, required=True)
    validate.add_argument("--reference-metadata", type=pathlib.Path, required=True)
    validate.add_argument(
        "--sidecar",
        type=pathlib.Path,
        default=ROOT / "bench-results/parity-details/QF_UFLIA.tsv",
    )
    validate.add_argument(
        "--evidence-dir",
        type=pathlib.Path,
        default=ROOT / "docs/plan/evidence/qf-uflia-a4",
    )

    args = parser.parse_args()
    try:
        if args.command == "capture-axeyum":
            capture_axeyum(
                args.binary.resolve(), args.output, args.metadata, args.failure_metadata
            )
        elif args.command == "capture-reference":
            capture_reference(
                args.binary.resolve(), args.output, args.metadata, args.failure_metadata
            )
        else:
            manifest = retain_capture(
                args.axeyum,
                args.axeyum_metadata,
                args.reference,
                args.reference_metadata,
                args.sidecar,
                args.evidence_dir,
            )
            print(json.dumps(manifest["counts"], sort_keys=True))
        return 0
    except (CensusError, OSError, subprocess.SubprocessError, json.JSONDecodeError) as error:
        print(f"qf-uflia-a4-census: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
