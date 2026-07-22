"""Independent contracts for an official SMT-COMP selection artifact.

This module deliberately does not generate the pseudorandom sample. The pinned
organizer implementation owns that output; these standard-library routines
reconstruct eligibility and prove that an externally supplied selection has the
required per-logic shape.
"""

from __future__ import annotations

import hashlib
import json
import math
import stat
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence


SCHEMA = "axeyum-smtcomp-official-selection-v1"
TERMINAL_REASONS = frozenset(
    {
        "selected-new",
        "selected-old",
        "excluded-explicit-removal",
        "excluded-noncompetitive-logic",
        "excluded-trivial",
        "excluded-cap-new",
        "excluded-cap-old",
    }
)
RESULTS = frozenset({"sat", "unsat", "unknown"})
STATUSES = frozenset({"sat", "unsat", "unknown"})


class SelectionAuditError(ValueError):
    """An input or output violates the independent selection contract."""


@dataclass(frozen=True)
class HistoricalYear:
    """Audited historical facts for one benchmark in one year."""

    competitive: bool
    coherent: bool
    result: str
    row_count: int
    trivial: bool
    year: int


def canonical_json_bytes(value: Any) -> bytes:
    """Return canonical UTF-8 JSON with one final LF."""
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    """Return the lowercase SHA-256 digest of exact bytes."""
    return hashlib.sha256(data).hexdigest()


def division_cap(
    count: int,
    *,
    minimum: int = 300,
    ratio: float = 0.5,
    large_threshold: int = 1000,
    large_ratio: float = 0.1,
) -> int:
    """Reproduce the pinned organizer's per-logic sample-size expression."""
    if isinstance(count, bool) or not isinstance(count, int) or count < 0:
        raise SelectionAuditError("logic population must be a nonnegative integer")
    proportional = (
        math.floor(count * ratio)
        if count <= large_threshold
        else math.floor(large_threshold * ratio + (count - large_threshold) * large_ratio)
    )
    return min(count, max(minimum, proportional))


def normalize_benchmark(row: Mapping[str, Any]) -> dict[str, Any]:
    """Validate metadata and derive its absolute-path-free benchmark ID."""
    expected = {"logic", "family", "name", "status", "asserts"}
    if set(row) != expected:
        raise SelectionAuditError(f"benchmark fields differ: {sorted(set(row) ^ expected)}")
    logic = _component(row["logic"], "logic")
    name = _component(row["name"], "name")
    family_value = row["family"]
    if not isinstance(family_value, list) or not family_value:
        raise SelectionAuditError("family must be a nonempty list")
    family = [_component(value, "family") for value in family_value]
    status = row["status"]
    if status not in STATUSES:
        raise SelectionAuditError(f"unsupported benchmark status: {status!r}")
    asserts = row["asserts"]
    if isinstance(asserts, bool) or not isinstance(asserts, int) or asserts < 0:
        raise SelectionAuditError("assert count must be a nonnegative integer")
    benchmark_id = str(PurePosixPath("non-incremental", logic, *family, name))
    return {
        "asserts": asserts,
        "benchmark_id": benchmark_id,
        "family": family,
        "logic": logic,
        "name": name,
        "status": status,
    }


def competitive_logics(submissions: Sequence[Mapping[str, Any]]) -> set[str]:
    """Expand competitive participation rows exactly as the organizer does."""
    counts: dict[str, int] = defaultdict(int)
    for submission in submissions:
        if set(submission) != {"name", "competitive", "seed", "participations"}:
            raise SelectionAuditError("submission fields differ")
        if not isinstance(submission["competitive"], bool):
            raise SelectionAuditError("submission competitive flag is not Boolean")
        if not submission["competitive"]:
            continue
        seed = submission["seed"]
        if isinstance(seed, bool) or not isinstance(seed, int):
            raise SelectionAuditError("competitive submission seed is missing or non-integer")
        participations = submission["participations"]
        if not isinstance(participations, list):
            raise SelectionAuditError("participations must be a list")
        for participation in participations:
            if set(participation) != {"track", "logics"}:
                raise SelectionAuditError("participation fields differ")
            if participation["track"] != "single-query":
                continue
            logics = participation["logics"]
            if not isinstance(logics, list) or not logics:
                raise SelectionAuditError("participation logics must be a nonempty list")
            for logic in logics:
                counts[_component(logic, "logic")] += 1
    return {logic for logic, count in counts.items() if count > 1}


def historical_facts(
    rows: Sequence[Mapping[str, Any]],
    known_ids: set[str],
    *,
    first_year: int = 2018,
    last_year: int = 2024,
    threshold: float = 1.0,
) -> dict[str, dict[str, Any]]:
    """Reconstruct the pinned old-criteria=false difficulty reduction."""
    grouped: dict[str, dict[int, list[Mapping[str, Any]]]] = defaultdict(lambda: defaultdict(list))
    for row in rows:
        if set(row) != {"benchmark_id", "year", "solver", "result", "cpu_seconds"}:
            raise SelectionAuditError("historical-result fields differ")
        benchmark_id = row["benchmark_id"]
        if benchmark_id not in known_ids:
            # The organizer drops results for benchmarks absent from current metadata.
            continue
        year = row["year"]
        if isinstance(year, bool) or not isinstance(year, int) or not first_year <= year <= last_year:
            raise SelectionAuditError("historical result year is outside the frozen range")
        _component(row["solver"], "solver")
        if row["result"] not in RESULTS:
            raise SelectionAuditError("unsupported historical result")
        seconds = row["cpu_seconds"]
        if isinstance(seconds, bool) or not isinstance(seconds, (int, float)) or seconds < 0:
            raise SelectionAuditError("historical CPU time must be nonnegative")
        grouped[benchmark_id][year].append(row)

    output: dict[str, dict[str, Any]] = {}
    for benchmark_id in sorted(known_ids):
        years = grouped.get(benchmark_id, {})
        all_rows = [row for rows_in_year in years.values() for row in rows_in_year]
        has_sat = any(row["result"] == "sat" for row in all_rows)
        has_unsat = any(row["result"] == "unsat" for row in all_rows)
        file_coherent = not (has_sat and has_unsat)
        year_facts: list[HistoricalYear] = []
        for year in sorted(years):
            year_rows = years[year]
            competitive = file_coherent and len(year_rows) > 1
            trivial = competitive and all(
                row["result"] != "unknown" and float(row["cpu_seconds"]) <= threshold
                for row in year_rows
            )
            sat_count = sum(row["result"] == "sat" for row in year_rows) if competitive else 0
            unsat_count = sum(row["result"] == "unsat" for row in year_rows) if competitive else 0
            result = "sat" if sat_count >= 2 else "unsat" if unsat_count >= 2 else "unknown"
            year_facts.append(
                HistoricalYear(
                    competitive=competitive,
                    coherent=file_coherent,
                    result=result,
                    row_count=len(year_rows),
                    trivial=trivial,
                    year=year,
                )
            )
        admitted = [fact for fact in year_facts if fact.competitive]
        output[benchmark_id] = {
            "file_coherent": file_coherent,
            "run": bool(admitted),
            "trivial": bool(admitted) and all(fact.trivial for fact in admitted),
            "years": [
                {
                    "competitive": fact.competitive,
                    "coherent": fact.coherent,
                    "result": fact.result,
                    "row_count": fact.row_count,
                    "trivial": fact.trivial,
                    "year": fact.year,
                }
                for fact in year_facts
            ],
        }
    return output


def audit_selection(
    benchmarks: Sequence[Mapping[str, Any]],
    submissions: Sequence[Mapping[str, Any]],
    historical_results: Sequence[Mapping[str, Any]],
    removed_ids: Iterable[str],
    selected_ids: Sequence[str],
    *,
    new_family_prefix: str = "2025",
) -> dict[str, Any]:
    """Audit eligibility, quotas, and the complete terminal decision partition."""
    normalized = [normalize_benchmark(row) for row in benchmarks]
    by_id = {row["benchmark_id"]: row for row in normalized}
    if len(by_id) != len(normalized):
        raise SelectionAuditError("duplicate benchmark ID")
    removed = set(removed_ids)
    if not removed <= set(by_id):
        raise SelectionAuditError("explicit removal names an unknown benchmark")
    if len(selected_ids) != len(set(selected_ids)):
        raise SelectionAuditError("official selected list contains a duplicate")
    selected = set(selected_ids)
    if not selected <= set(by_id):
        raise SelectionAuditError("official selected list contains an unknown benchmark")

    competitive = competitive_logics(submissions)
    history = historical_facts(historical_results, set(by_id))
    intermediate: dict[str, dict[str, Any]] = {}
    eligible_by_logic: dict[str, list[str]] = defaultdict(list)
    for benchmark_id, row in by_id.items():
        is_removed = benchmark_id in removed
        is_competitive = row["logic"] in competitive
        is_trivial = history[benchmark_id]["trivial"]
        is_new = row["family"][0].startswith(new_family_prefix)
        eligible = not is_removed and is_competitive and not is_trivial
        intermediate[benchmark_id] = {
            "eligible": eligible,
            "explicit_removal": is_removed,
            "historical": history[benchmark_id],
            "is_new": is_new,
            "logic_competitive": is_competitive,
        }
        if eligible:
            eligible_by_logic[row["logic"]].append(benchmark_id)

    summaries = []
    for logic in sorted(eligible_by_logic):
        ids = eligible_by_logic[logic]
        new_ids = [benchmark_id for benchmark_id in ids if intermediate[benchmark_id]["is_new"]]
        old_ids = [benchmark_id for benchmark_id in ids if not intermediate[benchmark_id]["is_new"]]
        cap = division_cap(len(ids))
        selected_new = min(cap, len(new_ids))
        selected_old = cap - selected_new
        actual_new = sum(benchmark_id in selected for benchmark_id in new_ids)
        actual_old = sum(benchmark_id in selected for benchmark_id in old_ids)
        if actual_new != selected_new or actual_old != selected_old:
            raise SelectionAuditError(
                f"official selection quota mismatch for {logic}: "
                f"new {actual_new}/{selected_new}, old {actual_old}/{selected_old}"
            )
        summaries.append(
            {
                "cap": cap,
                "eligible": len(ids),
                "eligible_new": len(new_ids),
                "eligible_old": len(old_ids),
                "logic": logic,
                "selected_new": actual_new,
                "selected_old": actual_old,
            }
        )

    for benchmark_id in selected:
        if not intermediate[benchmark_id]["eligible"]:
            raise SelectionAuditError(f"ineligible benchmark selected: {benchmark_id}")

    decisions = []
    for benchmark_id in sorted(by_id):
        row = by_id[benchmark_id]
        facts = intermediate[benchmark_id]
        if benchmark_id in selected:
            reason = "selected-new" if facts["is_new"] else "selected-old"
        elif facts["explicit_removal"]:
            reason = "excluded-explicit-removal"
        elif not facts["logic_competitive"]:
            reason = "excluded-noncompetitive-logic"
        elif facts["historical"]["trivial"]:
            reason = "excluded-trivial"
        else:
            reason = "excluded-cap-new" if facts["is_new"] else "excluded-cap-old"
        decisions.append({**row, **facts, "reason": reason, "selected": benchmark_id in selected})

    validate_decisions(decisions, expected_ids=set(by_id), selected_ids=selected)
    return {
        "competitive_logics": sorted(competitive),
        "decisions": decisions,
        "schema": SCHEMA,
        "selection_sha256": sha256_bytes(
            ("".join(f"{benchmark_id}\n" for benchmark_id in sorted(selected))).encode("utf-8")
        ),
        "summaries": summaries,
    }


def audit_corpus(
    corpus_root: Path,
    file_rows: Sequence[Mapping[str, Any]],
    *,
    expected_ids: set[str],
) -> dict[str, Any]:
    """Check an exact regular-file corpus/metadata bijection and byte ledger."""
    root = corpus_root.resolve(strict=True)
    rows = list(file_rows)
    ids = [row.get("benchmark_id") for row in rows]
    if rows != sorted(rows, key=lambda row: row.get("benchmark_id", "")):
        raise SelectionAuditError("corpus ledger is not sorted")
    if len(ids) != len(set(ids)):
        raise SelectionAuditError("corpus ledger contains a duplicate")
    if set(ids) != expected_ids:
        raise SelectionAuditError("corpus ledger is not a complete metadata partition")

    canonical_rows = []
    for row in rows:
        if set(row) != {"benchmark_id", "bytes", "sha256"}:
            raise SelectionAuditError("corpus-ledger fields differ")
        benchmark_id = row["benchmark_id"]
        path = PurePosixPath(benchmark_id)
        if path.is_absolute() or not path.parts or path.parts[0] != "non-incremental":
            raise SelectionAuditError("corpus benchmark ID has the wrong root")
        if any(part in {"", ".", ".."} or "\\" in part for part in path.parts):
            raise SelectionAuditError("corpus benchmark ID contains traversal")
        candidate = root.joinpath(*path.parts)
        try:
            mode = candidate.lstat().st_mode
        except FileNotFoundError as error:
            raise SelectionAuditError(f"missing corpus file: {benchmark_id}") from error
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise SelectionAuditError(f"corpus entry is not a regular file: {benchmark_id}")
        try:
            candidate.resolve(strict=True).relative_to(root)
        except ValueError as error:
            raise SelectionAuditError(f"corpus path escapes root: {benchmark_id}") from error
        data = candidate.read_bytes()
        if isinstance(row["bytes"], bool) or row["bytes"] != len(data):
            raise SelectionAuditError(f"corpus byte count drift: {benchmark_id}")
        digest = sha256_bytes(data)
        if row["sha256"] != digest:
            raise SelectionAuditError(f"corpus hash drift: {benchmark_id}")
        canonical_rows.append(dict(row))

    actual_ids = set()
    scan_root = root / "non-incremental"
    if not scan_root.is_dir():
        raise SelectionAuditError("non-incremental corpus root is missing")
    for candidate in scan_root.rglob("*"):
        mode = candidate.lstat().st_mode
        if stat.S_ISDIR(mode):
            continue
        benchmark_id = candidate.relative_to(root).as_posix()
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise SelectionAuditError(f"corpus scan found a non-regular entry: {benchmark_id}")
        actual_ids.add(benchmark_id)
    if actual_ids != expected_ids:
        missing = sorted(expected_ids - actual_ids)
        extra = sorted(actual_ids - expected_ids)
        raise SelectionAuditError(f"corpus/metadata mismatch: missing={missing}, extra={extra}")
    ledger_bytes = b"".join(canonical_json_bytes(row) for row in canonical_rows)
    return {"files": len(rows), "ledger_sha256": sha256_bytes(ledger_bytes)}


def validate_decisions(
    decisions: Sequence[Mapping[str, Any]],
    *,
    expected_ids: set[str],
    selected_ids: set[str],
) -> None:
    """Require one terminal, internally consistent decision per metadata row."""
    decision_ids = [row.get("benchmark_id") for row in decisions]
    if len(decision_ids) != len(set(decision_ids)):
        raise SelectionAuditError("decision ledger contains a duplicate")
    if set(decision_ids) != expected_ids:
        raise SelectionAuditError("decision ledger is not a complete metadata partition")
    for row in decisions:
        reason = row.get("reason")
        if reason not in TERMINAL_REASONS:
            raise SelectionAuditError("decision ledger has a missing or unknown reason")
        selected = row.get("selected")
        if not isinstance(selected, bool):
            raise SelectionAuditError("decision selected flag is not Boolean")
        if selected != (row["benchmark_id"] in selected_ids):
            raise SelectionAuditError("decision selected flag disagrees with official output")
        if selected != reason.startswith("selected-"):
            raise SelectionAuditError("decision reason disagrees with selected flag")


def _component(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value or value in {".", ".."}:
        raise SelectionAuditError(f"invalid {label} component")
    if "/" in value or "\\" in value or "\x00" in value:
        raise SelectionAuditError(f"path separator in {label} component")
    return value
