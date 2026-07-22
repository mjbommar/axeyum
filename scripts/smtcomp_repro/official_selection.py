"""Independent contracts for an official SMT-COMP selection artifact.

This module deliberately does not generate the pseudorandom sample. The pinned
organizer implementation owns that output; these standard-library routines
reconstruct eligibility and prove that an externally supplied selection has the
required per-logic shape.
"""

from __future__ import annotations

import ast
import gzip
import hashlib
import json
import math
import re
import stat
from collections import defaultdict
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
RESULTS = frozenset(
    {
        "IncrementalError",
        "ModelNotValidated",
        "ModelParsingError",
        "ModelPartialFunctionMissing",
        "ModelUnsat",
        "ModelValidatorBenchmarkStrictTyping",
        "ModelValidatorException",
        "ModelValidatorTimeout",
        "OutOfMemory",
        "Timeout",
        "UnsatCoreNotValidated",
        "incremental",
        "sat",
        "unknown",
        "unsat",
    }
)
STATUSES = frozenset({"sat", "unsat", "unknown"})


class SelectionAuditError(ValueError):
    """An input or output violates the independent selection contract."""


class HistoricalAccumulator:
    """Bounded-memory reduction of normalized historical result rows."""

    def __init__(
        self,
        known_ids: set[str],
        *,
        first_year: int = 2018,
        last_year: int = 2024,
        threshold: float = 1.0,
    ) -> None:
        self.known_ids = known_ids
        self.first_year = first_year
        self.last_year = last_year
        self.threshold = threshold
        self.ignored_rows = 0
        self.rows = 0
        self._files: dict[str, list[Any]] = {}

    def add(self, row: Mapping[str, Any]) -> None:
        """Validate and add one normalized historical row."""
        if set(row) != {"benchmark_id", "year", "solver", "result", "cpu_seconds"}:
            raise SelectionAuditError("historical-result fields differ")
        benchmark_id = row["benchmark_id"]
        year = row["year"]
        if (
            isinstance(year, bool)
            or not isinstance(year, int)
            or not self.first_year <= year <= self.last_year
        ):
            raise SelectionAuditError("historical result year is outside the frozen range")
        _component(row["solver"], "solver")
        result = row["result"]
        if result not in RESULTS:
            raise SelectionAuditError("unsupported historical result")
        seconds = row["cpu_seconds"]
        if isinstance(seconds, bool) or not isinstance(seconds, (int, float)) or seconds < 0:
            raise SelectionAuditError("historical CPU time must be nonnegative")
        self.rows += 1
        if benchmark_id not in self.known_ids:
            self.ignored_rows += 1
            return
        state = self._files.setdefault(benchmark_id, [False, False, {}])
        state[0] = state[0] or result == "sat"
        state[1] = state[1] or result == "unsat"
        year_state = state[2].setdefault(year, [0, True, 0, 0])
        year_state[0] += 1
        year_state[1] = year_state[1] and result != "unknown" and float(seconds) <= self.threshold
        year_state[2] += result == "sat"
        year_state[3] += result == "unsat"

    def facts_for(self, benchmark_id: str) -> dict[str, Any]:
        """Return final old-criteria=false facts for one known benchmark."""
        if benchmark_id not in self.known_ids:
            raise SelectionAuditError("historical facts requested for unknown benchmark")
        state = self._files.get(benchmark_id, [False, False, {}])
        file_coherent = not (state[0] and state[1])
        year_facts = []
        for year in sorted(state[2]):
            row_count, all_non_unknown_within_threshold, sat_count, unsat_count = state[2][year]
            competitive = file_coherent and row_count > 1
            result = (
                "sat"
                if competitive and sat_count >= 2
                else "unsat"
                if competitive and unsat_count >= 2
                else "unknown"
            )
            year_facts.append(
                {
                    "competitive": competitive,
                    "coherent": file_coherent,
                    "result": result,
                    "row_count": row_count,
                    "trivial": competitive and all_non_unknown_within_threshold,
                    "year": year,
                }
            )
        admitted = [fact for fact in year_facts if fact["competitive"]]
        return {
            "file_coherent": file_coherent,
            "run": bool(admitted),
            "trivial": bool(admitted) and all(fact["trivial"] for fact in admitted),
            "years": year_facts,
        }

    def facts(self) -> dict[str, dict[str, Any]]:
        """Return facts for every known benchmark in stable ID order."""
        return {benchmark_id: self.facts_for(benchmark_id) for benchmark_id in sorted(self.known_ids)}


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


def adapt_official_benchmarks(compressed: bytes) -> list[dict[str, Any]]:
    """Decode the pinned organizer benchmark JSON into normalized SQ rows."""
    document = _gzip_json(compressed, "benchmark metadata")
    if set(document) != {"incremental", "non_incremental"}:
        raise SelectionAuditError("official benchmark top-level fields differ")
    if not isinstance(document["incremental"], list) or not isinstance(
        document["non_incremental"], list
    ):
        raise SelectionAuditError("official benchmark populations must be lists")
    normalized = []
    ids = []
    for row in document["non_incremental"]:
        adapted = adapt_official_benchmark_row(row)
        ids.append(normalize_benchmark(adapted)["benchmark_id"])
        normalized.append(adapted)
    if len(ids) != len(set(ids)):
        raise SelectionAuditError("official benchmark metadata contains a duplicate")
    return normalized


def adapt_official_benchmark_row(row: Any) -> dict[str, Any]:
    """Normalize one object from official ``non_incremental`` metadata."""
    if not isinstance(row, dict) or set(row) != {"file", "status", "asserts"}:
        raise SelectionAuditError("official non-incremental benchmark fields differ")
    file_row = _official_file(row["file"], incremental=False)
    adapted = {
        "asserts": row["asserts"],
        "family": file_row["family"],
        "logic": file_row["logic"],
        "name": file_row["name"],
        "status": row["status"],
    }
    normalize_benchmark(adapted)
    return adapted


def adapt_official_results(compressed: bytes, *, year: int) -> list[dict[str, Any]]:
    """Decode one official historical Single Query result file."""
    if isinstance(year, bool) or not isinstance(year, int) or not 2018 <= year <= 2024:
        raise SelectionAuditError("official historical year is outside 2018-2024")
    document = _gzip_json(compressed, f"historical results {year}")
    if set(document) != {"results"} or not isinstance(document["results"], list):
        raise SelectionAuditError("official result top-level fields differ")
    required = {"track", "solver", "file", "result", "cpu_time", "wallclock_time", "memory_usage"}
    allowed = required | {"nb_answers"}
    normalized = []
    for row in document["results"]:
        normalized.append(adapt_official_result_row(row, year=year))
    return normalized


def adapt_official_result_row(row: Any, *, year: int) -> dict[str, Any]:
    """Normalize one object from an official historical SQ result file."""
    if isinstance(year, bool) or not isinstance(year, int) or not 2018 <= year <= 2024:
        raise SelectionAuditError("official historical year is outside 2018-2024")
    required = {"track", "solver", "file", "result", "cpu_time", "wallclock_time", "memory_usage"}
    allowed = required | {"nb_answers"}
    if not isinstance(row, dict) or not required <= set(row) or not set(row) <= allowed:
        raise SelectionAuditError("official historical-result fields differ")
    if row["track"] != "SingleQuery":
        raise SelectionAuditError("non-SingleQuery row in historical SQ input")
    file_row = _official_file(row["file"], incremental=False)
    result = row["result"]
    if result not in RESULTS:
        raise SelectionAuditError(f"unsupported official answer: {result!r}")
    cpu_time = row["cpu_time"]
    if isinstance(cpu_time, bool) or not isinstance(cpu_time, (int, float)) or cpu_time < 0:
        raise SelectionAuditError("official CPU time must be nonnegative")
    return {
        "benchmark_id": file_row["benchmark_id"],
        "cpu_seconds": cpu_time,
        "result": result,
        "solver": _component(row["solver"], "solver"),
        "year": year,
    }


def extract_single_query_divisions(defs_source: bytes) -> dict[str, list[str]]:
    """Extract the SQ division map from pinned ``defs.py`` without importing it."""
    try:
        module = ast.parse(defs_source.decode("utf-8"), filename="pinned-smtcomp-defs.py")
    except (UnicodeDecodeError, SyntaxError) as error:
        raise SelectionAuditError("cannot parse pinned organizer definitions") from error

    enum_values = _extract_enum_values(module)
    if set(enum_values) != {"Track", "Division", "Logic"}:
        raise SelectionAuditError("pinned organizer enum definitions are incomplete")

    tracks_value: ast.expr | None = None
    for node in module.body:
        if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == "tracks":
            tracks_value = node.value
        elif isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "tracks" for target in node.targets
        ):
            tracks_value = node.value
    if not isinstance(tracks_value, ast.Dict):
        raise SelectionAuditError("pinned organizer tracks table is missing")

    single_query: ast.expr | None = None
    for key, value in zip(tracks_value.keys, tracks_value.values, strict=True):
        if _enum_attribute(key, "Track") == "SingleQuery":
            single_query = value
            break
    if not isinstance(single_query, ast.Dict):
        raise SelectionAuditError("pinned organizer SingleQuery table is missing")

    output: dict[str, list[str]] = {}
    for division_node, logic_nodes in zip(single_query.keys, single_query.values, strict=True):
        division_name = _enum_attribute(division_node, "Division")
        if division_name is None or division_name not in enum_values["Division"]:
            raise SelectionAuditError("invalid division key in pinned organizer table")
        if not isinstance(logic_nodes, (ast.Set, ast.List, ast.Tuple)):
            raise SelectionAuditError("invalid logic collection in pinned organizer table")
        logics = []
        for logic_node in logic_nodes.elts:
            logic_name = _enum_attribute(logic_node, "Logic")
            if logic_name is None or logic_name not in enum_values["Logic"]:
                raise SelectionAuditError("invalid logic in pinned organizer table")
            logics.append(enum_values["Logic"][logic_name])
        division = enum_values["Division"][division_name]
        if division in output:
            raise SelectionAuditError("duplicate SingleQuery division")
        output[division] = sorted(logics)
    return dict(sorted(output.items()))


def extract_removed_benchmark_ids(defs_source: bytes) -> set[str]:
    """Extract the two pre-selection removals from pinned ``defs.py`` by AST."""
    try:
        module = ast.parse(defs_source.decode("utf-8"), filename="pinned-smtcomp-defs.py")
    except (UnicodeDecodeError, SyntaxError) as error:
        raise SelectionAuditError("cannot parse pinned organizer definitions") from error
    enum_values = _extract_enum_values(module)
    config = next(
        (node for node in module.body if isinstance(node, ast.ClassDef) and node.name == "Config"),
        None,
    )
    if config is None:
        raise SelectionAuditError("pinned organizer Config class is missing")
    value: ast.expr | None = None
    for statement in config.body:
        if isinstance(statement, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == "removed_benchmarks"
            for target in statement.targets
        ):
            value = statement.value
            break
    if not isinstance(value, (ast.List, ast.Tuple)):
        raise SelectionAuditError("pinned organizer removal table is missing")
    output = set()
    for row_node in value.elts:
        if not isinstance(row_node, ast.Dict):
            raise SelectionAuditError("invalid organizer removal row")
        row = {}
        for key_node, item_node in zip(row_node.keys, row_node.values, strict=True):
            if not isinstance(key_node, ast.Constant) or not isinstance(key_node.value, str):
                raise SelectionAuditError("invalid organizer removal key")
            row[key_node.value] = item_node
        if set(row) != {"logic", "family", "name"}:
            raise SelectionAuditError("organizer removal fields differ")
        logic_call = row["logic"]
        if (
            not isinstance(logic_call, ast.Call)
            or not isinstance(logic_call.func, ast.Name)
            or logic_call.func.id != "int"
            or len(logic_call.args) != 1
        ):
            raise SelectionAuditError("organizer removal logic is not int(Logic.*)")
        logic_name = _enum_attribute(logic_call.args[0], "Logic")
        if logic_name is None or logic_name not in enum_values["Logic"]:
            raise SelectionAuditError("unknown logic in organizer removal")
        family = _literal_string(row["family"], "removal family")
        name = _component(_literal_string(row["name"], "removal name"), "name")
        family_parts = [_component(part, "family") for part in PurePosixPath(family).parts]
        if not family_parts:
            raise SelectionAuditError("empty organizer removal family")
        output.add(
            str(
                PurePosixPath(
                    "non-incremental",
                    enum_values["Logic"][logic_name],
                    *family_parts,
                    name,
                )
            )
        )
    if len(output) != len(value.elts):
        raise SelectionAuditError("duplicate organizer removal")
    return output


def adapt_official_submissions(
    documents: Sequence[Mapping[str, Any]],
    divisions: Mapping[str, Sequence[str]],
) -> list[dict[str, Any]]:
    """Expand official submission divisions/logics into normalized SQ rows."""
    valid_logics = {logic for logics in divisions.values() for logic in logics}
    normalized = []
    for document in documents:
        if not isinstance(document, Mapping):
            raise SelectionAuditError("official submission is not an object")
        if "name" not in document or "participations" not in document:
            raise SelectionAuditError("official submission lacks name or participations")
        competitive = document.get("competitive", True)
        if not isinstance(competitive, bool):
            raise SelectionAuditError("official submission competitive flag is not Boolean")
        seed_value = document.get("seed")
        if seed_value is None:
            seed = None
        else:
            if isinstance(seed_value, bool):
                raise SelectionAuditError("official submission seed is Boolean")
            try:
                seed = int(seed_value)
            except (TypeError, ValueError) as error:
                raise SelectionAuditError("official submission seed is not integer-like") from error
        participations = document["participations"]
        if not isinstance(participations, list):
            raise SelectionAuditError("official submission participations are not a list")
        normalized_participations = []
        for participation in participations:
            if not isinstance(participation, Mapping):
                raise SelectionAuditError("official participation is not an object")
            allowed = {"archive", "command", "divisions", "experimental", "logics", "tracks"}
            if not set(participation) <= allowed or "tracks" not in participation:
                raise SelectionAuditError("official participation fields differ")
            tracks = participation["tracks"]
            if not isinstance(tracks, list) or not all(isinstance(track, str) for track in tracks):
                raise SelectionAuditError("official participation tracks are invalid")
            if "SingleQuery" not in tracks:
                continue
            expanded: set[str] = set()
            division_names = participation.get("divisions", [])
            explicit_logics_value = participation.get("logics", [])
            if not isinstance(division_names, list):
                raise SelectionAuditError("official divisions are not a list")
            if isinstance(explicit_logics_value, str):
                try:
                    pattern = re.compile(explicit_logics_value)
                except re.error as error:
                    raise SelectionAuditError("official logic regexp is invalid") from error
                explicit_logics = sorted(
                    logic for logic in valid_logics if pattern.fullmatch(logic)
                )
            elif isinstance(explicit_logics_value, list):
                explicit_logics = explicit_logics_value
            else:
                raise SelectionAuditError("official logics are neither a list nor regexp")
            for division in division_names:
                if division not in divisions:
                    raise SelectionAuditError(f"unknown official division: {division!r}")
                expanded.update(divisions[division])
            for logic in explicit_logics:
                if logic not in valid_logics:
                    raise SelectionAuditError(f"unknown official SingleQuery logic: {logic!r}")
                expanded.add(logic)
            if expanded:
                normalized_participations.append(
                    {"logics": sorted(expanded), "track": "single-query"}
                )
        normalized.append(
            {
                "competitive": competitive,
                "name": _component(document["name"], "solver"),
                "participations": normalized_participations,
                "seed": seed,
            }
        )
    return normalized


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
    accumulator = HistoricalAccumulator(
        known_ids,
        first_year=first_year,
        last_year=last_year,
        threshold=threshold,
    )
    for row in rows:
        accumulator.add(row)
    return accumulator.facts()


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


def _gzip_json(compressed: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(gzip.decompress(compressed))
    except (gzip.BadGzipFile, json.JSONDecodeError, UnicodeDecodeError, OSError) as error:
        raise SelectionAuditError(f"cannot decode {label}") from error
    if not isinstance(value, dict):
        raise SelectionAuditError(f"{label} is not a JSON object")
    return value


def _official_file(value: Any, *, incremental: bool) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != {"incremental", "logic", "family", "name"}:
        raise SelectionAuditError("official file identity fields differ")
    if value["incremental"] is not incremental:
        raise SelectionAuditError("official file incremental flag differs")
    family = value["family"]
    if not isinstance(family, list) or not family:
        raise SelectionAuditError("official file family is invalid")
    logic = _component(value["logic"], "logic")
    name = _component(value["name"], "name")
    normalized_family = [_component(component, "family") for component in family]
    prefix = "incremental" if incremental else "non-incremental"
    return {
        "benchmark_id": str(PurePosixPath(prefix, logic, *normalized_family, name)),
        "family": normalized_family,
        "logic": logic,
        "name": name,
    }


def _enum_attribute(node: ast.expr | None, enum_name: str) -> str | None:
    if (
        isinstance(node, ast.Attribute)
        and isinstance(node.value, ast.Name)
        and node.value.id == enum_name
    ):
        return node.attr
    return None


def _extract_enum_values(module: ast.Module) -> dict[str, dict[str, str]]:
    enum_values: dict[str, dict[str, str]] = {}
    for node in module.body:
        if isinstance(node, ast.ClassDef) and node.name in {"Track", "Division", "Logic"}:
            values: dict[str, str] = {}
            for statement in node.body:
                if (
                    isinstance(statement, ast.Assign)
                    and len(statement.targets) == 1
                    and isinstance(statement.targets[0], ast.Name)
                    and isinstance(statement.value, ast.Constant)
                    and isinstance(statement.value.value, str)
                ):
                    values[statement.targets[0].id] = statement.value.value
            enum_values[node.name] = values
    if set(enum_values) != {"Track", "Division", "Logic"}:
        raise SelectionAuditError("pinned organizer enum definitions are incomplete")
    return enum_values


def _literal_string(node: ast.expr, label: str) -> str:
    if not isinstance(node, ast.Constant) or not isinstance(node.value, str):
        raise SelectionAuditError(f"{label} is not a string literal")
    return node.value
