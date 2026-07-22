"""Independent standard-library checks for ADR-0356 S4 publication."""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

from scripts.smtcomp_repro.official_selection import canonical_json_bytes


FINAL_REASONS = {
    "selected-new",
    "selected-old",
    "excluded-explicit-removal",
    "excluded-noncompetitive-logic",
    "excluded-trivial",
    "excluded-cap-new",
    "excluded-cap-old",
}
INELIGIBLE_REASONS = {
    "excluded-explicit-removal",
    "excluded-noncompetitive-logic",
    "excluded-trivial",
}
ELIGIBLE_REASONS = {"eligible-new", "eligible-old"}
EXPECTED_MUTATIONS = tuple(f"M{number:02d}" for number in range(1, 19))
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
ELIGIBILITY_FIELDS = {
    "asserts",
    "benchmark_id",
    "family",
    "historical",
    "is_new",
    "logic",
    "logic_competitive",
    "name",
    "reason",
    "status",
}
CORPUS_FIELDS = {
    "archive",
    "asserts",
    "benchmark_id",
    "bytes",
    "family",
    "logic",
    "name",
    "sha256",
    "status",
}
DECISION_FIELDS = {
    "archive",
    "asserts",
    "benchmark_id",
    "bytes",
    "eligible",
    "family",
    "historical",
    "is_new",
    "logic",
    "logic_competitive",
    "name",
    "reason",
    "selected",
    "sha256",
    "status",
}


class FinalSelectionAuditError(ValueError):
    """A final selection artifact violates the registered S4 contract."""


def sha256_file(path: Path) -> tuple[int, str]:
    """Return byte count and SHA-256 for a regular non-symlink file."""
    if path.is_symlink() or not path.is_file():
        raise FinalSelectionAuditError(f"not a regular file: {path}")
    size = 0
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while data := source.read(1024 * 1024):
            size += len(data)
            digest.update(data)
    return size, digest.hexdigest()


def validate_benchmark_id(value: object) -> str:
    """Require one canonical non-incremental POSIX benchmark ID."""
    if not isinstance(value, str) or "\\" in value:
        raise FinalSelectionAuditError(f"invalid benchmark ID: {value!r}")
    path = PurePosixPath(value)
    if (
        path.as_posix() != value
        or path.is_absolute()
        or len(path.parts) < 4
        or path.parts[0] != "non-incremental"
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FinalSelectionAuditError(f"invalid benchmark ID: {value!r}")
    return value


def read_selected(path: Path) -> list[str]:
    """Read a canonical LF-terminated, strictly sorted selected path list."""
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise FinalSelectionAuditError("official selected list is not UTF-8") from error
    if not text.endswith("\n") or "\r" in text:
        raise FinalSelectionAuditError("official selected list is not LF-terminated")
    paths = text.splitlines()
    previous: str | None = None
    for value in paths:
        validate_benchmark_id(value)
        if previous is not None and value <= previous:
            raise FinalSelectionAuditError("official selected list is not strictly sorted and unique")
        previous = value
    return paths


def terminal_reason(eligibility_reason: object, selected: bool) -> str:
    """Map an S1 eligibility reason and official membership to one terminal reason."""
    if not isinstance(eligibility_reason, str):
        raise FinalSelectionAuditError("eligibility reason is not a string")
    if eligibility_reason in INELIGIBLE_REASONS:
        if selected:
            raise FinalSelectionAuditError(f"ineligible row was selected: {eligibility_reason}")
        return eligibility_reason
    if eligibility_reason == "eligible-new":
        return "selected-new" if selected else "excluded-cap-new"
    if eligibility_reason == "eligible-old":
        return "selected-old" if selected else "excluded-cap-old"
    raise FinalSelectionAuditError(f"unknown eligibility reason: {eligibility_reason!r}")


def merge_decision(
    eligibility: Mapping[str, Any],
    corpus: Mapping[str, Any],
    selected: bool,
) -> dict[str, Any]:
    """Validate and merge one aligned S1/S2 row into the canonical decision."""
    if set(eligibility) != ELIGIBILITY_FIELDS:
        raise FinalSelectionAuditError("eligibility fields differ")
    if set(corpus) != CORPUS_FIELDS:
        raise FinalSelectionAuditError("corpus fields differ")
    benchmark_id = validate_benchmark_id(eligibility.get("benchmark_id"))
    if corpus.get("benchmark_id") != benchmark_id:
        raise FinalSelectionAuditError("eligibility/corpus benchmark IDs differ")
    for key in ("asserts", "family", "logic", "name", "status"):
        if eligibility.get(key) != corpus.get(key):
            raise FinalSelectionAuditError(f"eligibility/corpus field differs: {benchmark_id} {key}")
    logic = corpus.get("logic")
    if not isinstance(logic, str) or PurePosixPath(benchmark_id).parts[1] != logic:
        raise FinalSelectionAuditError(f"logic/path mismatch: {benchmark_id}")
    byte_count = corpus.get("bytes")
    sha256 = corpus.get("sha256")
    archive = corpus.get("archive")
    family = corpus.get("family")
    if (
        isinstance(byte_count, bool)
        or not isinstance(byte_count, int)
        or byte_count < 0
        or not isinstance(sha256, str)
        or SHA256_PATTERN.fullmatch(sha256) is None
        or archive != f"{logic}.tar.zst"
        or not isinstance(family, list)
        or not family
        or not all(isinstance(component, str) and component for component in family)
    ):
        raise FinalSelectionAuditError(f"invalid corpus identity: {benchmark_id}")
    reason = terminal_reason(eligibility.get("reason"), selected)
    is_new = eligibility.get("is_new")
    if not isinstance(is_new, bool):
        raise FinalSelectionAuditError(f"invalid new/old flag: {benchmark_id}")
    if is_new != family[0].startswith("2025"):
        raise FinalSelectionAuditError(f"family/new flag mismatch: {benchmark_id}")
    if (reason.endswith("-new") and not is_new) or (reason.endswith("-old") and is_new):
        raise FinalSelectionAuditError(f"terminal reason/new flag mismatch: {benchmark_id}")
    decision = {
        "archive": archive,
        "asserts": corpus["asserts"],
        "benchmark_id": benchmark_id,
        "bytes": byte_count,
        "eligible": eligibility.get("reason") in ELIGIBLE_REASONS,
        "family": corpus["family"],
        "historical": eligibility.get("historical"),
        "is_new": is_new,
        "logic": logic,
        "logic_competitive": eligibility.get("logic_competitive"),
        "name": corpus["name"],
        "reason": reason,
        "selected": selected,
        "sha256": sha256,
        "status": corpus["status"],
    }
    if reason not in FINAL_REASONS or not isinstance(decision["logic_competitive"], bool):
        raise FinalSelectionAuditError(f"invalid terminal decision: {benchmark_id}")
    validate_published_decision(
        decision,
        corpus,
        {"benchmark_id": benchmark_id, "historical": decision["historical"]},
        selected,
    )
    return decision


def validate_published_decision(
    decision: Mapping[str, Any],
    corpus: Mapping[str, Any],
    historical: Mapping[str, Any],
    selected: bool,
) -> str:
    """Validate one published decision against its copied corpus/history rows."""
    if set(decision) != DECISION_FIELDS:
        raise FinalSelectionAuditError("published decision fields differ")
    if set(corpus) != CORPUS_FIELDS:
        raise FinalSelectionAuditError("published corpus fields differ")
    if set(historical) != {"benchmark_id", "historical"}:
        raise FinalSelectionAuditError("published historical fields differ")
    benchmark_id = validate_benchmark_id(decision.get("benchmark_id"))
    if corpus.get("benchmark_id") != benchmark_id or historical.get("benchmark_id") != benchmark_id:
        raise FinalSelectionAuditError("published ledger benchmark IDs differ")
    for key in ("archive", "asserts", "bytes", "family", "logic", "name", "sha256", "status"):
        if decision.get(key) != corpus.get(key):
            raise FinalSelectionAuditError(f"published corpus identity differs: {benchmark_id} {key}")
    if decision.get("historical") != historical.get("historical"):
        raise FinalSelectionAuditError(f"published historical identity differs: {benchmark_id}")
    _validate_historical_fact(decision.get("historical"), benchmark_id)
    logic = decision.get("logic")
    family = decision.get("family")
    byte_count = decision.get("bytes")
    sha256 = decision.get("sha256")
    if (
        not isinstance(logic, str)
        or PurePosixPath(benchmark_id).parts[1] != logic
        or decision.get("archive") != f"{logic}.tar.zst"
        or not isinstance(family, list)
        or not family
        or not all(isinstance(component, str) and component for component in family)
        or isinstance(byte_count, bool)
        or not isinstance(byte_count, int)
        or byte_count < 0
        or not isinstance(sha256, str)
        or SHA256_PATTERN.fullmatch(sha256) is None
    ):
        raise FinalSelectionAuditError(f"published corpus identity is malformed: {benchmark_id}")
    reason = decision.get("reason")
    if reason not in FINAL_REASONS or decision.get("selected") is not selected:
        raise FinalSelectionAuditError(f"published selection decision differs: {benchmark_id}")
    if selected != reason.startswith("selected-"):
        raise FinalSelectionAuditError(f"published terminal reason differs: {benchmark_id}")
    eligible = reason.startswith("selected-") or reason.startswith("excluded-cap-")
    if decision.get("eligible") is not eligible:
        raise FinalSelectionAuditError(f"published eligibility differs: {benchmark_id}")
    is_new = decision.get("is_new")
    if not isinstance(is_new, bool) or (
        (reason.endswith("-new") and not is_new) or (reason.endswith("-old") and is_new)
    ):
        raise FinalSelectionAuditError(f"published new/old identity differs: {benchmark_id}")
    if is_new != family[0].startswith("2025"):
        raise FinalSelectionAuditError(f"published family age differs: {benchmark_id}")
    logic_competitive = decision.get("logic_competitive")
    if (
        not isinstance(logic_competitive, bool)
        or (reason == "excluded-noncompetitive-logic" and logic_competitive)
        or (
            reason
            in {
                "selected-new",
                "selected-old",
                "excluded-trivial",
                "excluded-cap-new",
                "excluded-cap-old",
            }
            and not logic_competitive
        )
    ):
        raise FinalSelectionAuditError(f"published competitive identity differs: {benchmark_id}")
    return reason


def _validate_historical_fact(value: object, benchmark_id: str) -> None:
    if not isinstance(value, dict) or set(value) != {"file_coherent", "run", "trivial", "years"}:
        raise FinalSelectionAuditError(f"published historical fact is malformed: {benchmark_id}")
    if any(not isinstance(value[field], bool) for field in ("file_coherent", "run", "trivial")):
        raise FinalSelectionAuditError(f"published historical booleans are malformed: {benchmark_id}")
    years = value["years"]
    if not isinstance(years, list):
        raise FinalSelectionAuditError(f"published historical years are malformed: {benchmark_id}")
    previous_year = 2017
    admitted = []
    for row in years:
        if not isinstance(row, dict) or set(row) != {
            "coherent",
            "competitive",
            "result",
            "row_count",
            "trivial",
            "year",
        }:
            raise FinalSelectionAuditError(f"published historical year is malformed: {benchmark_id}")
        year = row["year"]
        row_count = row["row_count"]
        if (
            not isinstance(row["coherent"], bool)
            or not isinstance(row["competitive"], bool)
            or not isinstance(row["trivial"], bool)
            or isinstance(year, bool)
            or not isinstance(year, int)
            or not previous_year < year <= 2024
            or isinstance(row_count, bool)
            or not isinstance(row_count, int)
            or row_count <= 0
            or row["result"] not in {"sat", "unsat", "unknown"}
            or row["coherent"] is not value["file_coherent"]
            or (row["competitive"] and row_count <= 1)
            or (not row["competitive"] and (row["result"] != "unknown" or row["trivial"]))
            or (row["trivial"] and not row["competitive"])
        ):
            raise FinalSelectionAuditError(f"published historical year differs: {benchmark_id}")
        previous_year = year
        if row["competitive"]:
            admitted.append(row)
    if value["run"] is not bool(admitted) or value["trivial"] is not (
        bool(admitted) and all(row["trivial"] for row in admitted)
    ):
        raise FinalSelectionAuditError(f"published historical reduction differs: {benchmark_id}")


def validate_logic_summary(
    registered: Mapping[str, Any],
    observed: Mapping[str, int],
    official: Mapping[str, int] | None,
) -> None:
    """Require exact S1 quotas, terminal balance, and S3 per-logic counts."""
    logic = registered.get("logic")
    numeric_fields = (
        "metadata",
        "explicit_removal",
        "noncompetitive",
        "trivial",
        "selected_new_quota",
        "selected_old_quota",
        "eligible_new",
        "eligible_old",
    )
    if not isinstance(logic, str) or any(
        isinstance(registered.get(field), bool)
        or not isinstance(registered.get(field), int)
        or registered[field] < 0
        for field in numeric_fields
    ):
        raise FinalSelectionAuditError("registered per-logic summary is malformed")
    expected = {
        "metadata": registered.get("metadata"),
        "excluded-explicit-removal": registered.get("explicit_removal"),
        "excluded-noncompetitive-logic": registered.get("noncompetitive"),
        "excluded-trivial": registered.get("trivial"),
        "selected-new": registered.get("selected_new_quota"),
        "selected-old": registered.get("selected_old_quota"),
        "excluded-cap-new": registered.get("eligible_new", 0) - registered.get("selected_new_quota", 0),
        "excluded-cap-old": registered.get("eligible_old", 0) - registered.get("selected_old_quota", 0),
    }
    for key, value in expected.items():
        if observed.get(key, 0) != value:
            raise FinalSelectionAuditError(f"per-logic count differs: {logic} {key}")
    terminal_total = sum(observed.get(reason, 0) for reason in FINAL_REASONS)
    if terminal_total != observed.get("metadata"):
        raise FinalSelectionAuditError(f"per-logic terminal partition differs: {logic}")
    official_new = 0 if official is None else official.get("new")
    official_old = 0 if official is None else official.get("old")
    official_selected = 0 if official is None else official.get("selected")
    if (
        official_new != observed.get("selected-new", 0)
        or official_old != observed.get("selected-old", 0)
        or official_selected != observed.get("selected-new", 0) + observed.get("selected-old", 0)
    ):
        raise FinalSelectionAuditError(f"official per-logic count differs: {logic}")


def _validate_mutation_fixture(fixture: Mapping[str, Any]) -> None:
    for name in ("authority", "data", "submissions", "release", "selected_bytes", "repeat", "auditor", "dependencies"):
        if fixture.get(name) is not True:
            raise FinalSelectionAuditError(f"fixture identity differs: {name}")
    metadata = fixture.get("metadata")
    corpus = fixture.get("corpus")
    decisions = fixture.get("decisions")
    selected = fixture.get("selected")
    if not all(isinstance(value, list) for value in (metadata, corpus, decisions, selected)):
        raise FinalSelectionAuditError("fixture ledgers are malformed")
    if len(metadata) != len(set(metadata)) or len(decisions) != len(set(decisions)):
        raise FinalSelectionAuditError("fixture metadata or decisions are duplicated")
    if set(metadata) != set(corpus) or set(metadata) != set(decisions):
        raise FinalSelectionAuditError("fixture population bijection differs")
    if len(selected) != len(set(selected)) or not set(selected).issubset(metadata):
        raise FinalSelectionAuditError("fixture selected IDs differ")
    for value in metadata:
        validate_benchmark_id(value)
    if fixture.get("competitive") is not True or fixture.get("historical") is not True:
        raise FinalSelectionAuditError("fixture eligibility fact differs")
    if fixture.get("inclusive_boundary") is not True:
        raise FinalSelectionAuditError("fixture 1.0-second boundary differs")
    if fixture.get("selected_eligible") is not True:
        raise FinalSelectionAuditError("fixture selected an ineligible row")
    if fixture.get("producer_selected") != selected or fixture.get("auditor_selected") != selected:
        raise FinalSelectionAuditError("fixture producer/auditor membership differs")
    if fixture.get("cap") != fixture.get("selected_count"):
        raise FinalSelectionAuditError("fixture quota differs")
    if fixture.get("reasons") != len(metadata):
        raise FinalSelectionAuditError("fixture terminal reason count differs")
    if fixture.get("completion_last") is not True:
        raise FinalSelectionAuditError("fixture completion is premature")


def run_registered_mutations(contract: Mapping[str, Any]) -> list[dict[str, str]]:
    """Execute one rejecting synthetic mutation for each registered M01--M18 ID."""
    mutations = contract.get("mutations")
    if not isinstance(mutations, list) or tuple(row.get("id") for row in mutations) != EXPECTED_MUTATIONS:
        raise FinalSelectionAuditError("registered mutation IDs differ")
    a = "non-incremental/QF_BV/family/a.smt2"
    b = "non-incremental/QF_BV/family/b.smt2"
    base: dict[str, Any] = {
        "auditor": True,
        "authority": True,
        "cap": 1,
        "completion_last": True,
        "competitive": True,
        "corpus": [a, b],
        "data": True,
        "decisions": [a, b],
        "dependencies": True,
        "historical": True,
        "inclusive_boundary": True,
        "metadata": [a, b],
        "reasons": 2,
        "release": True,
        "repeat": True,
        "selected": [a],
        "auditor_selected": [a],
        "producer_selected": [a],
        "selected_bytes": True,
        "selected_count": 1,
        "selected_eligible": True,
        "submissions": True,
    }
    changes: dict[str, tuple[str, Any]] = {
        "M01": ("authority", False),
        "M02": ("data", False),
        "M03": ("submissions", False),
        "M04": ("release", False),
        "M05": ("corpus", [a]),
        "M06": ("decisions", [a, a]),
        "M07": ("metadata", ["../escape.smt2", b]),
        "M08": ("selected_bytes", False),
        "M09": ("competitive", False),
        "M10": ("historical", False),
        "M11": ("inclusive_boundary", False),
        "M12": ("selected_eligible", False),
        "M13": ("cap", 2),
        "M14": ("selected", [a, "non-incremental/QF_BV/family/missing.smt2"]),
        "M15": ("reasons", 1),
        "M16": ("repeat", False),
        "M17": ("auditor_selected", [b]),
        "M18": ("completion_last", False),
    }
    results = []
    for row in mutations:
        mutation_id = row["id"]
        fixture = dict(base)
        key, value = changes[mutation_id]
        fixture[key] = value
        try:
            _validate_mutation_fixture(fixture)
        except FinalSelectionAuditError:
            results.append({"id": mutation_id, "rejects": row["rejects"], "result": "rejected"})
        else:
            raise FinalSelectionAuditError(f"registered mutation did not reject: {mutation_id}")
    return results


def summarize_reasons(decisions: list[Mapping[str, Any]]) -> Counter[str]:
    """Small-fixture helper used by S4 mutation tests."""
    reasons: Counter[str] = Counter()
    seen: set[str] = set()
    for decision in decisions:
        benchmark_id = validate_benchmark_id(decision.get("benchmark_id"))
        reason = decision.get("reason")
        if benchmark_id in seen or reason not in FINAL_REASONS:
            raise FinalSelectionAuditError("duplicate ID or unknown terminal reason")
        seen.add(benchmark_id)
        reasons[reason] += 1
    return reasons
