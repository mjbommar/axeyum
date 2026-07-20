#!/usr/bin/env python3
"""Measure exact and implication-cache opportunities in ordered Glaurung traces."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import pathlib
import statistics
import sys
from dataclasses import dataclass, field
from typing import Any, Iterable


REGISTRATION_SCHEMA = "axeyum-glaurung-six-cell-registration-v1"
REPORT_SCHEMA = "axeyum-glaurung-paired-analysis-v1"
TRACE_SCHEMA = "glaurung-ordered-trace-v1"
RESULT_SCHEMAS = {
    "textual-query": "axeyum.glaurung-constraint-cache-opportunity.v1",
    "canonical-constraint-set": "axeyum.glaurung-constraint-cache-opportunity.v2",
}


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def read_json(path: pathlib.Path, *, label: str) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be a JSON object")
    return value, raw


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label} must be a non-empty string")
    return value


@dataclass
class Scope:
    scope_id: str
    constraint_id: str | None = None


@dataclass
class UnsatTrieNode:
    terminal: bool = False
    children: dict[str, "UnsatTrieNode"] = field(default_factory=dict)


class UnsatSubsetTrie:
    """Store sorted UNSAT conjunctions and find one that is a query subset."""

    def __init__(self) -> None:
        self.root = UnsatTrieNode()

    def insert(self, constraints: frozenset[str]) -> None:
        node = self.root
        for constraint in sorted(constraints):
            node = node.children.setdefault(constraint, UnsatTrieNode())
        node.terminal = True

    def has_subset(self, constraints: frozenset[str]) -> bool:
        ordered = sorted(constraints)

        def search(node: UnsatTrieNode, start: int) -> bool:
            if node.terminal:
                return True
            for index in range(start, len(ordered)):
                child = node.children.get(ordered[index])
                if child is not None and search(child, index + 1):
                    return True
            return False

        return search(self.root, 0)


class SatSupersetIndex:
    """Index cached SAT conjunctions that logically imply a weaker query."""

    def __init__(self) -> None:
        self.entries: list[frozenset[str]] = []
        self.postings: dict[str, set[int]] = {}

    def insert(self, constraints: frozenset[str]) -> None:
        entry_id = len(self.entries)
        self.entries.append(constraints)
        for constraint in constraints:
            self.postings.setdefault(constraint, set()).add(entry_id)

    def has_superset(self, constraints: frozenset[str]) -> bool:
        if not self.entries:
            return False
        if not constraints:
            return True
        posting_sets = [self.postings.get(constraint) for constraint in constraints]
        if any(posting is None for posting in posting_sets):
            return False
        ordered = sorted(posting_sets, key=len)  # type: ignore[arg-type]
        candidates = set(ordered[0])
        for posting in ordered[1:]:
            candidates.intersection_update(posting)
            if not candidates:
                return False
        return bool(candidates)


@dataclass
class CacheCounts:
    checks: int = 0
    sat: int = 0
    unsat: int = 0
    exact_sat_hits: int = 0
    exact_unsat_hits: int = 0
    sat_superset_hits: int = 0
    unsat_subset_hits: int = 0
    misses: int = 0

    def as_dict(self) -> dict[str, Any]:
        exact = self.exact_sat_hits + self.exact_unsat_hits
        implication = self.sat_superset_hits + self.unsat_subset_hits
        structural = exact + implication
        return {
            "checks": self.checks,
            "sat": self.sat,
            "unsat": self.unsat,
            "exact_hits": exact,
            "exact_sat_hits": self.exact_sat_hits,
            "exact_unsat_hits": self.exact_unsat_hits,
            "sat_superset_hits": self.sat_superset_hits,
            "unsat_subset_hits": self.unsat_subset_hits,
            "implication_only_hits": implication,
            "structural_hits": structural,
            "misses": self.misses,
            "exact_hit_rate": exact / self.checks if self.checks else 0.0,
            "structural_hit_rate": structural / self.checks if self.checks else 0.0,
        }


class StructuralCache:
    def __init__(self, exact_identity: str = "textual-query") -> None:
        if exact_identity not in RESULT_SCHEMAS:
            raise ValueError(f"unsupported exact identity: {exact_identity}")
        self.exact_identity = exact_identity
        self.exact: dict[str | tuple[str, ...], str] = {}
        self.unsat = UnsatSubsetTrie()
        self.sat = SatSupersetIndex()
        self.counts = CacheCounts()

    def observe(
        self,
        *,
        query_sha256: str,
        outcome: str,
        constraints: frozenset[str],
    ) -> str:
        self.counts.checks += 1
        if outcome == "sat":
            self.counts.sat += 1
        elif outcome == "unsat":
            self.counts.unsat += 1
        else:
            raise ValueError(f"cache opportunity requires a decided outcome: {outcome}")

        exact_key: str | tuple[str, ...] = (
            query_sha256
            if self.exact_identity == "textual-query"
            else tuple(sorted(constraints))
        )
        previous = self.exact.get(exact_key)
        if previous is not None:
            if previous != outcome:
                raise ValueError(f"conflicting exact outcome for query {query_sha256}")
            if outcome == "sat":
                self.counts.exact_sat_hits += 1
            else:
                self.counts.exact_unsat_hits += 1
            classification = f"exact-{outcome}"
        else:
            unsat_hit = self.unsat.has_subset(constraints)
            sat_hit = self.sat.has_superset(constraints)
            if unsat_hit and sat_hit:
                raise ValueError("cached SAT/UNSAT implications conflict")
            if unsat_hit:
                if outcome != "unsat":
                    raise ValueError("cached UNSAT subset contradicts recorded SAT")
                self.counts.unsat_subset_hits += 1
                classification = "unsat-subset"
            elif sat_hit:
                if outcome != "sat":
                    raise ValueError("cached SAT superset contradicts recorded UNSAT")
                self.counts.sat_superset_hits += 1
                classification = "sat-superset"
            else:
                self.counts.misses += 1
                classification = "miss"

        self.exact[exact_key] = outcome
        if outcome == "sat":
            self.sat.insert(constraints)
        else:
            self.unsat.insert(constraints)
        return classification


def validate_trace_files(trace_dir: pathlib.Path) -> tuple[dict[str, Any], bytes]:
    manifest, manifest_raw = read_json(
        trace_dir / "trace-manifest-v1.json", label=f"trace manifest {trace_dir}"
    )
    if manifest.get("schema") != TRACE_SCHEMA:
        raise ValueError(f"{trace_dir}: trace schema differs")
    events_raw = (trace_dir / "events-v1.ndjson").read_bytes()
    if sha256(events_raw) != manifest.get("events_sha256"):
        raise ValueError(f"{trace_dir}: event stream SHA-256 differs")
    index_raw = (trace_dir / "query-index-v1.json").read_bytes()
    if sha256(index_raw) != manifest.get("query_index_sha256"):
        raise ValueError(f"{trace_dir}: query index SHA-256 differs")
    return manifest, events_raw


def analyze_events(
    events_raw: bytes, *, exact_identity: str = "textual-query"
) -> dict[str, Any]:
    paths: dict[str, list[Scope]] = {}
    cache = StructuralCache(exact_identity)
    sequence_rows: list[dict[str, Any]] = []
    assertion_counts: list[int] = []
    event_count = 0

    for line_number, raw_line in enumerate(events_raw.splitlines(), 1):
        try:
            event = json.loads(raw_line)
        except json.JSONDecodeError as error:
            raise ValueError(f"event line {line_number} is invalid JSON") from error
        if not isinstance(event, dict):
            raise ValueError(f"event line {line_number} must be an object")
        if event.get("event_seq") != event_count:
            raise ValueError(f"non-contiguous event sequence at line {line_number}")
        event_count += 1
        kind = require_string(event.get("event"), "event kind")
        path_id = require_string(event.get("path_id"), "path ID")

        if kind == "path_start":
            parent = event.get("parent_path_id")
            if parent is None:
                scopes: list[Scope] = []
            else:
                parent_id = require_string(parent, "parent path ID")
                if parent_id not in paths:
                    raise ValueError(f"path {path_id} has unknown parent {parent_id}")
                scopes = [Scope(scope.scope_id, scope.constraint_id) for scope in paths[parent_id]]
            if path_id in paths:
                raise ValueError(f"duplicate path start: {path_id}")
            paths[path_id] = scopes
        elif kind == "push":
            scope_id = require_string(event.get("scope_id"), "scope ID")
            scopes = paths.get(path_id)
            if scopes is None:
                raise ValueError(f"push references unknown path {path_id}")
            if event.get("prior_depth") != len(scopes):
                raise ValueError(f"{path_id}: push prior depth differs")
            scopes.append(Scope(scope_id))
        elif kind == "assert":
            scope_id = require_string(event.get("scope_id"), "scope ID")
            constraint = require_string(event.get("constraint_id"), "constraint ID")
            scopes = paths.get(path_id)
            if not scopes or scopes[-1].scope_id != scope_id:
                raise ValueError(f"{path_id}: assertion does not match latest scope")
            if scopes[-1].constraint_id is not None:
                raise ValueError(f"{path_id}: scope has duplicate assertion")
            scopes[-1].constraint_id = constraint
        elif kind == "pop":
            scopes = paths.get(path_id)
            if not scopes:
                raise ValueError(f"pop references empty or unknown path {path_id}")
            scope = scopes.pop()
            if scope.scope_id != event.get("scope_id"):
                raise ValueError(f"{path_id}: popped scope identity differs")
        elif kind == "check":
            scopes = paths.get(path_id)
            if scopes is None or any(scope.constraint_id is None for scope in scopes):
                raise ValueError(f"{path_id}: check has incomplete scopes")
            if event.get("active_constraint_count") != len(scopes):
                raise ValueError(f"{path_id}: active constraint count differs")
            constraints = frozenset(
                scope.constraint_id for scope in scopes if scope.constraint_id is not None
            )
            query_sha256 = require_string(event.get("query_sha256"), "query SHA-256")
            outcome = require_string(event.get("outcome"), "query outcome")
            classification = cache.observe(
                query_sha256=query_sha256,
                outcome=outcome,
                constraints=constraints,
            )
            assertion_counts.append(len(constraints))
            sequence_rows.append(
                {
                    "query_sha256": query_sha256,
                    "outcome": outcome,
                    "constraints": sorted(constraints),
                    "classification": classification,
                }
            )
        elif kind == "path_end":
            if paths.pop(path_id, None) is None:
                raise ValueError(f"path end references unknown path {path_id}")
        elif kind in {
            "analysis_start",
            "analysis_end",
            "model_read",
            "model_choice",
            "warm_owner_share",
            "warm_owner_release",
        }:
            pass
        else:
            raise ValueError(f"unsupported event kind: {kind}")

    if paths:
        raise ValueError(f"event stream retains paths: {sorted(paths)}")
    if not assertion_counts:
        raise ValueError("event stream has no checks")
    ordered_counts = sorted(assertion_counts)

    def nearest_rank(fraction: float) -> int:
        index = max(
            0,
            min(len(ordered_counts) - 1, math.ceil(fraction * len(ordered_counts)) - 1),
        )
        return ordered_counts[index]

    return {
        "event_count": event_count,
        "sequence_digest": digest(sequence_rows),
        "cache": cache.counts.as_dict(),
        "distinct_exact_queries": len(cache.exact),
        "distinct_constraint_sets": len(
            {tuple(row["constraints"]) for row in sequence_rows}
        ),
        "assertion_count": {
            "min": min(assertion_counts),
            "median": statistics.median(assertion_counts),
            "p95": nearest_rank(0.95),
            "max": max(assertion_counts),
        },
    }


def analyze_trace(
    trace_dir: pathlib.Path, *, driver_sha256: str, exact_identity: str
) -> dict[str, Any]:
    manifest, events_raw = validate_trace_files(trace_dir)
    driver = manifest.get("driver")
    if not isinstance(driver, dict) or driver.get("sha256") != driver_sha256:
        raise ValueError(f"{trace_dir}: driver SHA-256 differs")
    result = analyze_events(events_raw, exact_identity=exact_identity)
    if result["event_count"] != manifest.get("event_count"):
        raise ValueError(f"{trace_dir}: event count differs from manifest")
    native_replay = manifest.get("native_replay")
    if not isinstance(native_replay, dict) or result["cache"]["checks"] != (
        native_replay.get("warm_check_count")
    ):
        raise ValueError(f"{trace_dir}: check count differs from manifest")
    return {
        "trace_path": str(trace_dir),
        "manifest_sha256": sha256((trace_dir / "trace-manifest-v1.json").read_bytes()),
        **result,
    }


def sum_counts(rows: Iterable[dict[str, Any]]) -> dict[str, Any]:
    fields = (
        "checks",
        "sat",
        "unsat",
        "exact_hits",
        "exact_sat_hits",
        "exact_unsat_hits",
        "sat_superset_hits",
        "unsat_subset_hits",
        "implication_only_hits",
        "structural_hits",
        "misses",
    )
    total = {field: 0 for field in fields}
    for row in rows:
        for field in fields:
            total[field] += row[field]
    checks = total["checks"]
    total["exact_hit_rate"] = total["exact_hits"] / checks if checks else 0.0
    total["structural_hit_rate"] = total["structural_hits"] / checks if checks else 0.0
    return total


def analyze_campaign(
    registration_path: pathlib.Path,
    report_paths: list[pathlib.Path],
    *,
    exact_identity: str = "textual-query",
) -> dict[str, Any]:
    if exact_identity not in RESULT_SCHEMAS:
        raise ValueError(f"unsupported exact identity: {exact_identity}")
    registration, registration_raw = read_json(
        registration_path, label="six-cell registration"
    )
    if registration.get("schema") != REGISTRATION_SCHEMA:
        raise ValueError("six-cell registration schema differs")
    registered_drivers = {
        row["sha256"]: row["label"] for row in registration.get("drivers", [])
    }
    if len(registered_drivers) != 4 or len(report_paths) != 4:
        raise ValueError("constraint-cache opportunity requires exactly four drivers")

    drivers: list[dict[str, Any]] = []
    report_hashes: dict[str, str] = {}
    seen_drivers: set[str] = set()
    for report_path in report_paths:
        report, report_raw = read_json(report_path, label=f"report {report_path}")
        if report.get("schema") != REPORT_SCHEMA:
            raise ValueError(f"{report_path}: report schema differs")
        driver = report.get("driver")
        if not isinstance(driver, dict):
            raise ValueError(f"{report_path}: driver identity is missing")
        driver_sha256 = require_string(driver.get("sha256"), "driver SHA-256")
        if driver_sha256 not in registered_drivers or driver_sha256 in seen_drivers:
            raise ValueError(f"{report_path}: driver population differs")
        seen_drivers.add(driver_sha256)
        if report.get("repetitions") != 5:
            raise ValueError(f"{report_path}: repetition count differs")
        gate = report.get("neutral_regime_gate")
        if not isinstance(gate, dict) or gate.get("accepted") is not True:
            raise ValueError(f"{report_path}: accepted neutral gate is required")
        trace_paths = report.get("trace_paths")
        if not isinstance(trace_paths, list) or len(trace_paths) != 5:
            raise ValueError(f"{report_path}: expected five trace paths")
        repetitions = [
            analyze_trace(
                pathlib.Path(path),
                driver_sha256=driver_sha256,
                exact_identity=exact_identity,
            )
            for path in trace_paths
        ]
        sequence_digests = {row["sequence_digest"] for row in repetitions}
        cache_digests = {digest(row["cache"]) for row in repetitions}
        drivers.append(
            {
                "label": registered_drivers[driver_sha256],
                "sha256": driver_sha256,
                "repetitions": repetitions,
                "sequence_stable": len(sequence_digests) == 1,
                "cache_counts_stable": len(cache_digests) == 1,
                "per_process": repetitions[0]["cache"],
                "all_processes": sum_counts(row["cache"] for row in repetitions),
            }
        )
        report_hashes[str(report_path)] = sha256(report_raw)

    if seen_drivers != set(registered_drivers):
        raise ValueError("report set does not cover all registered drivers")
    drivers.sort(key=lambda row: list(registered_drivers.values()).index(row["label"]))
    all_processes = sum_counts(
        repetition["cache"]
        for driver in drivers
        for repetition in driver["repetitions"]
    )
    return {
        "schema": RESULT_SCHEMAS[exact_identity],
        "exact_identity": exact_identity,
        "claim_boundary": (
            "structurally cache-addressable verdict opportunities only; no cache "
            "implementation, model replay, timing, or warm-additivity result"
        ),
        "inputs": {
            "registration_path": str(registration_path),
            "registration_sha256": sha256(registration_raw),
            "report_sha256": dict(sorted(report_hashes.items())),
        },
        "drivers": drivers,
        "all_processes": all_processes,
    }


def write_new_json(path: pathlib.Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"output already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=pathlib.Path, required=True)
    parser.add_argument("--reports", type=pathlib.Path, nargs="+", required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument(
        "--exact-identity",
        choices=tuple(RESULT_SCHEMAS),
        default="textual-query",
    )
    args = parser.parse_args()
    try:
        result = analyze_campaign(
            args.registration,
            args.reports,
            exact_identity=args.exact_identity,
        )
        write_new_json(args.output, result)
        print(json.dumps(result["all_processes"], sort_keys=True))
        return 0
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"constraint-cache opportunity analysis failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
