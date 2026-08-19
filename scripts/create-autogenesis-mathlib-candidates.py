#!/usr/bin/env python3
"""Select a deterministic, statement-only Mathlib Nat/Int candidate pool."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from collections import Counter, defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE_MANIFEST = ROOT / "artifacts/autogenesis/mathlib-statement-source-v1.json"
POLICY = ROOT / "artifacts/autogenesis/mathlib-nursery-source-policy-v1.json"
COMMITTED = ROOT / "artifacts/autogenesis/mathlib-nat-int-candidates-v1.json"
CONSTANT_RE = re.compile(r"Lean\.Expr\.const\s+`([^\s\[\)]+)")


class CandidateError(RuntimeError):
    """The candidate pool cannot be derived exactly from statement-only input."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def load_object(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CandidateError(f"{path} is not a JSON object")
    return value


def validate_inputs(source: dict[str, Any], policy: dict[str, Any]) -> None:
    unsigned = dict(source)
    claimed = unsigned.pop("manifest_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise CandidateError("source manifest digest is invalid")
    if policy.get("schema_version") != 1 or policy.get("kind") != "axeyum-autogenesis-mathlib-candidate-policy":
        raise CandidateError("candidate policy schema identity is invalid")
    if policy.get("source_manifest_sha256") != claimed:
        raise CandidateError("candidate policy names a different statement source")
    families = policy.get("families")
    if not isinstance(families, list) or not families:
        raise CandidateError("candidate policy has no families")
    modules = [row.get("module") for row in families if isinstance(row, dict)]
    if len(modules) != len(families) or len(set(modules)) != len(modules) or modules != sorted(modules):
        raise CandidateError("candidate family modules must be unique and sorted")
    quota = policy.get("quota_per_family")
    if not isinstance(quota, int) or quota < 1 or policy.get("candidate_count") != quota * len(families):
        raise CandidateError("candidate count does not equal family quota times family count")
    if policy.get("ranking") != [
        "fewest-distinct-type-constants",
        "shortest-structural-type",
        "lexicographic-declaration-name",
    ]:
        raise CandidateError("candidate ranking changed")
    authority = policy.get("authority")
    if not isinstance(authority, dict) or "statement-only" not in str(authority.get("answers")):
        raise CandidateError("statement-only selection authority is absent")


def load_rows(path: pathlib.Path, expected_sha256: str) -> list[dict[str, Any]]:
    if not path.is_file() or sha256_file(path) != expected_sha256:
        raise CandidateError("statement source artifact is absent or has the wrong digest")
    rows: list[dict[str, Any]] = []
    previous = ""
    for number, line in enumerate(path.open(), start=1):
        value = json.loads(line)
        if not isinstance(value, dict) or set(value) != {"level_params", "module", "name", "type", "type_repr"}:
            raise CandidateError(f"statement source row {number} is not statement-only")
        name = value.get("name")
        if not isinstance(name, str) or (previous and name <= previous):
            raise CandidateError(f"statement source row {number} is duplicate or out of order")
        previous = name
        rows.append(value)
    return rows


def rejection_reason(row: dict[str, Any], policy: dict[str, Any]) -> str | None:
    exclusions = policy["exclusions"]
    name = row["name"]
    segments = name.split(".")
    if any(segment.startswith(tuple(exclusions["name_segment_prefixes"])) for segment in segments):
        return "generated-name-segment"
    if any(value in name for value in exclusions["name_substrings"]):
        return "generated-name-substring"
    if any(value in row["type"] for value in exclusions["type_substrings"]):
        return "unstable-pretty-type"
    if len(row["type_repr"].encode()) > policy["maximum_type_repr_bytes"]:
        return "structural-type-too-large"
    return None


def build_candidates(
    rows: list[dict[str, Any]], source: dict[str, Any], policy: dict[str, Any]
) -> dict[str, Any]:
    validate_inputs(source, policy)
    by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    rejected: dict[str, Counter[str]] = defaultdict(Counter)
    wanted = {family["module"] for family in policy["families"]}
    for row in rows:
        module = row["module"]
        if module not in wanted:
            continue
        reason = rejection_reason(row, policy)
        if reason is not None:
            rejected[module][reason] += 1
            continue
        constants = sorted(set(CONSTANT_RE.findall(row["type_repr"])))
        enriched = dict(row)
        enriched["type_constants"] = constants
        by_module[module].append(enriched)

    quota = policy["quota_per_family"]
    candidates: list[dict[str, Any]] = []
    family_rows: list[dict[str, Any]] = []
    for family in policy["families"]:
        module = family["module"]
        ranked = sorted(
            by_module[module],
            key=lambda row: (
                len(row["type_constants"]),
                len(row["type_repr"].encode()),
                row["name"],
            ),
        )
        if len(ranked) < quota:
            raise CandidateError(f"{module} has only {len(ranked)} eligible rows for quota {quota}")
        selected = ranked[:quota]
        for rank, row in enumerate(selected, start=1):
            candidate = {
                "candidate_id": digest(
                    {
                        "source_manifest_sha256": source["manifest_sha256"],
                        "name": row["name"],
                        "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
                    }
                ),
                "name": row["name"],
                "module": module,
                "domain": family["domain"],
                "theme": family["theme"],
                "level_params": row["level_params"],
                "type": row["type"],
                "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
                "source_row_sha256": digest(row),
                "rank_within_family": rank,
                "shape": {
                    "distinct_type_constants": len(row["type_constants"]),
                    "type_repr_bytes": len(row["type_repr"].encode()),
                },
            }
            candidates.append(candidate)
        family_rows.append(
            {
                **family,
                "eligible": len(ranked),
                "selected": len(selected),
                "rejected": dict(sorted(rejected[module].items())),
            }
        )
    candidates.sort(key=lambda row: (row["module"], row["rank_within_family"], row["name"]))
    if len(candidates) != policy["candidate_count"] or len({row["candidate_id"] for row in candidates}) != len(candidates):
        raise CandidateError("candidate count or identity uniqueness failed")
    result: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-mathlib-statement-candidates",
        "state": "source-candidates-not-nursery-facts",
        "source_manifest_sha256": source["manifest_sha256"],
        "source_artifact_sha256": source["external_artifact"]["sha256"],
        "policy_sha256": digest(policy),
        "selection_authority": "statement-shape-only-no-axeyum-outcomes-no-proof-values",
        "coverage": {
            "source_records": len(rows),
            "candidate_count": len(candidates),
            "families": family_rows,
        },
        "candidates": candidates,
        "limitations": [
            "candidate rows are not fact-ledger entries",
            "dependencies and split components are not assigned",
            "route hypotheses and Axeyum reachability are not measured",
            "Mathlib theorem status and proof do not count as Axeyum construction",
        ],
    }
    result["candidates_sha256"] = digest(result)
    return result


def verify(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    unsigned = dict(actual)
    claimed = unsigned.pop("candidates_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise CandidateError("candidate artifact digest is invalid")
    if actual != expected:
        raise CandidateError("candidate artifact is stale or mutated")


def validate_committed(
    actual: dict[str, Any], source: dict[str, Any], policy: dict[str, Any]
) -> None:
    unsigned = dict(actual)
    claimed = unsigned.pop("candidates_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise CandidateError("candidate artifact digest is invalid")
    if (
        actual.get("schema_version") != 1
        or actual.get("kind") != "axeyum-autogenesis-mathlib-statement-candidates"
        or actual.get("state") != "source-candidates-not-nursery-facts"
        or actual.get("source_manifest_sha256") != source["manifest_sha256"]
        or actual.get("source_artifact_sha256")
        != source["external_artifact"]["sha256"]
        or actual.get("policy_sha256") != digest(policy)
        or actual.get("selection_authority")
        != "statement-shape-only-no-axeyum-outcomes-no-proof-values"
    ):
        raise CandidateError("candidate artifact authority or source binding is invalid")
    candidates = actual.get("candidates")
    if not isinstance(candidates, list) or len(candidates) != policy["candidate_count"]:
        raise CandidateError("candidate artifact has the wrong population size")
    if len({row.get("candidate_id") for row in candidates if isinstance(row, dict)}) != len(candidates):
        raise CandidateError("candidate artifact identities are malformed or duplicate")
    expected_modules = {family["module"] for family in policy["families"]}
    counts = Counter(row.get("module") for row in candidates if isinstance(row, dict))
    if set(counts) != expected_modules or any(
        counts[module] != policy["quota_per_family"] for module in expected_modules
    ):
        raise CandidateError("candidate artifact family quotas changed")
    ordering = [
        (row["module"], row["rank_within_family"], row["name"])
        for row in candidates
    ]
    if ordering != sorted(ordering):
        raise CandidateError("candidate artifact ordering changed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--json", action="store_true")
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        source = load_object(SOURCE_MANIFEST)
        policy = load_object(POLICY)
        artifact = source["external_artifact"]
        input_path = args.input or pathlib.Path(artifact["storage_root"]) / artifact["file"]
        if args.check:
            actual = load_object(COMMITTED)
            validate_committed(actual, source, policy)
            storage = pathlib.Path(artifact["storage_root"])
            if input_path.is_file():
                rows = load_rows(input_path, artifact["sha256"])
                result = build_candidates(rows, source, policy)
                verify(actual, result)
                external = "verified"
            elif storage.exists():
                raise CandidateError(
                    "external storage is mounted but the statement source is absent"
                )
            else:
                result = actual
                external = "unavailable"
            print(
                "AUTOGENESIS_MATHLIB_CANDIDATES_OK|"
                f"{result['candidates_sha256']}|candidates={len(result['candidates'])}|"
                f"families={len(result['coverage']['families'])}|external={external}"
            )
            return 0
        rows = load_rows(input_path, artifact["sha256"])
        result = build_candidates(rows, source, policy)
        if args.json:
            print(json.dumps(result, indent=2, sort_keys=True))
        elif args.output is not None:
            output = args.output.resolve()
            if output.exists():
                raise CandidateError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_MATHLIB_CANDIDATES_OK|{result['candidates_sha256']}|output={output}")
    except (OSError, json.JSONDecodeError, CandidateError, KeyError) as error:
        print(f"autogenesis-mathlib-candidates: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
