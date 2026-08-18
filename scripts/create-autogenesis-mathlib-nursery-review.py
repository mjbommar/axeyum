#!/usr/bin/env python3
"""Apply outcome-blind review and mutation grouping to Mathlib candidates."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
CANDIDATES = ROOT / "artifacts/autogenesis/mathlib-nat-int-candidates-v1.json"
COMPONENTS = ROOT / "artifacts/autogenesis/mathlib-nat-int-dependency-components-v1.json"
POLICY = ROOT / "artifacts/autogenesis/mathlib-nursery-review-policy-v1.json"
COMMITTED = ROOT / "artifacts/autogenesis/mathlib-nat-int-reviewed-nursery-v1.json"


class ReviewError(RuntimeError):
    """The outcome-blind review or its grouping contract is invalid."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load_object(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ReviewError(f"{path} is not a JSON object")
    return value


def verified_digest(value: dict[str, Any], field: str, label: str) -> None:
    unsigned = dict(value)
    claimed = unsigned.pop(field, None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ReviewError(f"{label} digest is missing or invalid")


def validate_inputs(candidates: dict[str, Any], components: dict[str, Any], policy: dict[str, Any]) -> None:
    verified_digest(candidates, "candidates_sha256", "candidate")
    verified_digest(components, "components_sha256", "dependency component")
    verified_digest(policy, "policy_sha256", "review policy")
    if policy.get("schema_version") != 1 or policy.get("kind") != "axeyum-autogenesis-mathlib-nursery-review-policy":
        raise ReviewError("review policy schema identity is invalid")
    if policy.get("candidate_set_sha256") != candidates.get("candidates_sha256"):
        raise ReviewError("review policy names a different candidate population")
    if policy.get("dependency_components_sha256") != components.get("components_sha256"):
        raise ReviewError("review policy names different dependency components")
    authority = policy.get("authority")
    if not isinstance(authority, dict) or not any("Axeyum outcomes" in value for value in authority.get("forbidden", [])):
        raise ReviewError("outcome-blind review authority is absent")
    if policy.get("state") != "review-authority-no-splits-no-outcomes":
        raise ReviewError("review policy state is invalid")


def build(candidates: dict[str, Any], components: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    validate_inputs(candidates, components, policy)
    candidate_rows = candidates.get("candidates")
    if not isinstance(candidate_rows, list) or not candidate_rows:
        raise ReviewError("candidate population is absent")
    by_name = {row.get("name"): row for row in candidate_rows if isinstance(row, dict)}
    if len(by_name) != len(candidate_rows):
        raise ReviewError("candidate names are malformed or duplicate")

    component_by_name: dict[str, str] = {}
    for component in components.get("components", []):
        component_id = component.get("component_id")
        for member in component.get("members", []):
            name = member.get("name")
            if name in component_by_name:
                raise ReviewError(f"candidate {name} occurs in multiple dependency components")
            component_by_name[name] = component_id
    if set(component_by_name) != set(by_name):
        raise ReviewError("dependency components do not cover the candidate population")

    disposition_by_name: dict[str, tuple[str, str]] = {}
    dispositions = policy.get("dispositions")
    if not isinstance(dispositions, dict):
        raise ReviewError("review dispositions are absent")
    for disposition, rule in dispositions.items():
        if not isinstance(rule, dict) or not isinstance(rule.get("reason"), str) or not isinstance(rule.get("names"), list):
            raise ReviewError(f"review disposition {disposition} is malformed")
        for name in rule["names"]:
            if name not in by_name:
                raise ReviewError(f"review disposition names unknown candidate {name}")
            if name in disposition_by_name:
                raise ReviewError(f"candidate {name} has multiple review dispositions")
            disposition_by_name[name] = (disposition, rule["reason"])

    default = policy.get("default_disposition")
    if default != "evaluation-eligible":
        raise ReviewError("review default must remain evaluation-eligible")
    reviewed = []
    for name in sorted(by_name):
        source = by_name[name]
        disposition, reason = disposition_by_name.get(
            name,
            (default, "retained by statement-only review; no proof or Axeyum outcome consulted"),
        )
        reviewed.append(
            {
                "candidate_id": source["candidate_id"],
                "dependency_component_id": component_by_name[name],
                "disposition": disposition,
                "domain": source["domain"],
                "module": source["module"],
                "name": name,
                "reason": reason,
                "statement": source["type"],
                "theme": source["theme"],
            }
        )

    mutations = []
    mutation_sources: set[str] = set()
    for mutation in policy.get("mutations", []):
        if not isinstance(mutation, dict) or set(mutation) != {"source", "class", "statement"}:
            raise ReviewError("mutation row has forbidden or missing fields")
        source_name = mutation["source"]
        if not isinstance(source_name, str) or not isinstance(mutation["class"], str) or not mutation["class"]:
            raise ReviewError("mutation source or class is malformed")
        source = by_name.get(source_name)
        if source is None:
            raise ReviewError(f"mutation names unknown source {source_name}")
        if disposition_by_name.get(source_name, (default, ""))[0] != default:
            raise ReviewError(f"mutation source {source_name} is not evaluation-eligible")
        if source_name in mutation_sources:
            raise ReviewError(f"mutation source {source_name} is duplicated")
        if not isinstance(mutation["statement"], str) or not mutation["statement"].strip() or mutation["statement"] == source["type"]:
            raise ReviewError(f"mutation for {source_name} is empty or unchanged")
        mutation_sources.add(source_name)
        identity = digest(
            {
                "source_candidate_id": source["candidate_id"],
                "class": mutation["class"],
                "statement": mutation["statement"],
            }
        )
        mutations.append(
            {
                "dependency_component_id": component_by_name[source_name],
                "domain": source["domain"],
                "mutation_class": mutation["class"],
                "mutation_id": f"M:{identity[:24]}",
                "source_candidate_id": source["candidate_id"],
                "source_name": source_name,
                "statement": mutation["statement"],
                "theme": source["theme"],
            }
        )
    mutations.sort(key=lambda row: row["source_name"])
    family_counts = Counter(row["theme"] for row in mutations)
    candidate_families = {row["theme"] for row in reviewed}
    if set(family_counts) != candidate_families or any(count != 1 for count in family_counts.values()):
        raise ReviewError("mutations must cover every candidate family exactly once")

    eligible = [row for row in reviewed if row["disposition"] == "evaluation-eligible"]
    groups: dict[str, dict[str, Any]] = {}
    for row in eligible:
        group = groups.setdefault(
            row["dependency_component_id"],
            {"dependency_component_id": row["dependency_component_id"], "candidate_names": [], "mutation_ids": []},
        )
        group["candidate_names"].append(row["name"])
    for row in mutations:
        groups[row["dependency_component_id"]]["mutation_ids"].append(row["mutation_id"])
    group_rows = sorted(groups.values(), key=lambda row: row["dependency_component_id"])
    for row in group_rows:
        row["candidate_names"].sort()
        row["mutation_ids"].sort()

    disposition_counts = Counter(row["disposition"] for row in reviewed)
    result: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-mathlib-reviewed-nursery-candidates",
        "state": "reviewed-groups-not-frozen-split",
        "candidate_set_sha256": candidates["candidates_sha256"],
        "dependency_components_sha256": components["components_sha256"],
        "review_policy_sha256": policy["policy_sha256"],
        "authority": "statement-and-dependency-metadata-only-no-proofs-no-axeyum-outcomes",
        "coverage": {
            "source_candidates": len(reviewed),
            "evaluation_eligible_candidates": len(eligible),
            "mutations": len(mutations),
            "future_evaluation_statements": len(eligible) + len(mutations),
            "review_groups": len(group_rows),
            "families": len(candidate_families),
            "disposition_counts": dict(sorted(disposition_counts.items())),
        },
        "reviewed_candidates": reviewed,
        "mutations": mutations,
        "review_groups": group_rows,
        "limitations": [
            "pretty-printed Mathlib statements are not yet Axeyum fact-ledger formal statements",
            "mutation truth values and all Axeyum outcomes remain unmeasured",
            "proof-shape risk labels and train/development/held-out partitions are not assigned",
            "review groups preserve direct dependency and mutation leakage only; family and proof-shape controls still apply",
        ],
    }
    result["review_sha256"] = digest(result)
    return result


def verify(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    verified_digest(actual, "review_sha256", "review")
    if actual != expected:
        raise ReviewError("committed review artifact is stale or mutated")
    if actual.get("state") != "reviewed-groups-not-frozen-split":
        raise ReviewError("review artifact falsely claims frozen splits")
    names = [row.get("name") for row in actual.get("reviewed_candidates", [])]
    if names != sorted(names) or len(names) != len(set(names)):
        raise ReviewError("reviewed candidates are duplicate or out of order")
    mutation_ids = [row.get("mutation_id") for row in actual.get("mutations", [])]
    if len(mutation_ids) != len(set(mutation_ids)):
        raise ReviewError("mutation identities are duplicate")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        candidates = load_object(CANDIDATES)
        components = load_object(COMPONENTS)
        policy = load_object(POLICY)
        expected = build(candidates, components, policy)
        if args.check:
            verify(load_object(COMMITTED), expected)
        else:
            COMMITTED.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
        print(
            "AUTOGENESIS_MATHLIB_REVIEW_OK|"
            f"{expected['review_sha256']}|eligible={expected['coverage']['evaluation_eligible_candidates']}|"
            f"mutations={expected['coverage']['mutations']}|groups={expected['coverage']['review_groups']}"
        )
    except (OSError, json.JSONDecodeError, ReviewError) as error:
        print(f"autogenesis-mathlib-review: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
