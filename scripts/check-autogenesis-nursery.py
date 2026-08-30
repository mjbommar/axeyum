#!/usr/bin/env python3
"""Validate the Autogenesis nursery and report leakage-safe evaluation readiness."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
NURSERY_V2 = ROOT / "artifacts/autogenesis/nursery-v2-extension.json"
FACTS = ROOT / "artifacts/facts"
RESULT = ROOT / "artifacts/autogenesis/autogenesis-1-result.json"

PARTITIONS = {"longitudinal", "train", "development", "held-out"}
EVALUATION_PARTITIONS = {"train", "development", "held-out"}
PROVENANCE_CLASSES = {
    "project-constructed",
    "external-transcribed",
    "generated-mutation",
    "imported-library",
}
ANSWER_ACCESS = {"withheld-during-episode", "unavailable"}


class NurseryError(RuntimeError):
    """The nursery contract or its derived report is invalid."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise NurseryError(f"{path.relative_to(ROOT)} is not a JSON object")
    return value


def load_facts(root: Path = FACTS) -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(root.glob("*.json")):
        fact = load_object(path)
        fact_id = fact.get("id")
        if not isinstance(fact_id, str) or fact_id in facts:
            raise NurseryError(f"malformed or duplicate fact id in {path}")
        facts[fact_id] = fact
    return facts


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise NurseryError(f"{label} must be a non-empty string")
    return value


def validate_policy(policy: Any) -> dict[str, Any]:
    if not isinstance(policy, dict):
        raise NurseryError("policy must be an object")
    expected_literals = {
        "admission_dependency_authority": "proof-derived-kernel-dependency",
        "family_leakage": "no-family-may-cross-evaluation-partitions",
        "proof_shape_leakage": "no-proof-shape-may-cross-evaluation-partitions",
        "source_group_leakage": "no-source-review-group-may-cross-evaluation-partitions",
        "split_component_authority": "declared-dependency-weak-component",
        "split_freeze": "before-target-outcomes",
        "split_leakage": "no-declared-component-may-cross-evaluation-partitions",
    }
    for key, expected in expected_literals.items():
        if policy.get(key) != expected:
            raise NurseryError(f"policy.{key} must be {expected!r}")
    count = policy.get("evaluation_fact_count")
    if not isinstance(count, dict) or count.get("minimum") != 100 or count.get("maximum") != 300:
        raise NurseryError("evaluation_fact_count must retain the 100..300 programme range")
    required = policy.get("required_evaluation_partitions")
    if required != ["train", "development", "held-out"]:
        raise NurseryError("required evaluation partitions changed or are unordered")
    for key in (
        "minimum_declared_dependency_depth",
        "minimum_held_out_components",
        "minimum_provenance_classes",
        "minimum_route_hypothesis_families",
        "minimum_statement_mutations",
    ):
        if not isinstance(policy.get(key), int) or policy[key] < 1:
            raise NurseryError(f"policy.{key} must be a positive integer")
    return policy


def validate_entries(
    raw: Any, facts: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    if not isinstance(raw, list) or not raw:
        raise NurseryError("entries must be a non-empty list")
    entries: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, entry in enumerate(raw):
        if not isinstance(entry, dict):
            raise NurseryError(f"entries[{index}] is not an object")
        fact_id = require_string(entry.get("fact_id"), f"entries[{index}].fact_id")
        if fact_id in seen:
            raise NurseryError(f"duplicate nursery fact {fact_id}")
        seen.add(fact_id)
        if fact_id not in facts:
            raise NurseryError(f"nursery fact {fact_id} is absent from the fact ledger")
        if entry.get("partition") not in PARTITIONS:
            raise NurseryError(f"{fact_id}: invalid partition")
        if entry.get("provenance_class") not in PROVENANCE_CLASSES:
            raise NurseryError(f"{fact_id}: invalid provenance class")
        require_string(entry.get("family"), f"{fact_id}.family")
        require_string(entry.get("proof_shape"), f"{fact_id}.proof_shape")
        require_string(entry.get("source_group"), f"{fact_id}.source_group")
        routes = entry.get("route_hypotheses")
        if (
            not isinstance(routes, list)
            or not routes
            or routes != sorted(set(routes))
            or not all(isinstance(route, str) and route for route in routes)
        ):
            raise NurseryError(f"{fact_id}: route hypotheses must be sorted and unique")
        mutation_of = entry.get("mutation_of")
        if mutation_of is not None and (
            not isinstance(mutation_of, str) or mutation_of == fact_id
        ):
            raise NurseryError(f"{fact_id}: invalid mutation_of")
        if entry.get("answer_access") not in ANSWER_ACCESS:
            raise NurseryError(f"{fact_id}: invalid answer_access")
        entries.append(entry)
    for entry in entries:
        mutation_of = entry.get("mutation_of")
        if mutation_of is not None and mutation_of not in seen:
            raise NurseryError(f"{entry['fact_id']}: mutation target is outside the nursery")
    by_id = {entry["fact_id"]: entry for entry in entries}
    for entry in entries:
        mutation_of = entry.get("mutation_of")
        is_generated = entry["provenance_class"] == "generated-mutation"
        if is_generated != (mutation_of is not None):
            raise NurseryError(
                f"{entry['fact_id']}: generated-mutation provenance and mutation_of must agree"
            )
        if mutation_of is not None:
            target = by_id[mutation_of]
            if (
                entry["partition"] != target["partition"]
                or entry["family"] != target["family"]
                or entry["source_group"] != target["source_group"]
            ):
                raise NurseryError(
                    f"{entry['fact_id']}: mutation must stay with its target partition, family, and source group"
                )
    return entries


def components(
    entries: list[dict[str, Any]], facts: dict[str, dict[str, Any]]
) -> tuple[dict[str, str], dict[str, list[str]]]:
    selected = {entry["fact_id"] for entry in entries}
    adjacency: dict[str, set[str]] = {fact_id: set() for fact_id in selected}
    for fact_id in selected:
        dependencies = facts[fact_id].get("depends_on") or []
        if not isinstance(dependencies, list):
            raise NurseryError(f"{fact_id}: depends_on is not a list")
        for dependency in dependencies:
            if dependency in selected:
                adjacency[fact_id].add(dependency)
                adjacency[dependency].add(fact_id)
    by_fact: dict[str, str] = {}
    members: dict[str, list[str]] = {}
    for start in sorted(selected):
        if start in by_fact:
            continue
        found: list[str] = []
        queue = deque([start])
        while queue:
            current = queue.popleft()
            if current in found:
                continue
            found.append(current)
            queue.extend(sorted(adjacency[current]))
        found.sort()
        component_id = digest(found)
        members[component_id] = found
        for fact_id in found:
            by_fact[fact_id] = component_id
    return by_fact, members


def describe_leak(
    header: str,
    key_label: str,
    keys: list[str],
    members_by_key: dict[str, list[str]],
    by_partition: dict[str, str],
    origin_of: dict[str, str] | None = None,
) -> str:
    """Render one violation as a header plus every member's fact id and partition.

    The gate used to raise a bare header with no way to act on it (measured
    2026-08-30: a single stderr line naming no component, fact, or partition,
    left un-actioned for at least a day because nobody could tell what it
    meant). Every caller of this function must pass the FULL membership it
    knows about -- for a declared-dependency component that means every
    member of the weakly connected component, not only the ones that
    triggered the cross-partition check, so a reader can see WHY a
    longitudinal or non-evaluation fact pulled two partitions together.

    `origin_of`, when given, additionally names which manifest file (`v1` or
    `v2`) declared each fact -- load-bearing for the cross-population check,
    where a crossing component's whole point is that its members did not all
    come from the same file.
    """
    lines = [header]
    for key in keys:
        member_ids = sorted(set(members_by_key.get(key, [])))
        partitions_seen = sorted({by_partition[fid] for fid in member_ids if fid in by_partition})
        display_key = key if len(key) <= 16 else f"{key[:12]}…"
        lines.append(f"  {key_label}={display_key} partitions={partitions_seen}")
        for fact_id in member_ids:
            suffix = f" [{origin_of[fact_id]}]" if origin_of and fact_id in origin_of else ""
            lines.append(f"    {fact_id} -> {by_partition.get(fact_id, 'unknown')}{suffix}")
    return "\n".join(lines)


def validate_exemptions(
    raw: Any, entries_by_id: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    """Validate declared, scoped exemptions from the component-split check.

    An exemption names an EXACT, closed set of fact ids -- never a component
    digest by itself, because a digest is opaque and a reviewer cannot tell
    what it covers without re-running the tool. The set must recompute (via
    `digest`) to the SAME component id the checker itself derives, so an
    exemption silently stops applying the moment the declared-dependency
    graph grows that component (a new nursery fact starts depending on one of
    its members): the gate then goes red again on the ENLARGED, unreviewed
    component, which is the fail-closed behaviour this mechanism exists to
    keep. This is deliberately not the amendment ledger (ADR-0542): an
    amendment MOVES a row between partitions and is irreversible history; an
    exemption changes nothing about any entry and stops applying automatically
    if the fact it covers changes shape.
    """
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise NurseryError("component_split_exemptions must be a list")
    exemptions: list[dict[str, Any]] = []
    seen_keys: set[str] = set()
    for index, item in enumerate(raw):
        if not isinstance(item, dict):
            raise NurseryError(f"component_split_exemptions[{index}] is not an object")
        fact_ids = item.get("component_fact_ids")
        if (
            not isinstance(fact_ids, list)
            or not fact_ids
            or fact_ids != sorted(set(fact_ids))
            or not all(isinstance(fid, str) and fid for fid in fact_ids)
        ):
            raise NurseryError(
                f"component_split_exemptions[{index}].component_fact_ids must be a "
                "sorted, deduplicated, non-empty list of strings"
            )
        for fact_id in fact_ids:
            if fact_id not in entries_by_id:
                raise NurseryError(
                    f"component_split_exemptions[{index}] names {fact_id}, "
                    "which is not a nursery entry"
                )
        require_string(item.get("reason"), f"component_split_exemptions[{index}].reason")
        require_string(item.get("authority"), f"component_split_exemptions[{index}].authority")
        require_string(item.get("date"), f"component_split_exemptions[{index}].date")
        component_id = digest(fact_ids)
        if component_id in seen_keys:
            raise NurseryError(
                f"component_split_exemptions[{index}] duplicates an already-exempted component"
            )
        seen_keys.add(component_id)
        exemptions.append({**item, "component_id": component_id, "component_fact_ids": fact_ids})
    return exemptions


def maximum_declared_depth(
    fact_ids: set[str], facts: dict[str, dict[str, Any]]
) -> int:
    memo: dict[str, int] = {}

    def visit(fact_id: str, active: tuple[str, ...] = ()) -> int:
        if fact_id in memo:
            return memo[fact_id]
        if fact_id in active:
            raise NurseryError("nursery declared dependency graph contains a cycle")
        parents = [
            dependency
            for dependency in facts[fact_id].get("depends_on") or []
            if dependency in fact_ids
        ]
        value = 1 + max(
            (visit(parent, active + (fact_id,)) for parent in parents), default=0
        )
        memo[fact_id] = value
        return value

    return max((visit(fact_id) for fact_id in sorted(fact_ids)), default=0)


def build_report(
    nursery: dict[str, Any], facts: dict[str, dict[str, Any]], result: dict[str, Any]
) -> dict[str, Any]:
    if nursery.get("schema_version") != 1 or nursery.get("kind") != "axeyum-autogenesis-nursery":
        raise NurseryError("nursery schema identity is invalid")
    if nursery.get("state") not in {"foundation-only", "frozen-evaluation"}:
        raise NurseryError("nursery state is invalid")
    if nursery.get("longitudinal_result") != "artifacts/autogenesis/autogenesis-1-result.json":
        raise NurseryError("longitudinal result path changed")
    if result.get("verdict") != "autogenesis-1-passed":
        raise NurseryError("longitudinal result is not a passed Autogenesis-1 result")
    policy = validate_policy(nursery.get("policy"))
    entries = validate_entries(nursery.get("entries"), facts)
    entries_by_id = {entry["fact_id"]: entry for entry in entries}
    by_partition_lookup = {entry["fact_id"]: entry["partition"] for entry in entries}
    exemptions = validate_exemptions(nursery.get("component_split_exemptions"), entries_by_id)
    exempted_component_ids = {exemption["component_id"] for exemption in exemptions}
    by_fact, component_members = components(entries, facts)
    by_partition = Counter(entry["partition"] for entry in entries)
    evaluation = [entry for entry in entries if entry["partition"] in EVALUATION_PARTITIONS]
    evaluation_ids = {entry["fact_id"] for entry in evaluation}
    component_partitions: dict[str, set[str]] = defaultdict(set)
    family_partitions: dict[str, set[str]] = defaultdict(set)
    shape_partitions: dict[str, set[str]] = defaultdict(set)
    source_group_partitions: dict[str, set[str]] = defaultdict(set)
    for entry in evaluation:
        component_partitions[by_fact[entry["fact_id"]]].add(entry["partition"])
        family_partitions[entry["family"]].add(entry["partition"])
        shape_partitions[entry["proof_shape"]].add(entry["partition"])
        source_group_partitions[entry["source_group"]].add(entry["partition"])

    all_leaking_components = sorted(
        component_id
        for component_id, partitions in component_partitions.items()
        if len(partitions) > 1
    )
    leaks = [c for c in all_leaking_components if c not in exempted_component_ids]
    leaks_exempted = [c for c in all_leaking_components if c in exempted_component_ids]
    family_leaks = sorted(
        family for family, partitions in family_partitions.items() if len(partitions) > 1
    )
    shape_leaks = sorted(
        shape for shape, partitions in shape_partitions.items() if len(partitions) > 1
    )
    source_group_leaks = sorted(
        group for group, partitions in source_group_partitions.items() if len(partitions) > 1
    )
    longitudinal_ids = sorted(
        entry["fact_id"] for entry in entries if entry["partition"] == "longitudinal"
    )
    if longitudinal_ids != ["F:nat-mul-one", "F:nat-zero-add"]:
        raise NurseryError("longitudinal partition must be exactly the Autogenesis-1 chain")
    longitudinal_components = {by_fact[fact_id] for fact_id in longitudinal_ids}
    all_longitudinal_overlap_components = sorted(
        c for c in longitudinal_components if c in {by_fact[e["fact_id"]] for e in evaluation}
    )
    longitudinal_overlap_components = [
        c for c in all_longitudinal_overlap_components if c not in exempted_component_ids
    ]
    longitudinal_overlap_components_exempted = [
        c for c in all_longitudinal_overlap_components if c in exempted_component_ids
    ]
    evaluation_longitudinal_overlap = sorted(
        entry["fact_id"]
        for entry in evaluation
        if by_fact[entry["fact_id"]] in longitudinal_overlap_components
    )
    evaluation_longitudinal_overlap_exempted = sorted(
        entry["fact_id"]
        for entry in evaluation
        if by_fact[entry["fact_id"]] in longitudinal_overlap_components_exempted
    )

    violation_blocks: list[str] = []
    if leaks:
        violation_blocks.append(
            describe_leak(
                "declared dependency component crosses evaluation partitions",
                "component",
                leaks,
                {c: component_members[c] for c in leaks},
                by_partition_lookup,
            )
        )
    if family_leaks:
        violation_blocks.append(
            describe_leak(
                "theorem family crosses evaluation partitions",
                "family",
                family_leaks,
                {
                    family: [e["fact_id"] for e in evaluation if e["family"] == family]
                    for family in family_leaks
                },
                by_partition_lookup,
            )
        )
    if shape_leaks:
        violation_blocks.append(
            describe_leak(
                "proof shape crosses evaluation partitions",
                "proof_shape",
                shape_leaks,
                {
                    shape: [e["fact_id"] for e in evaluation if e["proof_shape"] == shape]
                    for shape in shape_leaks
                },
                by_partition_lookup,
            )
        )
    if source_group_leaks:
        violation_blocks.append(
            describe_leak(
                "source review group crosses evaluation partitions",
                "source_group",
                source_group_leaks,
                {
                    group: [e["fact_id"] for e in evaluation if e["source_group"] == group]
                    for group in source_group_leaks
                },
                by_partition_lookup,
            )
        )
    if longitudinal_overlap_components:
        violation_blocks.append(
            describe_leak(
                f"evaluation population shares a component with Autogenesis-1 "
                f"(longitudinal={longitudinal_ids})",
                "component",
                longitudinal_overlap_components,
                {c: component_members[c] for c in longitudinal_overlap_components},
                by_partition_lookup,
            )
        )
    if violation_blocks:
        raise NurseryError(
            f"{len(violation_blocks)} partition-leak violation type(s) found:\n\n"
            + "\n\n".join(violation_blocks)
        )

    provenance_classes = sorted({entry["provenance_class"] for entry in evaluation})
    route_hypotheses = sorted(
        {route for entry in evaluation for route in entry["route_hypotheses"]}
    )
    mutations = sum(entry.get("mutation_of") is not None for entry in evaluation)
    held_out_components = {
        by_fact[entry["fact_id"]]
        for entry in evaluation
        if entry["partition"] == "held-out"
    }
    depth = maximum_declared_depth(evaluation_ids, facts)
    blockers: list[str] = []
    minimum = policy["evaluation_fact_count"]["minimum"]
    maximum = policy["evaluation_fact_count"]["maximum"]
    if not minimum <= len(evaluation) <= maximum:
        blockers.append(f"evaluation-fact-count:{len(evaluation)}-outside-{minimum}..{maximum}")
    for partition in policy["required_evaluation_partitions"]:
        if by_partition[partition] == 0:
            blockers.append(f"empty-partition:{partition}")
    if len(provenance_classes) < policy["minimum_provenance_classes"]:
        blockers.append(f"provenance-classes:{len(provenance_classes)}")
    if len(route_hypotheses) < policy["minimum_route_hypothesis_families"]:
        blockers.append(f"route-hypothesis-families:{len(route_hypotheses)}")
    if mutations < policy["minimum_statement_mutations"]:
        blockers.append(f"statement-mutations:{mutations}")
    if len(held_out_components) < policy["minimum_held_out_components"]:
        blockers.append(f"held-out-components:{len(held_out_components)}")
    if depth < policy["minimum_declared_dependency_depth"]:
        blockers.append(f"declared-dependency-depth:{depth}")
    report: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-nursery-readiness",
        "nursery_sha256": digest(nursery),
        "fact_ledger_sha256": digest(
            [{"fact_id": fact_id, "fact_sha256": digest(facts[fact_id])} for fact_id in sorted(facts)]
        ),
        "longitudinal": {
            "fact_ids": longitudinal_ids,
            "result_sha256": digest(result),
            "excluded_from_evaluation": True,
        },
        "population": {
            "all_entries": len(entries),
            "evaluation_entries": len(evaluation),
            "partitions": {key: by_partition[key] for key in sorted(PARTITIONS)},
            "declared_components": len(component_members),
            "held_out_components": len(held_out_components),
            "maximum_declared_dependency_depth": depth,
            "provenance_classes": provenance_classes,
            "route_hypothesis_families": route_hypotheses,
            "statement_mutations": mutations,
        },
        "controls": {
            "component_split_leaks": leaks,
            "family_split_leaks": family_leaks,
            "proof_shape_split_leaks": shape_leaks,
            "source_group_split_leaks": source_group_leaks,
            "evaluation_longitudinal_component_overlap": evaluation_longitudinal_overlap,
            "answer_access_values": sorted({entry["answer_access"] for entry in entries}),
            "admission_edges_require_proof_derivation": True,
            "route_hypotheses_grant_no_dispatch_or_admission_authority": True,
            "component_split_leaks_exempted": [
                {
                    "component_id": component_id,
                    "members": [
                        {"fact_id": fact_id, "partition": by_partition_lookup[fact_id]}
                        for fact_id in sorted(component_members[component_id])
                    ],
                }
                for component_id in leaks_exempted
            ],
            "evaluation_longitudinal_component_overlap_exempted": evaluation_longitudinal_overlap_exempted,
            "component_split_exemptions": exemptions,
            "component_split_exemptions_unused": [
                exemption
                for exemption in exemptions
                if exemption["component_id"]
                not in set(leaks_exempted) | set(longitudinal_overlap_components_exempted)
            ],
        },
        "ready": not blockers,
        "blockers": blockers,
    }
    if nursery["state"] == "foundation-only" and report["ready"]:
        raise NurseryError("foundation-only nursery unexpectedly satisfies readiness floors")
    if nursery["state"] == "frozen-evaluation" and not report["ready"]:
        raise NurseryError("frozen-evaluation nursery does not satisfy readiness floors")
    report["report_sha256"] = digest(report)
    return report


def build_cross_population_report(
    v1_nursery: dict[str, Any],
    v2_extension: dict[str, Any],
    facts: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    """Check declared-dependency component crossings over the UNION of
    nursery-v1's entries and nursery-v2-extension's entries.

    `build_report` above only ever sees `nursery-v1.json`. A weakly-connected
    declared-dependency component does not respect which manifest file its
    members happen to be listed in: a nursery-v2-extension entry can depend on
    a nursery-v1 entry (or vice versa) through a real fact-ledger `depends_on`
    edge, or two v2-only entries can already form a crossing component on
    their own, and NEITHER case is visible to a check that reads one file.
    Measured 2026-08-30 (see docs/plan/status/nursery-v2-component-coverage.md
    and ADR-0855): computing components over the union surfaces 3 crossings —
    one entirely within v2, one where v1's three ADR-0850-exempted components
    merge with two v2-internal ones via real cross-file dependency edges, and
    one visible ONLY in the union (invisible to either file alone).

    This performs the identical weak-component-vs-evaluation-partition check
    as `build_report`'s `component_split_leaks` / longitudinal-overlap checks,
    over entries drawn from BOTH files, with its own self-invalidating
    exemption list (`cross_population_component_split_exemptions`, read from
    `nursery-v2-extension.json` — see ADR-0850 for the mechanism this reuses
    verbatim via `validate_exemptions`). An exemption here names the exact
    closed fact-id set of a UNION component; if the live union graph later
    enlarges that component (a new dependency edge, from either file, pulls in
    another fact), the recomputed digest no longer matches and the gate goes
    red again on the enlarged, unreviewed component — the same fail-closed
    property ADR-0850 established, not a second mechanism.

    Does NOT touch `build_report`'s readiness/policy computation, which stays
    scoped to nursery-v1 alone (its `evaluation_fact_count` policy floor and
    friends govern v1's own 214-entry population, not this extension — see
    nursery-v2-extension.json's own `coverage.ceiling_authority`).
    """
    if v2_extension.get("kind") != "axeyum-autogenesis-nursery-extension":
        raise NurseryError("nursery-v2-extension schema identity is invalid")
    if v2_extension.get("extends") != "artifacts/autogenesis/nursery-v1.json":
        raise NurseryError("nursery-v2-extension no longer declares nursery-v1 as its base")

    v1_entries = validate_entries(v1_nursery.get("entries"), facts)
    v2_entries = validate_entries(v2_extension.get("entries"), facts)

    v1_ids = {entry["fact_id"] for entry in v1_entries}
    v2_ids = {entry["fact_id"] for entry in v2_entries}
    overlap = sorted(v1_ids & v2_ids)
    if overlap:
        raise NurseryError(
            "nursery-v1 and nursery-v2-extension declare overlapping fact ids: "
            + ", ".join(overlap)
        )

    entries = v1_entries + v2_entries
    entries_by_id = {entry["fact_id"]: entry for entry in entries}
    by_partition_lookup = {entry["fact_id"]: entry["partition"] for entry in entries}
    origin_of = {entry["fact_id"]: "v1" for entry in v1_entries}
    origin_of.update({entry["fact_id"]: "v2" for entry in v2_entries})

    exemptions = validate_exemptions(
        v2_extension.get("cross_population_component_split_exemptions"), entries_by_id
    )
    exempted_component_ids = {exemption["component_id"] for exemption in exemptions}

    by_fact, component_members = components(entries, facts)
    evaluation = [entry for entry in entries if entry["partition"] in EVALUATION_PARTITIONS]
    component_partitions: dict[str, set[str]] = defaultdict(set)
    for entry in evaluation:
        component_partitions[by_fact[entry["fact_id"]]].add(entry["partition"])
    all_leaking_components = sorted(
        component_id
        for component_id, partitions in component_partitions.items()
        if len(partitions) > 1
    )
    leaks = [c for c in all_leaking_components if c not in exempted_component_ids]
    leaks_exempted = [c for c in all_leaking_components if c in exempted_component_ids]

    longitudinal_ids = sorted(
        entry["fact_id"] for entry in v1_entries if entry["partition"] == "longitudinal"
    )
    longitudinal_components = {by_fact[fact_id] for fact_id in longitudinal_ids}
    evaluation_components = {by_fact[entry["fact_id"]] for entry in evaluation}
    all_longitudinal_overlap_components = sorted(longitudinal_components & evaluation_components)
    longitudinal_overlap_components = [
        c for c in all_longitudinal_overlap_components if c not in exempted_component_ids
    ]
    longitudinal_overlap_components_exempted = [
        c for c in all_longitudinal_overlap_components if c in exempted_component_ids
    ]
    evaluation_longitudinal_overlap = sorted(
        entry["fact_id"]
        for entry in evaluation
        if by_fact[entry["fact_id"]] in longitudinal_overlap_components
    )
    evaluation_longitudinal_overlap_exempted = sorted(
        entry["fact_id"]
        for entry in evaluation
        if by_fact[entry["fact_id"]] in longitudinal_overlap_components_exempted
    )

    violation_blocks: list[str] = []
    if leaks:
        violation_blocks.append(
            describe_leak(
                "declared dependency component crosses evaluation partitions "
                "(cross-population: nursery-v1 union nursery-v2-extension)",
                "component",
                leaks,
                {c: component_members[c] for c in leaks},
                by_partition_lookup,
                origin_of=origin_of,
            )
        )
    if longitudinal_overlap_components:
        violation_blocks.append(
            describe_leak(
                "cross-population evaluation union shares a component with "
                f"Autogenesis-1 (longitudinal={longitudinal_ids})",
                "component",
                longitudinal_overlap_components,
                {c: component_members[c] for c in longitudinal_overlap_components},
                by_partition_lookup,
                origin_of=origin_of,
            )
        )
    if violation_blocks:
        raise NurseryError(
            f"{len(violation_blocks)} cross-population partition-leak violation type(s) found:\n\n"
            + "\n\n".join(violation_blocks)
        )

    report: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-cross-population-report",
        "population": {
            "v1_entries": len(v1_entries),
            "v2_entries": len(v2_entries),
            "union_entries": len(entries),
            "union_declared_components": len(component_members),
        },
        "controls": {
            "component_split_leaks": leaks,
            "evaluation_longitudinal_component_overlap": evaluation_longitudinal_overlap,
            "component_split_leaks_exempted": [
                {
                    "component_id": component_id,
                    "members": [
                        {
                            "fact_id": fact_id,
                            "partition": by_partition_lookup[fact_id],
                            "origin": origin_of[fact_id],
                        }
                        for fact_id in sorted(component_members[component_id])
                    ],
                }
                for component_id in leaks_exempted
            ],
            "evaluation_longitudinal_component_overlap_exempted": (
                evaluation_longitudinal_overlap_exempted
            ),
            "cross_population_component_split_exemptions": exemptions,
            "cross_population_component_split_exemptions_unused": [
                exemption
                for exemption in exemptions
                if exemption["component_id"]
                not in set(leaks_exempted) | set(longitudinal_overlap_components_exempted)
            ],
        },
    }
    report["report_sha256"] = digest(report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args()
    try:
        facts = load_facts()
        report = build_report(load_object(NURSERY), facts, load_object(RESULT))
        cross_population_report = build_cross_population_report(
            load_object(NURSERY), load_object(NURSERY_V2), facts
        )
        if args.require_ready and not report["ready"]:
            raise NurseryError("nursery is not evaluation-ready: " + ", ".join(report["blockers"]))
        if args.json:
            print(json.dumps(report, indent=2, sort_keys=True))
            print(json.dumps(cross_population_report, indent=2, sort_keys=True))
        else:
            print(
                "AUTOGENESIS_NURSERY_OK|"
                f"{report['report_sha256']}|ready={str(report['ready']).lower()}|"
                f"evaluation={report['population']['evaluation_entries']}|"
                f"blockers={len(report['blockers'])}"
            )
            print(
                "AUTOGENESIS_NURSERY_CROSS_POPULATION_OK|"
                f"{cross_population_report['report_sha256']}|"
                f"v1={cross_population_report['population']['v1_entries']}|"
                f"v2={cross_population_report['population']['v2_entries']}|"
                f"components={cross_population_report['population']['union_declared_components']}"
            )
    except (OSError, json.JSONDecodeError, NurseryError) as error:
        print(f"autogenesis-nursery: {error}", file=__import__("sys").stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
