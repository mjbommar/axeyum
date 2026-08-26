#!/usr/bin/env python3
"""Generate the mechanically authoritative lemma substrate for producers.

The kernel projection says which theorem terms were accepted and which other
theorems they directly reference. Fact records sometimes bind an evidence ID
of the form ``kernel-<declaration>`` or ``kernel:<declaration>`` to one of those
declarations. This generator joins only those exact identities. It never
matches names approximately and never claims that a linked theorem is
applicable to a goal.

The result is deliberately useful to an untrusted searcher: every theorem has
its direct prerequisites, reverse consumers, longest dependency depth, prelude
visibility, and exact fact links. A producer may rank or inspect these rows;
the kernel still decides whether any proposed application is valid.
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import pathlib
import sys
from collections import defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
KERNEL = ROOT / "artifacts/autogenesis/kernel-dependency-projection-v1.json"
FACTS = ROOT / "artifacts/facts"
OUTPUT = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json"


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_kernel_declarations(evidence: object) -> tuple[str, ...]:
    if not isinstance(evidence, dict):
        return ()
    explicit_many = evidence.get("kernel_declarations")
    if (
        isinstance(explicit_many, list)
        and explicit_many
        and all(isinstance(value, str) and value for value in explicit_many)
    ):
        return tuple(explicit_many)
    explicit = evidence.get("kernel_declaration")
    if isinstance(explicit, str) and explicit:
        return (explicit,)
    evidence_id = evidence.get("id")
    if not isinstance(evidence_id, str):
        return ()
    for prefix in ("kernel-", "kernel:"):
        if evidence_id.startswith(prefix):
            return (evidence_id[len(prefix) :],)
    return ()


def exact_kernel_declaration(evidence: object) -> str | None:
    """Compatibility helper for callers expecting at most one declaration."""
    declarations = exact_kernel_declarations(evidence)
    return declarations[0] if declarations else None


def build() -> dict[str, Any]:
    projection = json.loads(KERNEL.read_text())
    declaration_rows = {row["id"]: row for row in projection["declarations"]}
    theorem_rows = {
        row["id"]: row
        for row in projection["declarations"]
        if row["declaration_kind"] == "theorem"
    }
    if len(theorem_rows) != projection["census"]["theorems"]:
        raise ValueError("kernel theorem census disagrees with declaration rows")

    reverse: dict[str, set[str]] = defaultdict(set)
    for theorem, row in theorem_rows.items():
        for dependency in row["direct_theorem_dependencies"]:
            if dependency not in theorem_rows:
                raise ValueError(
                    f"theorem {theorem} names absent theorem dependency {dependency}"
                )
            reverse[dependency].add(theorem)

    visiting: set[str] = set()
    depths: dict[str, int] = {}

    def dependency_depth(theorem: str) -> int:
        prior = depths.get(theorem)
        if prior is not None:
            return prior
        if theorem in visiting:
            raise ValueError(f"theorem dependency cycle reaches {theorem}")
        visiting.add(theorem)
        dependencies = theorem_rows[theorem]["direct_theorem_dependencies"]
        depth = 0 if not dependencies else 1 + max(
            dependency_depth(dependency) for dependency in dependencies
        )
        visiting.remove(theorem)
        depths[theorem] = depth
        return depth

    fact_links: dict[str, set[str]] = defaultdict(set)
    unresolved: list[dict[str, str]] = []
    fact_paths = sorted(pathlib.Path(path) for path in glob.glob(str(FACTS / "F-*.json")))
    for path in fact_paths:
        fact = json.loads(path.read_text())
        fact_id = fact["id"]
        for evidence in fact.get("evidence", []):
            if evidence.get("kind") != "kernel-term":
                continue
            evidence_id = evidence.get("id")
            declarations = exact_kernel_declarations(evidence)
            if not declarations:
                continue
            for declaration in declarations:
                if declaration in theorem_rows:
                    fact_links[declaration].add(fact_id)
                else:
                    declaration_row = declaration_rows.get(declaration)
                    if declaration_row is None:
                        reason = "exact kernel evidence identity is absent from the current projection"
                    else:
                        declaration_kind = declaration_row["declaration_kind"]
                        reason = (
                            "exact kernel evidence identity resolves to a current "
                            f"{declaration_kind} declaration, not a theorem"
                        )
                    unresolved.append(
                        {
                            "fact_id": fact_id,
                            "evidence_id": str(evidence_id),
                            "candidate_declaration_id": declaration,
                            "reason": reason,
                        }
                    )

    unresolved.sort(
        key=lambda row: (row["candidate_declaration_id"], row["fact_id"], row["evidence_id"])
    )
    lemmas = []
    for theorem, row in sorted(theorem_rows.items()):
        dependents = sorted(reverse[theorem])
        linked_facts = sorted(fact_links[theorem])
        lemmas.append(
            {
                "kernel_declaration_id": theorem,
                "canonical_type": row["canonical_type"],
                "axiom_footprint_size": row["axiom_footprint_size"],
                "visible_in": row["visible_in"],
                "direct_type_dependencies": row["direct_type_dependencies"],
                "direct_declaration_dependencies": row["direct_declaration_dependencies"],
                "direct_theorem_dependencies": row["direct_theorem_dependencies"],
                "direct_theorem_dependents": dependents,
                "dependency_depth": dependency_depth(theorem),
                "exact_fact_ids": linked_facts,
                "search_authority": "candidate-only; kernel type checking remains authoritative",
            }
        )

    linked_theorems = sum(bool(row["exact_fact_ids"]) for row in lemmas)
    linked_facts = {fact for row in lemmas for fact in row["exact_fact_ids"]}
    unresolved_reasons = defaultdict(int)
    for row in unresolved:
        unresolved_reasons[row["reason"]] += 1
    return {
        "schema_version": 1,
        "kind": "axeyum-kernel-lemma-search-index",
        "derivation": {
            "kernel_projection_sha256": digest(KERNEL),
            "fact_population": "sorted artifacts/facts/F-*.json",
            "fact_identity_rule": "kernel-term evidence with explicit kernel_declarations or kernel_declaration, falling back for compatibility to an evidence id with exact kernel- or kernel: prefix and an exact current theorem suffix",
            "graph_semantics": "accepted theorem-term direct references; dependency depth is the longest direct-theorem path from a theorem with no theorem dependency",
            "trust_boundary": "search and retrieval only; no concept, applicability, proof, admission, or trusted-kernel authority",
        },
        "census": {
            "kernel_theorems": len(lemmas),
            "kernel_dependency_edges": sum(
                len(row["direct_theorem_dependencies"]) for row in lemmas
            ),
            "theorems_with_exact_fact_links": linked_theorems,
            "theorems_without_exact_fact_links": len(lemmas) - linked_theorems,
            "distinct_exactly_linked_facts": len(linked_facts),
            "unresolved_prefixed_kernel_evidence": len(unresolved),
            "unresolved_reason_counts": dict(sorted(unresolved_reasons.items())),
            "maximum_dependency_depth": max(depths.values(), default=0),
        },
        "lemmas": lemmas,
        "unresolved_prefixed_kernel_evidence": unresolved,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("AUTOGENESIS_KERNEL_LEMMA_INDEX_ERROR|index is stale", file=sys.stderr)
            return 1
    else:
        OUTPUT.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "AUTOGENESIS_KERNEL_LEMMA_INDEX|"
        f"theorems={census['kernel_theorems']}|"
        f"edges={census['kernel_dependency_edges']}|"
        f"linked_theorems={census['theorems_with_exact_fact_links']}|"
        f"linked_facts={census['distinct_exactly_linked_facts']}|"
        f"unresolved={census['unresolved_prefixed_kernel_evidence']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
