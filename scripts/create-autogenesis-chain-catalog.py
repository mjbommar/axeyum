#!/usr/bin/env python3
"""Build or verify the proof-derived B -> A candidate catalog."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
DEPENDENCY_CHECKER = ROOT / "scripts/check-fact-depends-derived.py"


class ChainCatalogError(RuntimeError):
    """A proof-derived chain catalog cannot be constructed exactly."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def dependency_module():
    spec = importlib.util.spec_from_file_location(
        "depends_derived_for_autogenesis_chain_catalog", DEPENDENCY_CHECKER
    )
    if spec is None or spec.loader is None:
        raise ChainCatalogError(f"cannot load {DEPENDENCY_CHECKER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_facts() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        fact_id = fact.get("id")
        if not isinstance(fact_id, str) or fact_id in facts:
            raise ChainCatalogError(f"malformed or duplicate fact id in {path}")
        facts[fact_id] = fact
    return facts


def theorem_index(
    facts: dict[str, dict[str, Any]], theorem_of
) -> tuple[dict[str, str], list[str]]:
    by_theorem: dict[str, str] = {}
    unnamed: list[str] = []
    for fact_id, fact in sorted(facts.items()):
        if fact.get("proof_route") != "kernel-lean" or fact.get(
            "epistemic_status"
        ) not in {"proved", "computed"}:
            continue
        theorem = theorem_of(fact)
        if theorem is None:
            unnamed.append(fact_id)
            continue
        if theorem in by_theorem:
            raise ChainCatalogError(
                f"kernel theorem {theorem!r} maps to multiple fact rows"
            )
        by_theorem[theorem] = fact_id
    return by_theorem, unnamed


def build_catalog(
    facts: dict[str, dict[str, Any]],
    graph: dict[str, list[str]],
    theorem_of,
) -> dict[str, Any]:
    if len(graph) < 1:
        raise ChainCatalogError("kernel dependency inventory is empty")
    by_theorem, unnamed = theorem_index(facts, theorem_of)
    missing_inventory = sorted(
        by_theorem[theorem] for theorem in by_theorem if theorem not in graph
    )

    edges: list[tuple[str, str, str, str]] = []
    for consequent_theorem, consequent_id in sorted(by_theorem.items()):
        if consequent_theorem not in graph:
            continue
        declared = set(facts[consequent_id].get("depends_on") or [])
        for premise_theorem in sorted(set(graph[consequent_theorem])):
            premise_id = by_theorem.get(premise_theorem)
            if premise_id is None or premise_id == consequent_id:
                continue
            if premise_id not in declared:
                raise ChainCatalogError(
                    f"proof-derived edge {premise_id} -> {consequent_id} is absent from depends_on"
                )
            edges.append(
                (premise_id, consequent_id, premise_theorem, consequent_theorem)
            )
    if not edges:
        raise ChainCatalogError("kernel-lean subgraph has no proof-derived edge")

    parents: dict[str, list[str]] = {}
    for premise_id, consequent_id, _, _ in edges:
        parents.setdefault(consequent_id, []).append(premise_id)
    depth_cache: dict[str, int] = {}

    def depth(fact_id: str, active: tuple[str, ...] = ()) -> int:
        if fact_id in depth_cache:
            return depth_cache[fact_id]
        if fact_id in active:
            raise ChainCatalogError("proof-derived fact graph contains a cycle")
        value = 1 + max(
            (depth(parent, active + (fact_id,)) for parent in parents.get(fact_id, [])),
            default=0,
        )
        depth_cache[fact_id] = value
        return value

    candidates: list[dict[str, Any]] = []
    for premise_id, consequent_id, premise_theorem, consequent_theorem in edges:
        premise = facts[premise_id]
        consequent = facts[consequent_id]
        other_dependencies = sorted(
            dependency
            for dependency in consequent.get("depends_on") or []
            if dependency != premise_id
        )
        axiom_free = (
            premise.get("axiom_footprint") == []
            and consequent.get("axiom_footprint") == []
        )
        other_dependencies_established = all(
            dependency in facts
            and facts[dependency].get("epistemic_status")
            in {"axiom", "proved", "computed", "refuted"}
            for dependency in other_dependencies
        )
        candidate: dict[str, Any] = {
            "premise": {
                "fact_id": premise_id,
                "fact_sha256": digest(premise),
                "theorem": premise_theorem,
            },
            "consequent": {
                "fact_id": consequent_id,
                "fact_sha256": digest(consequent),
                "theorem": consequent_theorem,
                "other_dependencies": other_dependencies,
            },
            "proof_derived_direct_edge": True,
            "axiom_free": axiom_free,
            "counterfactual_last_missing_dependency": other_dependencies_established,
            "rank": {
                "other_dependency_count": len(other_dependencies),
                "consequent_depth": depth(consequent_id),
            },
            "qualification": {
                "state": "unmeasured",
                "requires_same_target_pre_b_no_credit": True,
                "requires_b_production": True,
                "requires_post_b_a_production_with_derived_dependency": True,
                "requires_proof_leakage_audit": True,
            },
        }
        candidate["chain_id"] = digest(
            {
                "premise_fact_id": premise_id,
                "consequent_fact_id": consequent_id,
                "premise_theorem": premise_theorem,
                "consequent_theorem": consequent_theorem,
            }
        )
        candidates.append(candidate)
    candidates.sort(
        key=lambda row: (
            not row["axiom_free"],
            not row["counterfactual_last_missing_dependency"],
            row["rank"]["other_dependency_count"],
            row["rank"]["consequent_depth"],
            row["consequent"]["fact_id"],
            row["premise"]["fact_id"],
        )
    )

    catalog: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-proof-derived-chain-catalog",
        "authority": {
            "fact_ledger_sha256": digest(
                [
                    {"fact_id": fact_id, "fact_sha256": digest(facts[fact_id])}
                    for fact_id in sorted(facts)
                ]
            ),
            "theorem_dependency_inventory_sha256": digest(graph),
        },
        "policy": {
            "routes": ["kernel-lean"],
            "edge_requirement": "direct-kernel-theorem-dependency-and-declared-fact-edge",
            "autonomous_selection_requires_qualification": True,
            "ranking": [
                "axiom-free-first",
                "all-other-dependencies-established-first",
                "fewest-other-dependencies",
                "shallowest-consequent",
                "lexicographic-fact-ids",
            ],
        },
        "coverage": {
            "fact_count": len(facts),
            "named_kernel_facts": len(by_theorem),
            "unnamed_kernel_fact_ids": unnamed,
            "missing_inventory_fact_ids": missing_inventory,
            "proof_derived_edges": len(candidates),
            "distinct_consequents": len(
                {row["consequent"]["fact_id"] for row in candidates}
            ),
            "axiom_free_edges": sum(row["axiom_free"] for row in candidates),
            "maximum_depth": max(depth_cache.values()),
        },
        "candidates": candidates,
        "selection": {
            "outcome": "refused-no-qualified-chain",
            "selected_chain_id": None,
            "reason": "structural candidates require operational qualification evidence",
        },
    }
    catalog["catalog_sha256"] = digest(catalog)
    return catalog


def verify_catalog(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    unsigned = dict(actual)
    claimed = unsigned.pop("catalog_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ChainCatalogError("chain catalog digest is missing or invalid")
    if actual != expected:
        raise ChainCatalogError("chain catalog is stale or mutated")


def parse_result(raw: Any, prefix: str) -> dict[str, str]:
    if not isinstance(raw, str):
        raise ChainCatalogError(f"{prefix} result is not text")
    fields = raw.split("|")
    if not fields or fields[0] != prefix:
        raise ChainCatalogError(f"{prefix} result has the wrong kind")
    parsed: dict[str, str] = {}
    for field in fields[1:]:
        key, separator, value = field.partition("=")
        if not separator or not key or key in parsed:
            raise ChainCatalogError(f"{prefix} result fields are malformed")
        parsed[key] = value
    return parsed


def load_json(root: pathlib.Path, relative: str) -> dict[str, Any]:
    value = json.loads((root / relative).read_text())
    if not isinstance(value, dict):
        raise ChainCatalogError(f"{relative} is not a JSON object")
    return value


def verify_addressed(value: dict[str, Any], field: str, label: str) -> str:
    unsigned = dict(value)
    claimed = unsigned.pop(field, None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ChainCatalogError(f"{label} digest is missing or invalid")
    return claimed


def apply_counterfactual_qualification(
    catalog: dict[str, Any], experiment_root: pathlib.Path
) -> dict[str, Any]:
    """Select one structural edge only after the retained two-search episode closes."""
    report = load_json(experiment_root, "experiment.json")
    snapshot = load_json(experiment_root, "snapshot.json")
    readiness = load_json(experiment_root, "readiness-delta.json")
    evidence = load_json(experiment_root, "premise-evidence.json")
    transaction = load_json(experiment_root, "fact-transaction-proposal.json")
    pre_catalog = load_json(experiment_root, "pre_a-catalog.json")
    post_catalog = load_json(experiment_root, "post_b-catalog.json")
    post_bundle = load_json(experiment_root, "post_b-output/apply-plans.json")

    report_sha = verify_addressed(report, "experiment_sha256", "experiment")
    snapshot_sha = verify_addressed(snapshot, "snapshot_sha256", "snapshot")
    readiness_sha = verify_addressed(
        readiness, "readiness_delta_sha256", "readiness delta"
    )
    evidence_sha = verify_addressed(evidence, "evidence_sha256", "premise evidence")
    transaction_sha = verify_addressed(
        transaction, "transaction_sha256", "fact transaction"
    )
    pre_catalog_sha = verify_addressed(pre_catalog, "catalog_sha256", "pre-A catalog")
    post_catalog_sha = verify_addressed(
        post_catalog, "catalog_sha256", "post-B catalog"
    )
    post_bundle_sha = verify_addressed(
        post_bundle, "bundle_sha256", "post-B proposal bundle"
    )
    if (
        report.get("schema_version") != 8
        or report.get("kind") != "axeyum-autogenesis-apply-experiment"
    ):
        raise ChainCatalogError("qualification artifact identity is invalid")
    if (
        report.get("snapshot_sha256") != snapshot_sha
        or (report.get("premise") or {}).get("evidence_sha256") != evidence_sha
        or (report.get("premise") or {}).get("readiness_delta_sha256")
        != readiness_sha
        or (report.get("premise") or {}).get("fact_transaction_sha256")
        != transaction_sha
        or (report.get("pre_a") or {}).get("catalog_sha256") != pre_catalog_sha
        or (report.get("post_b") or {}).get("catalog_sha256") != post_catalog_sha
        or (report.get("post_b") or {}).get("bundle_sha256") != post_bundle_sha
    ):
        raise ChainCatalogError("qualification report does not bind its artifacts")

    premise_id = report.get("premise_fact_id")
    consequent_id = report.get("target_fact_id")
    candidates = [
        row
        for row in catalog.get("candidates") or []
        if row["premise"]["fact_id"] == premise_id
        and row["consequent"]["fact_id"] == consequent_id
    ]
    if len(candidates) != 1:
        raise ChainCatalogError("qualification does not name one structural candidate")
    candidate = candidates[0]
    chain = snapshot.get("chain") or {}
    premise = chain.get("premise") or {}
    consequent = chain.get("consequent") or {}
    denied = sorted([premise.get("retained_theorem"), consequent.get("retained_theorem")])
    if (
        premise.get("fact_id") != premise_id
        or consequent.get("fact_id") != consequent_id
        or premise.get("retained_theorem") != candidate["premise"]["theorem"]
        or consequent.get("retained_theorem") != candidate["consequent"]["theorem"]
        or chain.get("derived_direct_edge")
        != f"{candidate['premise']['theorem']} -> {candidate['consequent']['theorem']}"
        or not all((snapshot.get("controls") or {}).values())
        or sorted((report.get("controls") or {}).get("denied_retained_answers") or [])
        != denied
        or (report.get("controls") or {}).get("proposer_isolated") is not True
        or (report.get("controls") or {}).get("expected_outcome_mismatch_rejected")
        is not True
        or (report.get("controls") or {}).get("after_fact_fault_recovered") is not True
        or report.get("same_target") is not True
    ):
        raise ChainCatalogError("qualification proof-leakage or chain controls failed")

    premise_result = parse_result(
        (report.get("premise") or {}).get("result"),
        "AUTOGENESIS_INDUCTION_RESULT",
    )
    pre_result = parse_result(
        (report.get("pre_a") or {}).get("result"), "AUTOGENESIS_APPLY_RESULT"
    )
    post_result = parse_result(
        (report.get("post_b") or {}).get("result"), "AUTOGENESIS_APPLY_RESULT"
    )
    accepted = ((snapshot.get("phases") or {}).get("post_b") or {}).get(
        "accepted_episode_facts"
    )
    episode_declaration = accepted[0].get("declaration") if isinstance(accepted, list) and len(accepted) == 1 else None
    if (
        premise_result.get("outcome") != "proved"
        or pre_result.get("phase") != "pre_a"
        or pre_result.get("outcome") != "no-proof"
        or pre_result.get("attempted") != pre_result.get("budget")
        or post_result.get("phase") != "post_b"
        or post_result.get("outcome") != "proved"
        or post_result.get("theorem") != episode_declaration
    ):
        raise ChainCatalogError("qualification does not prove the required B/no-A/then-A sequence")

    target = readiness.get("target") or {}
    if (
        readiness.get("newly_ready") != [consequent_id]
        or (readiness.get("cause") or {}).get("admitted_fact_id") != premise_id
        or (readiness.get("cause") or {}).get("derived_dependency_edge")
        != f"{premise_id} -> {consequent_id}"
        or target.get("fact_id") != consequent_id
        or (target.get("before") or {}).get("missing_dependencies") != [premise_id]
        or (target.get("after") or {}).get("eligible") is not True
        or readiness.get("authoritative_ledger_writes") != 0
        or readiness.get("fixture_writes") != 1
        or (evidence.get("identity") or {}).get("fact_id") != premise_id
        or (evidence.get("result") or {}).get("outcome") != "proved"
        or (evidence.get("acceptance") or {}).get("independent_kernel_checked")
        is not True
        or (evidence.get("acceptance") or {}).get("axiom_footprint") != []
        or (evidence.get("acceptance") or {}).get("retained_answer_dependencies")
        != []
        or (transaction.get("precondition") or {}).get("source_is_authoritative")
        is not False
    ):
        raise ChainCatalogError("qualification evidence, readiness, or fixture scope is invalid")
    plans = post_bundle.get("plans")
    if (
        (pre_catalog.get("target") or {}).get("source_fact_id") != consequent_id
        or pre_catalog.get("target") != post_catalog.get("target")
        or not isinstance(plans, list)
        or not plans
        or not isinstance(plans[0], dict)
        or plans[0].get("theorem") != episode_declaration
        or plans[0].get("catalog_origin") != "accepted-episode"
    ):
        raise ChainCatalogError("qualification target or accepted-premise plan changed")

    qualified = json.loads(json.dumps(catalog))
    structural_sha = qualified.pop("catalog_sha256")
    selected = next(
        row for row in qualified["candidates"] if row["chain_id"] == candidate["chain_id"]
    )
    selected["qualification"] = {
        "state": "qualified-counterfactual-fixture",
        "experiment_sha256": report_sha,
        "experiment_git_commit": report.get("git_commit"),
        "snapshot_sha256": snapshot_sha,
        "readiness_delta_sha256": readiness_sha,
        "premise_evidence_sha256": evidence_sha,
        "same_target_pre_b_no_credit": True,
        "b_produced_axiom_free": True,
        "post_b_a_produced_from_episode_b": True,
        "proof_leakage_controls_passed": True,
        "authoritative_write_authority": False,
    }
    qualified["selection"] = {
        "outcome": "selected-qualified-counterfactual-chain",
        "selected_chain_id": candidate["chain_id"],
        "structural_catalog_sha256": structural_sha,
        "qualification_experiment_sha256": report_sha,
        "authoritative_write_authority": False,
    }
    qualified["catalog_sha256"] = digest(qualified)
    return qualified


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qualification-experiment", type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check", action="store_true")
    action.add_argument("--json", action="store_true")
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        dependencies = dependency_module()
        graph = dependencies.inventory()
        if len(graph) < 100:
            raise ChainCatalogError(
                f"dependency inventory returned only {len(graph)} theorems"
            )
        catalog = build_catalog(load_facts(), graph, dependencies.theorem_of)
        if args.qualification_experiment is not None:
            catalog = apply_counterfactual_qualification(
                catalog, args.qualification_experiment.resolve()
            )
        if args.check:
            print(
                f"AUTOGENESIS_CHAIN_CATALOG_OK|{catalog['catalog_sha256']}|"
                f"edges={catalog['coverage']['proof_derived_edges']}|"
                f"consequents={catalog['coverage']['distinct_consequents']}|"
                f"missing_inventory={len(catalog['coverage']['missing_inventory_fact_ids'])}"
            )
        elif args.verify is not None:
            verify_catalog(json.loads(args.verify.read_text()), catalog)
            print(f"AUTOGENESIS_CHAIN_CATALOG_OK|{catalog['catalog_sha256']}")
        elif args.output is not None:
            output = args.output.resolve()
            if output.exists():
                raise ChainCatalogError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(catalog, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_CHAIN_CATALOG|{catalog['catalog_sha256']}|{output}")
        else:
            print(json.dumps(catalog, indent=2, sort_keys=True))
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        ChainCatalogError,
    ) as error:
        print(f"AUTOGENESIS_CHAIN_CATALOG_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
