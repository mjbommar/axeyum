#!/usr/bin/env python3
"""Generate the stable, cross-artifact baseline Autogenesis works from.

The committed baseline deliberately does not contain ``git rev-parse HEAD``.
A file cannot contain the identity of the commit that contains that file without
becoming self-referential.  Instead it content-identifies every authoritative
input.  ``--capture`` binds that stable source identity to an exact *clean*
commit when an experiment is launched.

This is an internal Phase-0 contract, not the public episode schema.  It makes
the assumptions behind Autogenesis-1 inspectable before an orchestrator exists.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parent.parent
FACTS = Path("artifacts/facts")
PROOF_GAP = Path("docs/plan/generated/proof-gap-matrix.json")
OUT_JSON = Path("docs/plan/generated/autogenesis-baseline.json")
OUT_MD = Path("docs/plan/generated/autogenesis-baseline.md")

STATIC_SOURCES = (
    Path("scripts/gen-autogenesis-baseline.py"),
    Path("scripts/create-autogenesis-snapshot.py"),
    Path("scripts/create-autogenesis-chain-catalog.py"),
    Path("scripts/create-autogenesis-proposer-catalog.py"),
    Path("scripts/autogenesis-apply-proposer.py"),
    Path("scripts/verify-autogenesis-apply-proposals.py"),
    Path("scripts/check-autogenesis-apply-search.sh"),
    Path("scripts/autogenesis-induction-proposer.py"),
    Path("scripts/verify-autogenesis-induction-proposals.py"),
    Path("scripts/check-autogenesis-induction-search.sh"),
    Path("scripts/create-autogenesis-premise-evidence.py"),
    Path("scripts/create-autogenesis-premise-transition.py"),
    Path("scripts/create-autogenesis-accepted-event.py"),
    Path("scripts/stage-autogenesis-premise.sh"),
    Path("scripts/replay-autogenesis-apply-experiment.sh"),
    Path("scripts/replay-autogenesis-authoritative-admission.sh"),
    Path("scripts/run-autogenesis-authoritative-chain.py"),
    Path("scripts/compare-autogenesis-authoritative-chains.py"),
    Path("scripts/check-autogenesis-1-result.py"),
    Path("scripts/prepare-autogenesis-fact-transaction.py"),
    Path("scripts/apply-autogenesis-fact-transaction.py"),
    Path("scripts/create-autogenesis-readiness-delta.py"),
    Path("scripts/stage-autogenesis-fixture-admission.sh"),
    Path("scripts/tests/fixtures/F-nat-zero-add-open.json"),
    Path("scripts/check-autogenesis-knowledge-controls.sh"),
    Path("scripts/check-autogenesis-proposer-isolation.sh"),
    Path("scripts/run-autogenesis-python-proposer.sh"),
    Path("scripts/tests/fixtures/autogenesis-proposer-probe.py"),
    Path("scripts/provision-fleet-host.sh"),
    Path("scripts/check-fact-dag.py"),
    Path("scripts/check-fact-depends-derived.py"),
    Path("scripts/fact-frontier.py"),
    Path("scripts/validate-autogenesis-operations.py"),
    Path("scripts/execute-autogenesis-operation.py"),
    Path("scripts/check-autogenesis-fact-operation.py"),
    Path("artifacts/autogenesis/operations.json"),
    Path("artifacts/autogenesis/autogenesis-1-result.json"),
    Path("artifacts/autogenesis/nursery-v1.json"),
    Path("scripts/check-autogenesis-nursery.py"),
    Path("scripts/check-autogenesis-mathlib-source.py"),
    Path("scripts/create-autogenesis-mathlib-candidates.py"),
    Path("scripts/lean/autogenesis_mathlib_statement_inventory.lean"),
    Path("artifacts/autogenesis/mathlib-statement-source-v1.json"),
    Path("artifacts/autogenesis/mathlib-nursery-source-policy-v1.json"),
    Path("artifacts/autogenesis/mathlib-nat-int-candidates-v1.json"),
    Path("scripts/close-fact.py"),
    Path("scripts/gen-proof-gap-matrix.py"),
    Path("artifacts/ontology/fact.schema.json"),
    Path("justfile"),
    Path("scripts/check.sh"),
    Path("scripts/check-aggregate-scope.expected"),
    Path("crates/axeyum-lean-kernel/examples/theorem_knowledge_audit.rs"),
    Path("crates/axeyum-lean-kernel/examples/autogenesis_apply_plan_check.rs"),
    Path("crates/axeyum-lean-kernel/examples/autogenesis_induction_plan_check.rs"),
    Path("crates/axeyum-lean-kernel/examples/autogenesis_support/mod.rs"),
)

SETTLED = {"axiom", "proved", "computed", "refuted"}
KERNEL_ROUTES = {"kernel-lean"}
THEOREM_RE = re.compile(
    r"\^?((?:Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded)\\?\.[A-Za-z0-9_']+)"
)

# A reviewed classification, but never an unsupported one: each row carries a
# source marker.  If the implementation stops saying the thing on which the
# classification rests, generation fails instead of preserving stale prose.
SEAMS = (
    {
        "id": "goal-selection",
        "state": "autogenesis-1-bootstrap",
        "owner": "fact frontier",
        "source": "scripts/fact-frontier.py",
        "marker": "content-addressed authoritative queue",
        "gap": "the frontier completed the credited B-to-A sequence; selection beyond exact preregistered operations remains ungeneralized",
    },
    {
        "id": "chain-qualification",
        "state": "autogenesis-1-bootstrap",
        "owner": "proof-derived chain catalog",
        "source": "scripts/create-autogenesis-chain-catalog.py",
        "marker": "authoritative_write_authority",
        "gap": "the Nat.zero_add to Nat.mul_one primary passed authoritatively; no fallback or held-out nursery chain is measured",
    },
    {
        "id": "route-dispatch",
        "state": "autogenesis-1-bootstrap",
        "owner": "operation registry",
        "source": "artifacts/autogenesis/operations.json",
        "marker": "smt-int-quadratic-negative-discriminant-v1",
        "gap": "the exact Nat.zero_add and event-bound Nat.mul_one drivers passed; a generic typed apply operation remains absent",
    },
    {
        "id": "operation-execution",
        "state": "autogenesis-1-bootstrap",
        "owner": "typed operation executor",
        "source": "scripts/execute-autogenesis-operation.py",
        "marker": "Callers supply none of",
        "gap": "the two Nat drivers reproduced normalized receipts; heterogeneous proof-plan execution remains absent",
    },
    {
        "id": "evidence-assembly",
        "state": "partial",
        "owner": "transactional closer",
        "source": "scripts/close-fact.py",
        "marker": "writing the evidence rows",
        "gap": "the first authoritative adapter derives its evidence row and route metadata; other routes through the manual closer remain caller-authored",
    },
    {
        "id": "checker-selection",
        "state": "partial",
        "owner": "evidence registry",
        "source": "artifacts/autogenesis/operations.json",
        "marker": "autogenesis-induction-plan-check-v1",
        "gap": "fixture and first authoritative checkers are typed; the manual closer still accepts caller-authored shell text",
    },
    {
        "id": "ledger-transition",
        "state": "authoritative-two-write",
        "owner": "transactional closer",
        "source": "scripts/apply-autogenesis-fact-transaction.py",
        "marker": "fact compare-and-swap precondition failed",
        "gap": "two sequential authoritative compare-and-swaps recovered from durable intents; a generic multi-step orchestrator remains deferred",
    },
    {
        "id": "dependency-derivation",
        "state": "partial",
        "owner": "kernel dependency inventory",
        "source": "scripts/check-fact-depends-derived.py",
        "marker": "Derive a kernel-route fact's `depends_on` from the proof term",
        "gap": "kernel facts are covered where checker commands name the theorem; other routes are authored",
    },
    {
        "id": "accepted-transition-event",
        "state": "autogenesis-1-bootstrap",
        "owner": "episode/orchestrator",
        "source": "scripts/create-autogenesis-readiness-delta.py",
        "marker": "durable admission event",
        "gap": "B's durable event triggered the credited A retry; retry policy beyond this exact operation remains absent",
    },
    {
        "id": "clean-replay",
        "state": "autogenesis-1-passed",
        "owner": "episode replay",
        "source": "scripts/run-autogenesis-authoritative-chain.py",
        "marker": "Run the credited Autogenesis B -> A acquisition",
        "gap": "the bootstrap chain reproduces byte-identically; held-out longitudinal replay and generalization remain",
    },
    {
        "id": "evaluation-population",
        "state": "foundation-only",
        "owner": "nursery manifest and readiness checker",
        "source": "scripts/check-autogenesis-nursery.py",
        "marker": "route_hypotheses_grant_no_dispatch_or_admission_authority",
        "gap": "Autogenesis-1 is frozen as a longitudinal regression, but the leakage-safe train, development, and held-out population has zero evaluation facts",
    },
    {
        "id": "nursery-statement-source",
        "state": "source-candidates",
        "owner": "proof-isolated Mathlib source and candidate selector",
        "source": "scripts/create-autogenesis-mathlib-candidates.py",
        "marker": "statement-shape-only-no-axeyum-outcomes-no-proof-values",
        "gap": "240 statement-only candidates span twelve Nat/Int families; dependency components, mutations, frozen splits, route hypotheses, and Axeyum outcomes remain absent",
    },
)


class BaselineError(RuntimeError):
    """The baseline cannot be derived without guessing."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def relative(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def load_facts(root: Path) -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    facts: dict[str, dict[str, Any]] = {}
    sources: list[dict[str, Any]] = []
    fact_dir = root / FACTS
    if not fact_dir.is_dir():
        raise BaselineError(f"missing fact directory: {fact_dir}")
    for path in sorted(fact_dir.glob("*.json")):
        raw = path.read_bytes()
        try:
            fact = json.loads(raw)
        except json.JSONDecodeError as error:
            raise BaselineError(f"{relative(root, path)}: invalid JSON: {error}") from error
        ident = fact.get("id")
        if not isinstance(ident, str) or not ident:
            raise BaselineError(f"{relative(root, path)}: missing fact id")
        if ident in facts:
            raise BaselineError(f"duplicate fact id {ident!r}")
        facts[ident] = fact
        sources.append(
            {"path": relative(root, path), "bytes": len(raw), "sha256": sha256_bytes(raw)}
        )
    if not facts:
        raise BaselineError("fact ledger is empty")
    return facts, sources


def graph_shape(facts: dict[str, dict[str, Any]], population: set[str]) -> dict[str, Any]:
    dangling: list[str] = []
    deps: dict[str, list[str]] = {}
    for ident in sorted(population):
        resolved = []
        for dependency in facts[ident].get("depends_on") or []:
            if dependency not in facts:
                dangling.append(f"{ident} -> {dependency}")
            elif dependency in population:
                resolved.append(dependency)
        deps[ident] = sorted(set(resolved))

    dependents: dict[str, list[str]] = defaultdict(list)
    for consequent, premises in deps.items():
        for premise in premises:
            dependents[premise].append(consequent)

    visiting: set[str] = set()
    depths: dict[str, int] = {}

    def depth(ident: str) -> int:
        if ident in depths:
            return depths[ident]
        if ident in visiting:
            raise BaselineError(f"dependency cycle reaches {ident}")
        visiting.add(ident)
        value = 1 + max((depth(other) for other in deps[ident]), default=0)
        visiting.remove(ident)
        depths[ident] = value
        return value

    for ident in sorted(population):
        depth(ident)
    edges = [
        {"premise": premise, "consequent": consequent}
        for consequent in sorted(deps)
        for premise in deps[consequent]
    ]
    isolated = [
        ident for ident in sorted(population) if not deps[ident] and not dependents[ident]
    ]
    return {
        "nodes": len(population),
        "edges": len(edges),
        "with_dependencies": sum(bool(deps[i]) for i in population),
        "with_dependents": sum(bool(dependents[i]) for i in population),
        "isolated": len(isolated),
        "max_depth": max(depths.values(), default=0),
        "depth_histogram": {
            str(key): value for key, value in sorted(Counter(depths.values()).items())
        },
        "dangling": sorted(dangling),
        "edges_detail": edges,
    }


def named_kernel_theorem(fact: dict[str, Any]) -> str | None:
    for evidence in fact.get("evidence") or []:
        found = THEOREM_RE.search(evidence.get("checker_command", ""))
        if found:
            return found.group(1).replace("\\", "")
    return None


def assurance_shape(facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    evidence = [row for fact in facts.values() for row in fact.get("evidence") or []]
    return {
        "evidence_rows": len(evidence),
        "check_statuses": dict(
            sorted(Counter(row.get("check_status", "(missing)") for row in evidence).items())
        ),
        "with_checker_command": sum(bool(row.get("checker_command")) for row in evidence),
        "with_multiple_named_checkers": sum(
            len(row.get("checkers") or []) >= 2 for row in evidence
        ),
        "axiom_free_kernel_facts": sum(
            fact.get("proof_route") == "kernel-lean"
            and fact.get("epistemic_status") == "proved"
            and fact.get("axiom_footprint") == []
            for fact in facts.values()
        ),
    }


def validate_seams(root: Path, seams: Iterable[dict[str, str]]) -> tuple[list[dict[str, str]], list[dict[str, Any]]]:
    rows: list[dict[str, str]] = []
    sources: dict[str, dict[str, Any]] = {}
    for seam in seams:
        path = root / seam["source"]
        if not path.is_file():
            raise BaselineError(f"{seam['id']}: missing seam source {seam['source']}")
        raw = path.read_bytes()
        if seam["marker"].encode() not in raw:
            raise BaselineError(
                f"{seam['id']}: source {seam['source']} no longer contains reviewed marker {seam['marker']!r}"
            )
        rows.append({key: seam[key] for key in ("id", "state", "owner", "source", "gap")})
        sources[seam["source"]] = {
            "path": seam["source"], "bytes": len(raw), "sha256": sha256_bytes(raw)
        }
    return rows, [sources[key] for key in sorted(sources)]


def load_proof_gap(root: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    path = root / PROOF_GAP
    if not path.is_file():
        raise BaselineError(f"missing generated proof-gap authority: {PROOF_GAP}")
    raw = path.read_bytes()
    data = json.loads(raw)
    summary = data.get("summary")
    if not isinstance(summary, dict) or not summary:
        raise BaselineError(f"{PROOF_GAP}: missing summary")
    return summary, {"path": PROOF_GAP.as_posix(), "bytes": len(raw), "sha256": sha256_bytes(raw)}


def static_sources(root: Path, paths: Iterable[Path] = STATIC_SOURCES) -> list[dict[str, Any]]:
    rows = []
    for relative_path in paths:
        path = root / relative_path
        if not path.is_file():
            raise BaselineError(f"missing baseline semantic source: {relative_path}")
        raw = path.read_bytes()
        rows.append(
            {"path": relative_path.as_posix(), "bytes": len(raw), "sha256": sha256_bytes(raw)}
        )
    return rows


def has_autogenesis1_result(root: Path) -> bool:
    path = root / "artifacts/autogenesis/autogenesis-1-result.json"
    if not path.is_file():
        return False
    value = json.loads(path.read_text(encoding="utf-8"))
    unsigned = dict(value)
    claimed = unsigned.pop("result_sha256", None)
    checks = value.get("reproduction", {}).get("checks", {})
    return bool(
        claimed == sha256_bytes(canonical_json(unsigned).encode())
        and value.get("verdict") == "autogenesis-1-passed"
        and checks
        and all(checks.values())
    )


def requirement_rows(
    kernel: dict[str, Any], seams: list[dict[str, str]], *, autogenesis1_passed: bool
) -> list[dict[str, str]]:
    seam_state = {row["id"]: row["state"] for row in seams}
    has_chain = kernel["edges"] > 0 and kernel["max_depth"] >= 2
    unsettled = kernel.get("unsettled", 0)
    chain_state = "missing"
    if has_chain:
        chain_state = "candidate" if unsettled else "replay-candidate"
    rows = [
        {
            "id": "A1-fixed-input-identity",
            "state": "fixture",
            "evidence": "the retained result binds one exact source, deterministic pre-B and pre-A state commits, registry, facts, statements, operations, and budgets",
            "next": "preserve this identity contract while generalizing beyond the bootstrap chain",
        },
        {
            "id": "A1-real-derived-chain",
            "state": seam_state.get("chain-qualification", chain_state),
            "evidence": "the proof-derived Nat.zero_add -> Nat.mul_one edge is now exercised by two authoritative writes and an episode-local kernel dependency",
            "next": "measure a fallback and build the held-out nursery without weakening primary-chain credit",
        },
        {
            "id": "A1-proof-leakage-boundary",
            "state": "fixture",
            "evidence": "proof-body-free catalog plus Bubblewrap repository/network isolation control",
            "next": "broaden the structural grammar while retaining the no-proof-body boundary",
        },
        {
            "id": "A1-operational-unlock-control",
            "state": "fixture",
            "evidence": "the same A target and budget fail before B, then B's durable event makes A ready and A proves only through the episode-local B",
            "next": "apply the same causal control to held-out multi-step chains",
        },
        {
            "id": "A1-machine-selection",
            "state": seam_state.get("goal-selection", "missing"),
            "evidence": "the content-addressed frontier selected B, then selected A only after B admission, and ended with no registered candidate",
            "next": "replace bootstrap exact operations only after a typed generic contract is exercised",
        },
        {
            "id": "A1-typed-dispatch-evidence",
            "state": seam_state.get("operation-execution", "missing"),
            "evidence": "the registry fixes SMT, exact Nat.zero_add, and event-bound Nat.mul_one routes; A reconstructs and applies only an episode-local B candidate",
            "next": "lift the exercised receipts into the Phase 3 proof-plan contract",
        },
        {
            "id": "A1-atomic-admission",
            "state": seam_state.get("ledger-transition", "missing"),
            "evidence": "both B and A stopped after durable intent, left their facts unchanged, and recovered through compare-and-swap to durable events",
            "next": "retain this boundary for every future multi-step admission",
        },
        {
            "id": "A1-admission-triggered-retry",
            "state": seam_state.get("accepted-transition-event", "missing"),
            "evidence": "the durable authoritative B event binds exact before/after frontiers and derives newly_ready=[F:nat-mul-one] with one authoritative write and zero fixture writes",
            "next": "generalize event-driven retry without granting status-only dispatch authority",
        },
        {
            "id": "A1-clean-reproduction",
            "state": seam_state.get("clean-replay", "missing"),
            "evidence": "two isolated runs from one exact source produced identical B and A receipts, events, state bundle, 56 artifact bytes, and semantic identity",
            "next": "keep this result as the longitudinal Phase 3 regression baseline",
        },
    ]
    if autogenesis1_passed:
        for row in rows:
            row["state"] = "passed"
    return rows


def build_report(
    root: Path = ROOT,
    seams: Iterable[dict[str, str]] = SEAMS,
    semantic_sources: Iterable[Path] = STATIC_SOURCES,
) -> dict[str, Any]:
    facts, fact_sources = load_facts(root)
    all_population = set(facts)
    kernel_population = {
        ident for ident, fact in facts.items() if fact.get("proof_route") in KERNEL_ROUTES
    }
    all_graph = graph_shape(facts, all_population)
    kernel_graph = graph_shape(facts, kernel_population)
    kernel_statuses = Counter(facts[ident].get("epistemic_status", "(missing)") for ident in kernel_population)
    kernel_graph["statuses"] = dict(sorted(kernel_statuses.items()))
    kernel_graph["unsettled"] = sum(
        facts[ident].get("epistemic_status") not in SETTLED for ident in kernel_population
    )
    named_kernel = {
        ident: named_kernel_theorem(facts[ident]) for ident in sorted(kernel_population)
    }
    seam_rows, seam_sources = validate_seams(root, seams)
    proof_gap, proof_gap_source = load_proof_gap(root)
    sources_by_path = {
        row["path"]: row
        for row in fact_sources + seam_sources + static_sources(root, semantic_sources) + [proof_gap_source]
    }
    source_rows = [sources_by_path[key] for key in sorted(sources_by_path)]
    source_digest = sha256_bytes(canonical_json(source_rows).encode())
    statuses = Counter(fact.get("epistemic_status", "(missing)") for fact in facts.values())
    routes = Counter(fact.get("proof_route", "(missing)") for fact in facts.values())
    return {
        "version": 0,
        "contract": "internal-autogenesis-phase0",
        "source_identity": {"algorithm": "sha256", "digest": source_digest, "inputs": source_rows},
        "ledger": {
            "facts": len(facts),
            "statuses": dict(sorted(statuses.items())),
            "routes": dict(sorted(routes.items())),
            "assurance": assurance_shape(facts),
            "dependency_graph": all_graph,
            "kernel_lean_graph": kernel_graph,
            "kernel_dependency_coverage": {
                "facts": len(kernel_population),
                "named": sum(name is not None for name in named_kernel.values()),
                "unnamed_fact_ids": [
                    ident for ident, name in named_kernel.items() if name is None
                ],
                "authority_gate": "scripts/check-fact-depends-derived.py",
            },
        },
        "proof_gap": proof_gap,
        "manual_seams": seam_rows,
        "autogenesis1_passed": has_autogenesis1_result(root),
        "autogenesis1_requirements": requirement_rows(
            kernel_graph,
            seam_rows,
            autogenesis1_passed=has_autogenesis1_result(root),
        ),
    }


def markdown(report: dict[str, Any]) -> str:
    ledger = report["ledger"]
    graph = ledger["dependency_graph"]
    kernel = ledger["kernel_lean_graph"]
    lines = [
        "# Generated Autogenesis baseline",
        "",
        "> Generated by `scripts/gen-autogenesis-baseline.py`. Do not hand-edit.",
        "> This is the stable Phase-0 source snapshot; an execution capture binds it",
        "> to an exact clean Git commit without creating a self-referential artifact.",
        "",
        f"Source identity: `sha256:{report['source_identity']['digest']}`",
        "",
        "## Ledger and chain substrate",
        "",
        "| Population | Facts | Edges | Isolated | Maximum depth |",
        "|---|---:|---:|---:|---:|",
        f"| All facts | {graph['nodes']} | {graph['edges']} | {graph['isolated']} | {graph['max_depth']} |",
        f"| `kernel-lean` | {kernel['nodes']} | {kernel['edges']} | {kernel['isolated']} | {kernel['max_depth']} |",
        "",
        "The kernel row is a candidate substrate, not by itself proof that an edge is an",
        "operational unlock. The committed Autogenesis-1 result supplies the credited",
        "pre-B counterfactual and repeated authoritative two-write acquisition.",
        f"The dependency gate can map **{ledger['kernel_dependency_coverage']['named']}** of",
        f"**{ledger['kernel_dependency_coverage']['facts']}** kernel facts to named theorems;",
        "the remaining facts stay explicit rather than being guessed.",
        "",
        "## Backward requirements",
        "",
        "| Requirement | State | Current evidence | Next falsifiable step |",
        "|---|---|---|---|",
    ]
    for row in report["autogenesis1_requirements"]:
        lines.append(f"| `{row['id']}` | {row['state']} | {row['evidence']} | {row['next']} |")
    lines.extend(
        [
            "",
            "## Manual seams",
            "",
            "| Seam | State | Owner | Gap | Source |",
            "|---|---|---|---|---|",
        ]
    )
    for row in report["manual_seams"]:
        lines.append(
            f"| `{row['id']}` | {row['state']} | {row['owner']} | {row['gap']} | `{row['source']}` |"
        )
    lines.extend(
        [
            "",
            "## Proof-production context",
            "",
            f"The current proof-gap authority covers **{report['proof_gap'].get('baseline_unsat', 0)}** baseline UNSAT instances,",
            f"of which **{report['proof_gap'].get('dominant_unsat', 0)}** satisfy the recorded dominance conditions.",
            "This is route evidence available to the programme, not autonomous-acquisition credit.",
            "",
        ]
    )
    return "\n".join(lines)


def render_json(report: dict[str, Any]) -> str:
    return json.dumps(report, indent=2, sort_keys=True) + "\n"


def check_or_write(
    root: Path,
    check: bool,
    seams: Iterable[dict[str, str]] = SEAMS,
    semantic_sources: Iterable[Path] = STATIC_SOURCES,
) -> int:
    report = build_report(root, seams, semantic_sources)
    outputs = {
        root / OUT_JSON: render_json(report),
        root / OUT_MD: markdown(report),
    }
    stale = []
    for path, expected in outputs.items():
        if check:
            actual = path.read_text(encoding="utf-8") if path.is_file() else None
            if actual != expected:
                stale.append(relative(root, path))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected, encoding="utf-8")
    if stale:
        print("autogenesis baseline is stale: " + ", ".join(stale), file=sys.stderr)
        return 1
    return 0


def capture(root: Path, destination: Path) -> int:
    if check_or_write(root, check=True):
        return 1
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=normal"],
        cwd=root, capture_output=True, text=True, check=True,
    ).stdout
    if status:
        print("refusing execution capture from a dirty checkout", file=sys.stderr)
        return 1
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True, check=True
    ).stdout.strip()
    report = build_report(root)
    record = {
        "version": 1,
        "git_commit": commit,
        "git_tree_clean": True,
        "baseline_source_sha256": report["source_identity"]["digest"],
        "baseline_artifact_sha256": sha256_file(root / OUT_JSON),
    }
    if destination.exists():
        print(f"refusing to overwrite execution capture: {destination}", file=sys.stderr)
        return 1
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(render_json(record), encoding="utf-8")
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--capture", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.capture is not None:
            return capture(ROOT, args.capture)
        return check_or_write(ROOT, args.check)
    except (BaselineError, OSError, subprocess.SubprocessError, json.JSONDecodeError) as error:
        print(f"autogenesis-baseline: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
