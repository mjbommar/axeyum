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
    Path("artifacts/autogenesis/operations.json"),
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
        "state": "partial",
        "owner": "fact frontier",
        "source": "scripts/fact-frontier.py",
        "marker": "content-addressed authoritative queue",
        "gap": "machine frontier selects one exact fact with an authoritative operation; no executor yet consumes that selection",
    },
    {
        "id": "route-dispatch",
        "state": "partial",
        "owner": "operation registry",
        "source": "artifacts/autogenesis/operations.json",
        "marker": "smt-int-quadratic-negative-discriminant-v1",
        "gap": "one authoritative producer/checker contract exists; typed execution and transaction preparation remain route-specific",
    },
    {
        "id": "evidence-assembly",
        "state": "manual",
        "owner": "transactional closer",
        "source": "scripts/close-fact.py",
        "marker": "writing the evidence rows",
        "gap": "the caller authors the evidence rows and route metadata",
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
        "state": "fixture",
        "owner": "transactional closer",
        "source": "scripts/apply-autogenesis-fact-transaction.py",
        "marker": "fact compare-and-swap precondition failed",
        "gap": "compare-and-swap plus roll-forward recovery is fixture-only; the first matching authoritative evidence lacks a typed transaction adapter",
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
        "state": "fixture",
        "owner": "episode/orchestrator",
        "source": "scripts/create-autogenesis-readiness-delta.py",
        "marker": "durable admission event",
        "gap": "durable fixture event triggers a counterfactual readiness delta; authoritative frontier consumption remains",
    },
    {
        "id": "clean-replay",
        "state": "fixture",
        "owner": "episode replay",
        "source": "scripts/replay-autogenesis-apply-experiment.sh",
        "marker": "Replay a retained Autogenesis apply experiment",
        "gap": "exact-commit fixture replay exists; authoritative acquisition replay remains",
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


def requirement_rows(kernel: dict[str, Any], seams: list[dict[str, str]]) -> list[dict[str, str]]:
    seam_state = {row["id"]: row["state"] for row in seams}
    has_chain = kernel["edges"] > 0 and kernel["max_depth"] >= 2
    unsettled = kernel.get("unsettled", 0)
    chain_state = "missing"
    if has_chain:
        chain_state = "candidate" if unsettled else "replay-candidate"
    return [
        {
            "id": "A1-fixed-input-identity",
            "state": "fixture",
            "evidence": "baseline source digest plus retained exact-clean-commit captures",
            "next": "bind the first authoritative acquisition to the same identity contract",
        },
        {
            "id": "A1-real-derived-chain",
            "state": chain_state,
            "evidence": (
                f"kernel ledger graph has {kernel['edges']} edges at depth {kernel['max_depth']} "
                f"and {unsettled} unsettled nodes"
            ),
            "next": "qualify a primary and fallback with proof-derived dependency and pre-B counterfactual",
        },
        {
            "id": "A1-proof-leakage-boundary",
            "state": "fixture",
            "evidence": "proof-body-free catalog plus Bubblewrap repository/network isolation control",
            "next": "broaden the structural grammar and bind plans into typed evidence",
        },
        {
            "id": "A1-operational-unlock-control",
            "state": "fixture",
            "evidence": "catalog search produces B; a durable fixture event makes the same A target ready and fresh A depends on B",
            "next": "repeat the causal unlock on an authoritative open fact",
        },
        {
            "id": "A1-machine-selection",
            "state": seam_state.get("goal-selection", "missing"),
            "evidence": "content-addressed authoritative frontier selects exactly one matching fact and refuses every unregistered candidate",
            "next": "execute only the selected registered operation and bind its result to the frontier identity",
        },
        {
            "id": "A1-typed-dispatch-evidence",
            "state": "partial",
            "evidence": "registry has fixture and authoritative producer/checker contracts; route-specific code can produce and recheck the authoritative certificate",
            "next": "add a typed executor and derive the authoritative evidence row and transaction without caller-authored shell",
        },
        {
            "id": "A1-atomic-admission",
            "state": seam_state.get("ledger-transition", "missing"),
            "evidence": "fixture fact admission has compare-and-swap, fsynced intent, durable event, and fault recovery",
            "next": "admit one genuinely open authoritative fact with matching typed evidence",
        },
        {
            "id": "A1-admission-triggered-retry",
            "state": seam_state.get("accepted-transition-event", "missing"),
            "evidence": "durable fixture admission event derives B-to-A readiness and gates the post-B catalog",
            "next": "generalize the readiness input from counterfactual snapshot to authoritative frontier state",
        },
        {
            "id": "A1-clean-reproduction",
            "state": seam_state.get("clean-replay", "missing"),
            "evidence": "retained exact-commit command regenerates B, transaction, event, readiness, pre-A failure, and post-B success",
            "next": "repeat the same replay for an authoritative acquisition",
        },
    ]


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
        "autogenesis1_requirements": requirement_rows(kernel_graph, seam_rows),
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
        "The kernel row is a candidate substrate, not proof that an edge is an",
        "operational unlock. Autogenesis-1 still requires the pre-B counterfactual.",
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
