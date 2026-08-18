#!/usr/bin/env python3
"""Create a content-addressed, proof-leakage-safe B -> A experiment snapshot.

This does not edit the authoritative fact ledger.  It derives a counterfactual
view in which the already-settled premise and consequent are unavailable both
as facts and as retained theorem proofs.  The post-B phase permits only the
newly admitted episode-local premise declaration, never the retained B theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = pathlib.Path("artifacts/facts")
BASELINE = pathlib.Path("docs/plan/generated/autogenesis-baseline.json")
THEOREM_RE = re.compile(
    r"\^?((?:Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded)\\?\.[A-Za-z0-9_']+)"
)


class SnapshotError(RuntimeError):
    """The requested counterfactual cannot be established without guessing."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def file_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_of(fact: dict[str, Any]) -> str | None:
    for evidence in fact.get("evidence") or []:
        match = THEOREM_RE.search(evidence.get("checker_command", ""))
        if match:
            return match.group(1).replace("\\", "")
    return None


def load_facts(root: pathlib.Path) -> tuple[dict[str, dict[str, Any]], dict[str, str]]:
    facts: dict[str, dict[str, Any]] = {}
    hashes: dict[str, str] = {}
    for path in sorted((root / FACTS).glob("*.json")):
        raw = path.read_bytes()
        fact = json.loads(raw)
        ident = fact.get("id")
        if not isinstance(ident, str) or not ident:
            raise SnapshotError(f"{path}: missing fact id")
        if ident in facts:
            raise SnapshotError(f"duplicate fact id {ident!r}")
        facts[ident] = fact
        hashes[ident] = hashlib.sha256(raw).hexdigest()
    return facts, hashes


def dependency_inventory(root: pathlib.Path) -> dict[str, list[str]]:
    process = subprocess.run(
        [
            "cargo",
            "run",
            "-q",
            "-p",
            "axeyum-lean-kernel",
            "--example",
            "theorem_dependency_inventory",
        ],
        cwd=root,
        capture_output=True,
        text=True,
        timeout=1800,
        check=True,
    )
    graph: dict[str, list[str]] = {}
    for line in process.stdout.splitlines():
        name, separator, raw_dependencies = line.partition("\t")
        if not separator:
            raise SnapshotError(f"malformed dependency inventory row: {line!r}")
        graph[name] = [item for item in raw_dependencies.split(",") if item]
    if len(graph) < 100:
        raise SnapshotError(
            f"dependency inventory returned only {len(graph)} theorems; refusing a vacuous snapshot"
        )
    return graph


def build_snapshot(
    *,
    premise_id: str,
    consequent_id: str,
    facts: dict[str, dict[str, Any]],
    fact_hashes: dict[str, str],
    graph: dict[str, list[str]],
    baseline: dict[str, Any],
    baseline_sha256: str,
) -> dict[str, Any]:
    try:
        premise = facts[premise_id]
        consequent = facts[consequent_id]
    except KeyError as error:
        raise SnapshotError(f"unknown fact {error.args[0]!r}") from error
    for ident, fact in ((premise_id, premise), (consequent_id, consequent)):
        if fact.get("proof_route") != "kernel-lean":
            raise SnapshotError(f"{ident}: proof route is not kernel-lean")
        if fact.get("epistemic_status") not in {"proved", "computed"}:
            raise SnapshotError(f"{ident}: fact is not settled replay material")

    premise_theorem = theorem_of(premise)
    consequent_theorem = theorem_of(consequent)
    if premise_theorem is None or consequent_theorem is None:
        raise SnapshotError("both facts must name their checked theorem")
    if premise_id not in set(consequent.get("depends_on") or []):
        raise SnapshotError(f"{consequent_id} does not declare dependency on {premise_id}")
    if premise_theorem not in graph.get(consequent_theorem, []):
        raise SnapshotError(
            f"kernel proof {consequent_theorem} does not directly reference {premise_theorem}"
        )

    settled_kernel = sorted(
        ident
        for ident, fact in facts.items()
        if fact.get("proof_route") == "kernel-lean"
        and fact.get("epistemic_status") in {"proved", "computed"}
    )
    retained_theorems = sorted(graph)
    withheld_facts = sorted([premise_id, consequent_id])
    withheld_theorems = sorted([premise_theorem, consequent_theorem])
    visible_facts = [ident for ident in settled_kernel if ident not in withheld_facts]
    visible_theorems = [name for name in retained_theorems if name not in withheld_theorems]

    identity = {
        "version": 1,
        "baseline_sha256": baseline_sha256,
        "baseline_source_sha256": baseline.get("source_sha256"),
        "facts": {
            "premise": {"id": premise_id, "sha256": fact_hashes[premise_id]},
            "consequent": {"id": consequent_id, "sha256": fact_hashes[consequent_id]},
        },
        "theorem_inventory_sha256": digest(graph),
    }
    episode_id = digest(identity)
    premise_candidate = f"Autogenesis.E{episode_id[:16]}.premise"
    consequent_candidate = f"Autogenesis.E{episode_id[:16]}.consequent"

    snapshot: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-counterfactual",
        "episode_id": episode_id,
        "identity": identity,
        "chain": {
            "premise": {"fact_id": premise_id, "retained_theorem": premise_theorem},
            "consequent": {
                "fact_id": consequent_id,
                "retained_theorem": consequent_theorem,
            },
            "derived_direct_edge": f"{premise_theorem} -> {consequent_theorem}",
        },
        "withheld": {
            "fact_ids": withheld_facts,
            "retained_theorems": withheld_theorems,
        },
        "phases": {
            "pre_b": {
                "visible_fact_ids": visible_facts,
                "visible_retained_theorems": visible_theorems,
                "denied_theorems": withheld_theorems,
                "target_candidate": premise_candidate,
            },
            "post_b": {
                "visible_fact_ids": visible_facts,
                "visible_retained_theorems": visible_theorems,
                "denied_theorems": withheld_theorems,
                "accepted_episode_facts": [
                    {
                        "role": "premise",
                        "source_fact_id": premise_id,
                        "declaration": premise_candidate,
                    }
                ],
                "required_dependencies": [premise_candidate],
                "target_candidate": consequent_candidate,
            },
        },
        "controls": {
            "same_search_policy_and_budget_pre_and_post_b": True,
            "audit_command": "cargo run -q -p axeyum-lean-kernel --example theorem_knowledge_audit",
            "pre_b_requires_no_credit": True,
            "post_b_requires_new_premise_dependency": True,
            "retained_fact_evidence_never_becomes_visible": True,
            "proposer_must_not_receive_retained_proof_bodies": True,
        },
    }
    snapshot["snapshot_sha256"] = digest(snapshot)
    return snapshot


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--premise", required=True, help="withheld B fact id")
    parser.add_argument("--consequent", required=True, help="withheld A fact id")
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    try:
        subprocess.run(
            [sys.executable, "scripts/gen-autogenesis-baseline.py", "--check"],
            cwd=ROOT,
            check=True,
        )
        output = args.output.resolve()
        if output.exists():
            raise SnapshotError(f"refusing to overwrite {output}")
        facts, fact_hashes = load_facts(ROOT)
        baseline_path = ROOT / BASELINE
        snapshot = build_snapshot(
            premise_id=args.premise,
            consequent_id=args.consequent,
            facts=facts,
            fact_hashes=fact_hashes,
            graph=dependency_inventory(ROOT),
            baseline=json.loads(baseline_path.read_text()),
            baseline_sha256=file_digest(baseline_path),
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(snapshot, indent=2, sort_keys=True) + "\n")
        print(f"AUTOGENESIS_SNAPSHOT|{snapshot['episode_id']}|{output}")
        return 0
    except (OSError, json.JSONDecodeError, subprocess.CalledProcessError, SnapshotError) as error:
        print(f"AUTOGENESIS_SNAPSHOT_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
