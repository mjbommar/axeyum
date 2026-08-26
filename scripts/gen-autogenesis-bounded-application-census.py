#!/usr/bin/env python3
"""Measure one proof-isolated bounded-application strategy over linked Nat goals."""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from axeyum import producers
from axeyum.kernel import Declaration, Kernel

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json"
FACTS = ROOT / "artifacts/facts"
OUTPUT = ROOT / "artifacts/autogenesis/bounded-application-proof-isolated-census-v1.json"
SEED_DECLARATIONS = ("Nat.monotone_of_le_succ",)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def build() -> dict[str, Any]:
    index = json.loads(INDEX.read_text())
    rows = {row["kernel_declaration_id"]: row for row in index["lemmas"]}
    facts = {}
    for path_text in glob.glob(str(FACTS / "F-*.json")):
        fact = json.loads(Path(path_text).read_text())
        facts[fact["id"]] = fact
    fact_to_lemmas: dict[str, list[str]] = {}
    for row in index["lemmas"]:
        for fact_id in row["exact_fact_ids"]:
            fact_to_lemmas.setdefault(fact_id, []).append(row["kernel_declaration_id"])
    for values in fact_to_lemmas.values():
        values.sort()

    kernel = Kernel()
    kernel.build_nat_prelude()
    outcomes = []
    for theorem, row in sorted(rows.items()):
        if "nat" not in row["visible_in"] or not row["exact_fact_ids"]:
            continue
        fact_id = row["exact_fact_ids"][0]
        fact = facts[fact_id]
        premise_fact_ids = sorted(fact.get("depends_on", []))
        premise_declarations = sorted(
            {
                declaration
                for dependency in premise_fact_ids
                for declaration in fact_to_lemmas.get(dependency, [])
            }
        )
        candidates = sorted(
            set(row["direct_type_dependencies"])
            | set(premise_declarations)
            | set(SEED_DECLARATIONS)
        )
        candidates = [
            name for name in candidates if name != theorem and kernel.contains(name)
        ]
        goal_declaration = kernel.get_declaration(theorem)
        if goal_declaration is None:
            raise RuntimeError(f"indexed Nat theorem is absent from the Nat kernel: {theorem}")
        try:
            candidate = producers.propose_bounded_application(
                kernel,
                goal_declaration.ty,
                [kernel.name(name, must_exist=True) for name in candidates],
            )
            admitted_name = kernel.name(
                f"Axeyum.Census.{theorem.replace('.', '_')}", must_exist=False
            )
            kernel.add_declaration(
                Declaration.theorem(
                    admitted_name, [], goal_declaration.ty, candidate.proof
                )
            )
            outcomes.append(
                {
                    "theorem": theorem,
                    "fact_id": fact_id,
                    "result": "accepted",
                    "premise_fact_ids": premise_fact_ids,
                    "premise_declarations": premise_declarations,
                    "candidate_declarations": candidates,
                    "binders_used": candidate.binders_used,
                    "application_depth": candidate.application_depth,
                    "terms_considered": candidate.terms_considered,
                    "proof_sha256": sha256_text(kernel.render_lean(candidate.proof)),
                    "axiom_footprint": kernel.axiom_footprint(admitted_name),
                    "theorem_dependencies": kernel.theorem_dependencies(admitted_name),
                }
            )
        except producers.Declined as decline:
            outcomes.append(
                {
                    "theorem": theorem,
                    "fact_id": fact_id,
                    "result": "declined",
                    "reason_kind": decline.reason.kind,
                    "premise_fact_ids": premise_fact_ids,
                    "premise_declarations": premise_declarations,
                    "candidate_declarations": candidates,
                }
            )

    accepted = [row for row in outcomes if row["result"] == "accepted"]
    decline_reasons = Counter(
        row["reason_kind"] for row in outcomes if row["result"] == "declined"
    )
    return {
        "schema_version": 1,
        "kind": "axeyum-bounded-application-proof-isolated-census",
        "strategy": {
            "population": "every fact-linked theorem visible in the constructed Nat prelude",
            "candidate_rule": "direct type dependencies plus exact authored fact dependencies plus fixed seed declarations",
            "seed_declarations": list(SEED_DECLARATIONS),
            "forbidden_inputs": [
                "target theorem proof value",
                "direct_declaration_dependencies",
                "direct_theorem_dependencies",
                "transitive declaration closure",
                "name or statement similarity",
            ],
            "authority": "candidate-only; every accepted term is separately admitted and measured",
        },
        "census": {
            "population": len(outcomes),
            "accepted": len(accepted),
            "declined": len(outcomes) - len(accepted),
            "conversion_percent": round(100 * len(accepted) / len(outcomes), 1),
            "decline_reasons": dict(sorted(decline_reasons.items())),
        },
        "accepted": accepted,
        "outcomes": outcomes,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("BOUNDED_APPLICATION_CENSUS_ERROR|artifact is stale")
            return 1
    else:
        OUTPUT.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "BOUNDED_APPLICATION_CENSUS|"
        f"population={census['population']}|accepted={census['accepted']}|"
        f"declined={census['declined']}|conversion_percent={census['conversion_percent']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
