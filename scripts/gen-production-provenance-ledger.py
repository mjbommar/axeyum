#!/usr/bin/env python3
"""Split established results by WHO established them, and ratchet generality.

`gen-theorem-production-ledger.py` answers "how much library exists" (418
theorems, all axiom-free). It deliberately does not answer the question this
programme actually claims, which
`docs/autogenesis/04-metrics-and-evaluation.md` states as *autonomous verified
yield*: results the system established with nobody writing the proof.

This ledger answers it, and the answer is currently zero.

The classification is DERIVED, never self-reported. A fact does not get to say
it was produced autonomously; the join is:

    fact.evidence[].checker_operation.id
        -> artifacts/autogenesis/operations.json
            -> applicability.fact_ids

and the discriminator is the LENGTH of that list. An operation naming exactly
one fact is a capsule: a proof route written for that theorem and no other. It
can admit a result through the autogenesis machinery and produce a receipt, and
it is still a person having written the proof. An operation naming more than one
fact is the weakest possible evidence of generality — not sufficient, but
necessary, and measurable today.

## The two ratchets

Both are currently **0**, and both are gated:

* `multi_target_operations` — operations whose applicability names >1 fact.
* `facts_via_multi_target` — established facts that came through one.

A rise in either is the result this programme exists to produce. They are gated
because without a gate the next single-target capsule lands, activity looks
high, and both numbers sit at zero indefinitely — which is what the four days
before this was written look like from the artifacts.

## Fail-closed

* An operation id on a fact that is not in the registry is an ERROR.
* A `proof_route` this script does not know is an ERROR, not an "other" bucket.
  "Fail on unknown provenance" is the requirement that stops the headline
  metric from quietly absorbing a new route.
* Zero established facts is an ERROR: this ledger would pass vacuously.

Usage:  python3 scripts/gen-production-provenance-ledger.py [--check]
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
LEDGER = ROOT / "docs/plan/generated/production-provenance-ledger.md"

SETTLED = {"proved", "computed"}

# Every route that may appear on a settled fact. A new route must be added here
# deliberately, with a decision about which trust story it belongs to.
KNOWN_ROUTES: dict[str, str] = {
    "kernel-lean": "kernel proof, reconstructed and checked here",
    "imported-kernel-lean": "kernel proof imported from an external development",
    "smt-term-level": "SMT decision with term-level evidence",
    "smt-clausal": "SMT decision with clausal (DRAT) evidence",
    "cas-certificate": "computer-algebra certificate",
    "search-certificate": "search certificate",
}

CAPSULE = "single-target operation (a capsule)"
GENERAL = "multi-target operation"
NO_OP = "no registered operation"


class ProvenanceError(Exception):
    pass


def load_facts() -> dict[str, dict[str, Any]]:
    facts = {}
    for path in sorted(FACTS.glob("*.json")):
        document = json.loads(path.read_text())
        facts[document["id"]] = document
    if not facts:
        raise ProvenanceError("no facts found; this ledger would pass vacuously")
    return facts


def operation_widths() -> dict[str, int]:
    registry = json.loads(OPERATIONS.read_text())["operations"]
    return {
        operation["id"]: len(operation["applicability"]["fact_ids"])
        for operation in registry
    }


def operation_ids(fact: dict[str, Any]) -> set[str]:
    found = set()
    for item in fact.get("evidence", []) or []:
        if not isinstance(item, dict):
            continue
        checker = item.get("checker_operation")
        if isinstance(checker, dict) and isinstance(checker.get("id"), str):
            found.add(checker["id"])
    return found


def classify(
    facts: dict[str, dict[str, Any]], widths: dict[str, int]
) -> dict[str, Any]:
    settled = {i: d for i, d in facts.items() if d["epistemic_status"] in SETTLED}
    if not settled:
        raise ProvenanceError("no settled facts; this ledger would pass vacuously")

    unknown = sorted({d["proof_route"] for d in settled.values()} - set(KNOWN_ROUTES))
    if unknown:
        raise ProvenanceError(
            f"unknown proof_route(s) {unknown}: add them to KNOWN_ROUTES with a "
            "decision about which trust story they belong to, rather than letting "
            "the headline metric absorb a route nobody classified"
        )

    generality: collections.Counter[str] = collections.Counter()
    by_route: dict[str, collections.Counter[str]] = collections.defaultdict(
        collections.Counter
    )
    via_general: list[str] = []
    for fact_id, fact in sorted(settled.items()):
        ids = operation_ids(fact)
        missing = sorted(ids - set(widths))
        if missing:
            raise ProvenanceError(
                f"{fact_id} names operation(s) {missing} that are not in the registry"
            )
        if not ids:
            label = NO_OP
        elif max(widths[i] for i in ids) > 1:
            label = GENERAL
            via_general.append(fact_id)
        else:
            label = CAPSULE
        generality[label] += 1
        by_route[fact["proof_route"]][label] += 1

    return {
        "settled": len(settled),
        "generality": generality,
        "by_route": by_route,
        "multi_target_operations": sum(1 for w in widths.values() if w > 1),
        "operations": len(widths),
        "facts_via_multi_target": sorted(via_general),
        "axiom_free": sum(1 for d in settled.values() if not d.get("axiom_footprint")),
    }


def render(report: dict[str, Any]) -> str:
    generality = report["generality"]
    lines = [
        "# Generated production provenance ledger",
        "",
        "> Generated by `scripts/gen-production-provenance-ledger.py`. Do not hand-edit.",
        "> Classification is derived from `applicability.fact_ids` in",
        "> `artifacts/autogenesis/operations.json`, never self-reported by a fact.",
        "",
        "## Autonomous verified yield",
        "",
        "| | |",
        "|---|---:|",
        f"| Established facts (`proved` or `computed`) | {report['settled']} |",
        f"| …via an operation covering **more than one** fact | "
        f"**{generality[GENERAL]}** |",
        f"| …via a single-target operation (a capsule) | {generality[CAPSULE]} |",
        f"| …with no registered operation (hand-constructed or imported) | "
        f"{generality[NO_OP]} |",
        f"| Registered operations | {report['operations']} |",
        f"| …covering more than one fact | **{report['multi_target_operations']}** |",
        "",
    ]
    if generality[GENERAL] == 0:
        lines += [
            "**The two bold numbers are the metric.** Both are zero. Every operation in",
            "the registry names exactly one fact, so every result it has produced came",
            "through a proof route written for that theorem and no other. That is a",
            "dispatch table, not a producer: it cannot fail to \"produce\", and it cannot",
            "produce anything nobody wrote.",
            "",
        ]
    else:
        lines += [
            f"**{generality[GENERAL]} fact(s) were established through an operation that",
            "covers more than one fact.** That is the first evidence of generality this",
            "ledger has ever recorded; it is necessary, not sufficient.",
            "",
            "Facts: " + ", ".join(f"`{i}`" for i in report["facts_via_multi_target"]),
            "",
        ]
    lines += [
        "## By route",
        "",
        "| Route | Multi-target | Capsule | No operation | Meaning |",
        "|---|---:|---:|---:|---|",
    ]
    for route, meaning in sorted(KNOWN_ROUTES.items()):
        counts = report["by_route"].get(route, collections.Counter())
        total = sum(counts.values())
        if not total:
            continue
        lines.append(
            f"| `{route}` | {counts[GENERAL]} | {counts[CAPSULE]} | "
            f"{counts[NO_OP]} | {meaning} |"
        )
    lines += [
        "",
        "## Reading a change",
        "",
        "- **Multi-target rising is the result.** It is the only number here that",
        "  distinguishes a producer from a person.",
        "- **Capsule rising is activity, not production.** It is worth recording and",
        "  it is not progress against this metric.",
        "- **No-operation rising** means hand-constructed or imported work, which is",
        "  how the preludes were built and is not autogenesis output at all.",
        "",
        "## What this does not say",
        "",
        "An operation covering two facts is not thereby *autonomous* — the bar in",
        "[`04-metrics-and-evaluation.md`](../../autogenesis/04-metrics-and-evaluation.md)",
        "is no proof-affecting intervention, which this join cannot see. Multi-target",
        "coverage is the **necessary** condition that is measurable today, and a",
        "single-target registry fails it without needing a harder test.",
        "",
        f"Of the {report['settled']} established facts, {report['axiom_free']} record an",
        "empty axiom footprint. That is a different axis from provenance: a",
        "hand-written proof can be axiom-free and a produced one need not be.",
        "",
    ]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        report = classify(load_facts(), operation_widths())
        rendered = render(report)
        if args.check:
            if not LEDGER.exists() or LEDGER.read_text() != rendered:
                raise ProvenanceError(
                    "ledger is stale; regenerate without --check. If "
                    "`facts_via_multi_target` rose, say so in the commit message — "
                    "it is the first generality this project has measured."
                )
        else:
            LEDGER.write_text(rendered)
        print(
            f"PRODUCTION_PROVENANCE|settled={report['settled']}|"
            f"via_multi_target={report['generality'][GENERAL]}|"
            f"via_capsule={report['generality'][CAPSULE]}|"
            f"no_operation={report['generality'][NO_OP]}|"
            f"multi_target_operations={report['multi_target_operations']}|"
            f"operations={report['operations']}"
        )
    except (OSError, KeyError, json.JSONDecodeError, ProvenanceError) as error:
        print(f"PRODUCTION_PROVENANCE_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
