#!/usr/bin/env python3
"""Measure the fact ledger's dependency DAG — the flywheel's weakest arrow.

CLAUDE.md describes a cycle whose last step is *"the concept DAG and the fact
ledger say what to prove next"*. That step is `depends_on`: a fact becomes
workable when its dependencies are settled, so the ledger can hand out goals
without a person choosing them. Both of this lane's kernel proofs on 2026-08-16
were selected exactly that way.

Then `F:nat-euclid-lemma` was proved and **unlocked nothing** — no fact declares
it as a dependency. Measuring why, on 2026-08-17:

    108 facts
     26 (24%) declare depends_on
     27 (25%) have a dependent
     65 (60%) are ISOLATED — neither
     max chain depth 6, but 82 of 108 sit at depth 1

So the DAG is not a DAG so much as a pile. Proving a fact usually cannot make
another workable, because 60% of the ledger is disconnected, and the arrow that
is supposed to choose the next goal mostly has nothing to choose from.

This is not an argument for forcing every fact to declare a dependency. Plenty
genuinely have none in *this* ledger — an SMT-LIB refutation of the barber
sentence does not rest on a Nat lemma. It is an argument for the number being
visible and not getting worse, which is what the ratchet below does. A fact
added with no links is fine; the fraction of such facts creeping upward means
the self-extension loop is quietly losing its input.

Reported, never inferred: the counts come from resolving `depends_on` against
ids that actually exist in `artifacts/facts/`, so a dangling reference is
counted as absent rather than silently treated as a link.
"""

from __future__ import annotations

import json
import pathlib
import sys
from collections import Counter, defaultdict
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"

# The isolated FRACTION may not grow. A count would ratchet against adding
# facts at all, which is the opposite of the intent — the ledger should grow.
# Measured 0.602 on 2026-08-17; the slack is deliberate and small.
MAX_ISOLATED_FRACTION = 0.62
# A floor, so a loader that stops finding facts cannot report a healthy zero.
MIN_FACTS = 100


def load() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        facts[data["id"]] = data
    return facts


def shape(facts: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """Counts, plus the dangling references that would otherwise inflate them."""
    dangling: list[str] = []
    deps: dict[str, list[str]] = {}
    for ident, data in facts.items():
        resolved = []
        for other in data.get("depends_on") or []:
            if other in facts:
                resolved.append(other)
            else:
                dangling.append(f"{ident} -> {other}")
        deps[ident] = resolved

    dependents: dict[str, list[str]] = defaultdict(list)
    for ident, targets in deps.items():
        for target in targets:
            dependents[target].append(ident)

    depth_cache: dict[str, int] = {}

    def depth(ident: str, seen: frozenset[str] = frozenset()) -> int:
        if ident in depth_cache:
            return depth_cache[ident]
        if ident in seen:  # a cycle is a defect, not a depth
            return 0
        value = 1 + max(
            (depth(x, seen | {ident}) for x in deps[ident]), default=0
        )
        depth_cache[ident] = value
        return value

    depths = {ident: depth(ident) for ident in facts}
    isolated = [i for i in facts if not deps[i] and not dependents[i]]
    return {
        "facts": len(facts),
        "with_depends_on": sum(1 for i in deps if deps[i]),
        "with_dependents": sum(1 for i in facts if dependents[i]),
        "isolated": len(isolated),
        "max_depth": max(depths.values(), default=0),
        "depth_histogram": dict(sorted(Counter(depths.values()).items())),
        "dangling": sorted(dangling),
    }


def evaluate(stats: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if stats["facts"] < MIN_FACTS:
        failures.append(
            f"only {stats['facts']} facts loaded (floor {MIN_FACTS}); this check "
            "is looking at the wrong tree or has stopped parsing"
        )
        return failures
    if stats["dangling"]:
        failures.append(
            "depends_on names a fact that does not exist: "
            + ", ".join(stats["dangling"])
            + " -- a dangling edge is not a dependency, and counting it as one "
            "would overstate how connected the ledger is"
        )
    fraction = stats["isolated"] / stats["facts"]
    if fraction > MAX_ISOLATED_FRACTION:
        failures.append(
            f"{stats['isolated']} of {stats['facts']} facts ({fraction:.1%}) are "
            f"isolated, above the {MAX_ISOLATED_FRACTION:.0%} ratchet. The ledger "
            "is supposed to say what to prove next; a fact that neither rests on "
            "anything nor supports anything cannot participate in that, and the "
            "self-extension loop is losing its input"
        )
    return failures


def main(argv: list[str]) -> int:
    stats = shape(load())
    failures = evaluate(stats)
    if "--quiet" not in argv:
        print(f"  depth histogram: {stats['depth_histogram']}")
    print(
        "FACT_DAG|facts={facts}|with_depends_on={with_depends_on}|"
        "with_dependents={with_dependents}|isolated={isolated}|"
        "max_depth={max_depth}".format(**stats)
    )
    for failure in failures:
        print(f"FACT_DAG_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
