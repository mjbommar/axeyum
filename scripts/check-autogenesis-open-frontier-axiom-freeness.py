#!/usr/bin/env python3
"""Gate `artifacts/autogenesis/open-frontier-axiom-freeness-census-v1.json`.

The census answers ONE question with a measurement: for each open,
non-held-out ledger proposition that names a Mathlib source declaration, does
Mathlib's own proof of that declaration depend on an axiom?  It bounds the
*transport* route (reuse a Mathlib proof term) and nothing else -- an
axiom-bearing Mathlib proof does not mean no axiom-free proof exists, which the
`nat.modeq` family demonstrated by being closed axiom-free against lemmas that
all carry `propext`.

Every check below is written so the exit status depends on what the run FOUND,
not on the run completing.  In particular the population check derives the
expected set from the LEDGER, so the census cannot silently go stale while
reporting a healthy count, and the non-vacuity check refuses a census in which
nothing was measured as axiom-bearing -- the shape a broken `#print axioms`
parse would produce.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CENSUS = ROOT / "artifacts/autogenesis/open-frontier-axiom-freeness-census-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
FACTS = ROOT / "artifacts/facts"

TITLE = re.compile(r"source proposition ([A-Za-z0-9_.']+)")


def ledger_population() -> dict[str, str]:
    """Open, non-held-out facts naming a Mathlib source proposition."""
    partition = {
        entry["fact_id"]: entry.get("partition")
        for entry in json.loads(NURSERY.read_text())["entries"]
    }
    population: dict[str, str] = {}
    for path in sorted(FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        fact_id = fact.get("id")
        if not fact_id or fact.get("epistemic_status") != "open":
            continue
        if partition.get(fact_id) == "held-out":
            continue
        match = TITLE.search(fact.get("title", ""))
        if match:
            population[fact_id] = match.group(1)
    return population


def held_out_ids() -> set[str]:
    return {
        entry["fact_id"]
        for entry in json.loads(NURSERY.read_text())["entries"]
        if entry.get("partition") == "held-out"
    }


def check(census_path: Path) -> list[str]:
    failures: list[str] = []
    census = json.loads(census_path.read_text())
    rows = census["rows"]
    population = census["population"]
    known = {p.stem.replace("F-", "F:", 1) for p in FACTS.glob("*.json")}
    held_out = held_out_ids()

    # 1. every row names a fact that exists
    for row in rows:
        if row["fact_id"] not in known:
            failures.append(f"row names an absent fact: {row['fact_id']}")

    # 2. no row may name a held-out fact -- the partition, never the count
    for row in rows:
        if row["fact_id"] in held_out:
            failures.append(f"row names a HELD-OUT fact: {row['fact_id']}")

    # 3. the declared counts must equal the counts the rows carry
    resolved = [r for r in rows if r["resolved"]]
    free = [r for r in resolved if r["lean_axiom_footprint"] == []]
    observed = {
        "total": len(rows),
        "resolved_in_mathlib": len(resolved),
        "unresolved_in_mathlib": len(rows) - len(resolved),
        "axiom_free": len(free),
        "axiom_bearing": len(resolved) - len(free),
    }
    for key, value in observed.items():
        if population.get(key) != value:
            failures.append(f"population.{key}={population.get(key)} but rows say {value}")

    # 4. the named axiom-free declarations must be exactly the measured ones
    named = sorted(census["axiom_free_declarations"])
    measured = sorted(r["declaration"] for r in free)
    if named != measured:
        failures.append(f"axiom_free_declarations={named} but rows measure {measured}")

    # 5. the census must still COVER the ledger's open non-held-out population.
    #    Derived from the ledger, never from the census's own list, so a fact
    #    added to the frontier reds this gate instead of being silently absent.
    covered = {r["fact_id"] for r in rows}
    missing = sorted(set(ledger_population()) - covered)
    if missing:
        failures.append(f"{len(missing)} open non-held-out proposition(s) absent from the census: {missing[:5]}")

    # 6. non-vacuity: a census measuring nothing, or measuring everything as
    #    axiom-free, is what a broken `#print axioms` parse looks like.
    if not rows:
        failures.append("census carries no rows")
    if observed["axiom_bearing"] == 0:
        failures.append("no row was measured as axiom-bearing; the measurement did not discriminate")

    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--census", type=Path, default=CENSUS)
    args = parser.parse_args()
    if not args.census.exists():
        print(f"OPEN_FRONTIER_AXIOM_FREENESS|verdict=FAIL|reason=missing:{args.census}")
        return 1
    failures = check(args.census)
    census = json.loads(args.census.read_text())
    population = census["population"]
    if failures:
        for failure in failures:
            print(f"OPEN_FRONTIER_AXIOM_FREENESS_ERROR|{failure}")
        print(f"OPEN_FRONTIER_AXIOM_FREENESS|verdict=FAIL|failures={len(failures)}")
        return 1
    print(
        "OPEN_FRONTIER_AXIOM_FREENESS"
        f"|total={population['total']}"
        f"|resolved={population['resolved_in_mathlib']}"
        f"|axiom_bearing={population['axiom_bearing']}"
        f"|axiom_free={population['axiom_free']}"
        f"|unresolved={population['unresolved_in_mathlib']}"
        "|verdict=PASS"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
