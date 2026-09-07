#!/usr/bin/env python3
"""What ONE held-out family costs, as a number a brief consults BEFORE dispatch.

WHY THIS EXISTS
===============

Nine held-out families have been spent since 2026-08-22, and every one of them
was priced AFTER the fact, in an amendment that could only record the loss. Two
of the nine -- the two most recent, on 2026-09-03 and 2026-09-05 -- were spent
by a producer contract naming a held-out row as a NON-EXAMPLE. No proof was
attempted. No outcome was consulted. One id in a `non_examples` list, and the
whole family left the blind population irreversibly.

That is the cheapest possible breach and it costs the same as the most expensive
one, because the declared partition unit is
`whole-family-with-source-review-groups-indivisible`: a family is spent or it is
not, and there is no partial spend. A lane that knew the number beforehand would
not have paid it.

So this script prints the price. It is deliberately NOT a gate on whether a
family may be spent -- `check-autogenesis-holdout-isolation.py` and
`check-holdout-adjacency.py` already enforce that. It is the cost side, printed
in the units a brief is written in.

WHAT IT NEVER PRINTS
====================

A held-out fact id. Naming one, even as an example of what not to name, is
itself a citation, and a citation is what spends a family. The script reads the
ids to count them and asserts, before exiting, that none reached its own output.
Families are named; rows are counted.

METHOD
======

The held-out population is derived the same way
`check-autogenesis-holdout-isolation.py` derives it: every row carrying
`partition: "held-out"` in `nursery-v1.json` or `nursery-v2-extension.json`.
The total is then CROSS-CHECKED against that gate's own `held_out=` field by
running it, because a price computed from a population the enforcing gate does
not share is a price for a population nobody protects.

The spend history is the `amendments` array of
`mathlib-nursery-split-policy-v1.json`, which ADR-0542 made irreversible and
machine-enforced. Amendments are the authority over the manifests'
`family_partitions`: two families still carry `held-out` in the extension's
preregistration block and are `development` by amendment, and reading the
preregistration alone overcounts the blind population by two families.

Usage:
    python3 scripts/price-holdout-family.py
    python3 scripts/price-holdout-family.py --check    # gate
"""

from __future__ import annotations

import argparse
import collections
import datetime
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _input(env: str, default: pathlib.Path) -> pathlib.Path:
    value = os.environ.get(env)
    return pathlib.Path(value) if value else default


AUTOGEN = _input("AXEYUM_HOLDOUT_PRICE_AUTOGEN", ROOT / "artifacts/autogenesis")
# Redirectable for the control suite, which runs guard-deleted COPIES of this
# script from a scratch root -- where `ROOT` no longer points at the checkout and
# the gate would go missing for a reason that has nothing to do with the guard
# under test. That is not hypothetical: it made four of five guard deletions
# report the wrong control as dead until it was fixed.
ISOLATION_GATE = _input(
    "AXEYUM_HOLDOUT_PRICE_GATE",
    ROOT / "scripts/check-autogenesis-holdout-isolation.py",
)

MANIFESTS = ("nursery-v1.json", "nursery-v2-extension.json")
ROW_KEYS = ("entries", "facts", "rows")
HELD_OUT = "held-out"
# Any held-out id shape. The output is scanned for this before the script exits.
HELD_OUT_ID = re.compile(r"F:ml430-[a-z0-9-]+")

# Why each family left the blind population. Derived from the amendment
# `reason` text by keyword, and printed with its own coverage line, because the
# CAUSE mix is the actionable part: a brief can only avoid some of these.
CAUSES = (
    ("producer contract cited a row as a non-example", ("producer contract",)),
    ("an operation was registered against a held-out row", ("authoritative operation", "operation was registered")),
    ("rows were never blind: in-tree development predated the draw", ("never blind", "ordinary hand development")),
    ("rows were decided by the unblocking definition itself", ("unblocking definition", "decided by reduction", "closed evaluation")),
)


class Out:
    """Collects output so it can be checked for held-out ids before exit."""

    def __init__(self) -> None:
        self.lines: list[str] = []

    def __call__(self, line: str = "") -> None:
        self.lines.append(line)
        print(line)


def held_out_rows() -> dict[str, list[str]]:
    """family -> its held-out row ids, by the enforcing gate's own rule."""
    by_family: dict[str, list[str]] = collections.defaultdict(list)
    for name in MANIFESTS:
        path = AUTOGEN / name
        if not path.exists():
            continue
        data = json.loads(path.read_text())
        for key in ROW_KEYS:
            for entry in data.get(key, []) or []:
                if isinstance(entry, dict) and entry.get("partition") == HELD_OUT:
                    by_family[entry.get("family") or "<unfamilied>"].append(
                        entry.get("fact_id") or entry.get("id") or "<unidentified>"
                    )
    return dict(by_family)


def amendments() -> list[dict]:
    policy = AUTOGEN / "mathlib-nursery-split-policy-v1.json"
    if not policy.exists():
        return []
    return json.loads(policy.read_text()).get("amendments", []) or []


def gate_population() -> int | None:
    """`held_out=` as the ENFORCING gate reports it. Re-derived, not inherited."""
    if not ISOLATION_GATE.exists():
        return None
    try:
        proc = subprocess.run(
            [sys.executable, str(ISOLATION_GATE)],
            capture_output=True,
            text=True,
            timeout=300,
            cwd=ISOLATION_GATE.resolve().parents[1],
        )
    except (OSError, subprocess.SubprocessError):
        return None
    m = re.search(r"held_out=(\d+)", proc.stdout + proc.stderr)
    return int(m.group(1)) if m else None


def classify(reason: str) -> str:
    low = reason.lower()
    for label, keys in CAUSES:
        if any(k in low for k in keys):
            return label
    return "unclassified"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="gate: exit nonzero on a finding")
    args = ap.parse_args()
    out = Out()
    errors: list[str] = []

    rows = held_out_rows()
    sizes = {fam: len(ids) for fam, ids in rows.items()}
    n_families = len(sizes)
    n_rows = sum(sizes.values())
    amend = amendments()

    out("# The price of one held-out family")
    out()
    out("METHOD: held-out rows are every entry with `partition: \"held-out\"` in")
    out("        nursery-v1.json / nursery-v2-extension.json -- the same rule")
    out("        check-autogenesis-holdout-isolation.py enforces. Amendments in")
    out("        mathlib-nursery-split-policy-v1.json OVERRIDE the manifests'")
    out("        preregistered family_partitions. No held-out id is printed.")
    out()

    # ---- the population -------------------------------------------------
    out("## Blind population remaining")
    out()
    out(f"  families           {n_families:4d}")
    out(f"  rows               {n_rows:4d}")
    if sizes:
        ordered = sorted(sizes.values())
        median = ordered[len(ordered) // 2]
        out(f"  rows per family    min {min(ordered)}, median {median}, max {max(ordered)}")
    out()
    for fam, size in sorted(sizes.items()):
        out(f"    {size:4d}  {fam}")
    out()

    gate = gate_population()
    if gate is None:
        out("  CROSS-CHECK: the isolation gate did not run; population unverified.")
        errors.append(  # GUARD:gate-unavailable
            "could not re-derive held_out= from check-autogenesis-holdout-isolation.py: "  # GUARD:gate-unavailable
            "this price is for a population no gate was shown to share"  # GUARD:gate-unavailable
        )  # GUARD:gate-unavailable
    else:
        agree = gate == n_rows
        out(f"  CROSS-CHECK: isolation gate reports held_out={gate}; "
            f"this script derives {n_rows}  -> {'agree' if agree else 'DISAGREE'}")
        if not agree:  # GUARD:population-mismatch
            errors.append(  # GUARD:population-mismatch
                f"population disagreement: the enforcing gate protects {gate} rows, "  # GUARD:population-mismatch
                f"this price is computed over {n_rows}"  # GUARD:population-mismatch
            )  # GUARD:population-mismatch
    out()

    # ---- the spend history ----------------------------------------------
    out("## Spend history")
    out()
    spent_families = [a.get("family") for a in amend if a.get("from") == HELD_OUT]
    causes = collections.Counter(classify(str(a.get("reason", ""))) for a in amend)
    dates = sorted(str(a.get("date", "")) for a in amend if a.get("date"))
    out(f"  families spent     {len(spent_families):4d}")
    if len(dates) >= 2:
        try:
            first = datetime.date.fromisoformat(dates[0])
            last = datetime.date.fromisoformat(dates[-1])
            span = max((last - first).days, 1)
            rate = len(spent_families) / span
            out(f"  window             {dates[0]} .. {dates[-1]}  ({span} days)")
            out(f"  measured rate      {rate:.2f} families/day")
            if rate > 0:
                out(f"  runway             {n_families / rate:5.1f} days of blind "
                    "population left at that rate")
        except ValueError:
            pass
    out()
    out("  cause of each spend:")
    for label, _ in CAUSES:
        out(f"    {causes.get(label, 0):4d}  {label}")
    if causes.get("unclassified"):
        out(f"    {causes['unclassified']:4d}  unclassified (this script could not read the reason)")
    out()

    # ---- the price ------------------------------------------------------
    out("## THE PRICE OF ONE FAMILY")
    out()
    typical = sorted(sizes.values())[len(sizes) // 2] if sizes else 0
    out(f"  Spending one family costs {typical} propositions -- "
        f"{100.0 * typical / max(n_rows, 1):.1f}% of the rows and "
        f"{100.0 / max(n_families, 1):.1f}% of the families that remain.")
    out()
    out("  There is no partial spend. The declared partition unit is")
    out("  `whole-family-with-source-review-groups-indivisible`, so naming ONE row")
    out("  costs the SAME as proving all of them. Two of the nine spends to date")
    out("  were exactly this: an id in a producer contract's `non_examples` list,")
    out("  no proof attempted, whole family gone.")
    out()
    out("  The spend is IRREVERSIBLE and machine-enforced (ADR-0542). Assigning an")
    out("  amended family back to held-out is a generator error.")
    out()
    out("  What can never be claimed about a spent family, by anyone, afterwards:")
    for line in (
        "that the system closed a proposition it had never seen -- the family is",
        "  no longer evidence of generalization, only of capability;",
        "an unbiased estimate of producer coverage that includes its rows;",
        "a blind trial of any kind. One family is ONE independent trial, and the",
        "  trials are not replaceable: the catalog is a pinned Mathlib slice, so a",
        "  new family has to come from what is left of it, not from more sampling.",
    ):
        out(f"    - {line}" if not line.startswith("  ") else f"    {line}")
    out()
    out("  Before dispatching a lane that will write a producer contract, an")
    out("  operation, a fixture or an example: no held-out id may appear in it,")
    out("  including as a non-example. State the goal and the invariant; do not")
    out("  name the row.")
    out()

    # ---- guards ---------------------------------------------------------
    if n_families == 0:  # GUARD:empty-population
        errors.append(  # GUARD:empty-population
            "zero held-out families: the blind population is exhausted or this "  # GUARD:empty-population
            "script stopped seeing it, and the price would be vacuous"  # GUARD:empty-population
        )  # GUARD:empty-population
    for fam, size in sorted(sizes.items()):  # GUARD:empty-family
        if size == 0:  # GUARD:empty-family
            errors.append(f"held-out family `{fam}` has zero rows")  # GUARD:empty-family
    amended = {a.get("family") for a in amend if a.get("from") == HELD_OUT}
    recycled = sorted(amended & set(sizes))
    for fam in recycled:  # GUARD:recycled-family
        errors.append(  # GUARD:recycled-family
            f"family `{fam}` was amended OUT of held-out and is held-out again: "  # GUARD:recycled-family
            "a spent family cannot re-enter the blind population (ADR-0542)"  # GUARD:recycled-family
        )  # GUARD:recycled-family
    leaked = sorted({m for line in out.lines for m in HELD_OUT_ID.findall(line)})
    if leaked:  # GUARD:id-leak
        errors.append(  # GUARD:id-leak
            f"{len(leaked)} held-out fact id(s) reached this script's own output: "  # GUARD:id-leak
            "printing one is a citation, and a citation is what spends a family"  # GUARD:id-leak
        )  # GUARD:id-leak

    if errors:
        print("## Findings")
        print()
        for e in errors:
            print(f"  ERROR: {e}")
        print()
        return 1 if args.check else 0
    print("No findings.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
