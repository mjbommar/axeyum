#!/usr/bin/env python3
"""What to work on next, read off the fact ledger.

`validate-facts.py` says whether the ledger is *consistent*. This says what it is
*for*: the end-to-end path from an established foundation to a new result, with
the next move named at every point on it.

Until now nothing consumed `artifacts/facts/` except the validator, so "pick an
open fact whose dependencies are established and dispatch it" -- the loop the
schema is designed around -- existed only in somebody's head. A ledger nothing
selects from is a record, not a queue.

The four bands, in the order the flow runs:

  RESEARCH FRONTIER  open to us AND unsettled in the literature, dependencies
                     established. Genuinely new mathematics if closed. This is
                     the band the project exists to grow.
  IMPORT BACKLOG     open to us, settled elsewhere. Real work, but formalization
                     rather than discovery -- and it must NOT be confused with
                     the frontier, or the loop burns its queue re-deriving the
                     literature. That confusion is why `external_status` exists.
  BLOCKED            open, with dependencies not yet established. Prints what is
                     missing, because those dependencies are the actual next
                     task -- this is where "established foundation" turns into a
                     work order.
  ESTABLISHED HERE, NOT THERE   already closed by us and unsettled outside. The
                     output. Reported so the count is visible rather than
                     anecdotal.

How a fact could be attacked is reported separately from how interesting it is,
in three classes rather than two: DECIDABLE (a procedure we have terminates —
dispatch it), proof-route-only (quantified over an infinite domain, so only a
kernel proof can close it, and saying a route exists is not saying it is
feasible), and no route at all. Collapsing the first two is how a queue comes to
rank Goldbach's conjecture beside a finite colouring problem.

Usage:
    python3 scripts/fact-frontier.py            # the queue
    python3 scripts/fact-frontier.py --band research
    python3 scripts/fact-frontier.py --unlocks  # what each open fact would free
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"

# A status asserting we settled it. `axiom` counts: a dependency taken as an
# axiom is available to build on, whatever one thinks of taking it.
SETTLED = {"proved", "computed", "refuted", "axiom"}
# Unsettled in the wider literature. `None` cannot appear once the ledger is
# fully classified, but is treated as unknown rather than as an opportunity --
# an unclassified fact is an unchecked one, and guessing in the optimistic
# direction is how a backlog item gets mistaken for a discovery.
EXTERNAL_UNSETTLED = {"open", "conjectured"}

# How a fact could be attacked, which is NOT the same question as which fragment
# it is written in.
#
# The first version of this file conflated them: it held one DISPATCHABLE set
# containing both `QF_BV` and `Nat`, and so reported Goldbach's conjecture as
# "dispatchable" because its fragment string is `Nat`. Nothing finite settles a
# universal over an infinite domain. A queue that ranks Goldbach beside a
# 625-vertex colouring problem is worse than no queue, and it is the same
# overstatement this repository keeps finding in its own tools -- so the
# distinction is structural here, not a footnote.
#
# DECIDABLE   a decision procedure we have terminates on it. Dispatch and wait.
DECIDABLE = {"QF_BV", "QF_LIA", "QF_LRA", "QF_NIA", "QF_NRA", "QF_UF",
             "QF_UFLIA", "QF_ABV", "QF_SLIA", "UF"}
# PROOF_ROUTE quantified over an infinite domain: reachable only by constructing
#             a proof in the kernel (induction, a lemma chain), never by search.
#             Being in this class says a route EXISTS, not that it is feasible --
#             Goldbach lives here and will not be closed by it.
PROOF_ROUTE = {"Nat", "Int", "Real"}
# Anything else, `none` included, has no route at all today.


def load() -> dict[str, dict]:
    facts = {}
    for path in sorted(FACTS.glob("*.json")):
        d = json.loads(path.read_text())
        facts[d["id"]] = d
    return facts


def settled(fact: dict) -> bool:
    return fact["epistemic_status"] in SETTLED


def band(fact: dict, facts: dict[str, dict]) -> str:
    status = fact["epistemic_status"]
    external = fact.get("external_status")
    if status in SETTLED:
        return "novel" if external in EXTERNAL_UNSETTLED else "done"
    if status not in {"open", "conjectured", "empirical"}:
        return "done"
    unmet = [d for d in fact["depends_on"] if d not in facts or not settled(facts[d])]
    if unmet:
        return "blocked"
    return "research" if external in EXTERNAL_UNSETTLED else "backlog"


def describe(fact: dict, facts: dict[str, dict], show_unlocks: bool,
             unlocks: dict[str, list[str]]) -> str:
    frag = fact["formal"]["fragment"]
    if frag in DECIDABLE:
        reach = "DECIDABLE — dispatch it"
    elif frag in PROOF_ROUTE:
        reach = "proof route only — needs a kernel proof, no search will close it"
    else:
        reach = f"NO ROUTE (fragment {frag!r})"
    line = f"  {fact['id']:<40} {frag:<8} {reach}"
    unmet = [d for d in fact["depends_on"] if d not in facts or not settled(facts[d])]
    if unmet:
        line += f"\n      needs first: {', '.join(unmet)}"
    if show_unlocks and unlocks.get(fact["id"]):
        line += f"\n      would unlock: {', '.join(unlocks[fact['id']])}"
    return line


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--band", choices=["research", "backlog", "blocked", "novel"])
    ap.add_argument("--unlocks", action="store_true",
                    help="show which open facts each entry would unblock")
    args = ap.parse_args()

    if not FACTS.is_dir():
        print("fact-frontier: no artifacts/facts/ directory", file=sys.stderr)
        return 2
    facts = load()

    # Reverse dependency edges: proving X frees everything that names X.
    unlocks: dict[str, list[str]] = defaultdict(list)
    for fact in facts.values():
        if fact["epistemic_status"] in SETTLED:
            continue
        for dep in fact["depends_on"]:
            unlocks[dep].append(fact["id"])

    bands: dict[str, list[dict]] = defaultdict(list)
    for fact in facts.values():
        bands[band(fact, facts)].append(fact)

    titles = {
        "research": "RESEARCH FRONTIER — open to us and unsettled in the literature",
        "backlog": "IMPORT BACKLOG — settled elsewhere, not here (formalization, not discovery)",
        "blocked": "BLOCKED — open, but a dependency is not established yet",
        "novel": "ESTABLISHED HERE, NOT IN THE LITERATURE — the output",
    }
    for key in ("research", "blocked", "backlog", "novel"):
        if args.band and args.band != key:
            continue
        rows = sorted(bands.get(key, []), key=lambda f: f["id"])
        print(f"\n{titles[key]}  [{len(rows)}]")
        if not rows:
            print("  (none)")
            continue
        for fact in rows:
            print(describe(fact, facts, args.unlocks, unlocks))

    if not args.band:
        research = bands.get("research", [])
        decidable = [f for f in research if f["formal"]["fragment"] in DECIDABLE]
        proofish = [f for f in research if f["formal"]["fragment"] in PROOF_ROUTE]
        print(f"\n{len(facts)} facts. Research frontier {len(research)}: "
              f"{len(decidable)} decidable by dispatch, {len(proofish)} needing a "
              f"kernel proof, {len(research) - len(decidable) - len(proofish)} with "
              f"no route.")
        if decidable:
            print("Dispatch next: " + ", ".join(f["id"] for f in sorted(
                decidable, key=lambda f: f["id"])))
        if not research:
            print("The frontier is EMPTY. That is not success -- it means nothing in "
                  "the ledger is both unsettled outside and open here, so the next "
                  "move is to extract or state new propositions, not to solve.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
