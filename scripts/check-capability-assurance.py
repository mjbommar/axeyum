#!/usr/bin/env python3
"""Derive the capability table's assurance mix, and gate the tier that matters.

`docs/mathematics-2026-08/01-decide-vs-certify.md` sets the strand's primary
metric: *"For each area: does a verdict come with an artifact a third party can
check without trusting us?"* — and says "moving that count is the strand's
primary metric".

**That count could not be computed.** `Assurance` distinguishes `Checked` /
`Validated` / `SoundIncomplete` / `Experimental`, and `Checked` means "has an
independently *checkable* certificate" — which does not say whether anyone
outside this project has checked it. The rest lives in `evidence`, a free-prose
field. So the metric existed as a sentence, not a number.

The distinction this makes, which the prose blurs:

  external-artifact-checker  Carcara / Lean / drat-trim read OUR artifact and
                             accept or reject it. This is the third tier.
  self-checker               our own re-derivation (check_drat, recheck, model
                             replay). Real, and not the same claim.
  differential               agreement with Z3/cvc5 on the VERDICT. Valuable,
                             but nobody checked an artifact — a differential
                             oracle is not a proof checker, and counting it as
                             one is the overstatement this strand exists to
                             remove.

# This is a heuristic over prose, and that is the point

It classifies by scanning `evidence` for named checkers, so it can be fooled by
wording. It reports an `unclassified` bucket rather than sorting the remainder
into whichever tier looks good. The need for a heuristic at all IS the strand's
item A ("re-derive the table from the code rather than maintaining it by hand")
and item C ("make 'decided, not certified' an explicit status"): the day this
field is machine-readable, this script gets simpler and stops guessing.
"""

from __future__ import annotations

import pathlib
import re
import sys
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parents[1]
TABLE = ROOT / "crates/axeyum-solver/src/capabilities.rs"

# Third parties that read OUR artifact.
EXTERNAL = re.compile(r"\bCarcara\b|\bLean\b|\bdrat-trim\b|\blean4?\b", re.I)
# Our own re-derivation.
SELF = re.compile(r"check_drat|recheck|replay|re-deriv|independent(ly)? check", re.I)
# Verdict agreement, not artifact checking.
DIFFERENTIAL = re.compile(r"differential|vs\.? Z3|vs\.? cvc5|oracle", re.I)

# The externally-checked count may not FALL. Measured 2026-08-17: 36 entries
# across 11 of 23 areas.
#
# This is the strand's primary metric, and the reason it needs a floor is that
# it had drifted UNMEASURED. `01-decide-vs-certify.md` said "Four name a
# kernel/Lean-checked proof … QF_LIA, QF_LRA, QF_NRA, quantifiers". All four are
# real, and seven more had joined them — QF_ABV, QF_BV, QF_UF, QF_UFLIA,
# QF_UFLRA, datatypes, reachability — mostly via Carcara. Nobody noticed,
# because counting required reading 101 prose fields.
EXTERNAL_FLOOR = 36
MIN_ENTRIES = 90


def entries(text: str) -> list[dict[str, str]]:
    """Every `Capability { … }` literal, as a dict of its string fields."""
    out: list[dict[str, str]] = []
    for m in re.finditer(r"Capability\s*\{(.*?)\n    \},", text, re.S):
        body = m.group(1)
        rec: dict[str, str] = {}
        for field in ("area", "feature", "evidence", "reference"):
            fm = re.search(rf'{field}:\s*"(.*?)"\s*,\s*\n', body, re.S)
            if fm:
                # join `\` line continuations into one line
                rec[field] = re.sub(r"\\\s*\n\s*", " ", fm.group(1))
        am = re.search(r"assurance:\s*Assurance::(\w+)", body)
        if am:
            rec["assurance"] = am.group(1)
        if "area" in rec:
            out.append(rec)
    return out


def tier(rec: dict[str, str]) -> str:
    ev = rec.get("evidence", "")
    if EXTERNAL.search(ev):
        return "external-artifact-checker"
    if SELF.search(ev):
        return "self-checker"
    if DIFFERENTIAL.search(ev):
        return "differential-only"
    return "unclassified"


def main(argv: list[str]) -> int:
    text = TABLE.read_text(encoding="utf-8")
    recs = entries(text)
    tiers = Counter(tier(r) for r in recs)
    assurance = Counter(r.get("assurance", "?") for r in recs)
    areas = {r["area"] for r in recs}
    external = tiers["external-artifact-checker"]

    if "--quiet" not in argv:
        print(f"  areas: {len(areas)}   assurance: " +
              ", ".join(f"{k} {v}" for k, v in sorted(assurance.items())))
        for k in ("external-artifact-checker", "self-checker",
                  "differential-only", "unclassified"):
            print(f"    {tiers[k]:4d}  {k}")
        if tiers["unclassified"]:
            print("  unclassified areas: " + ", ".join(sorted(
                {r["area"] for r in recs if tier(r) == "unclassified"})))

    print(f"CAPABILITY_ASSURANCE|entries={len(recs)}|areas={len(areas)}|"
          f"external={external}|self={tiers['self-checker']}|"
          f"differential={tiers['differential-only']}|"
          f"unclassified={tiers['unclassified']}")

    failures = []
    if len(recs) < MIN_ENTRIES:
        failures.append(
            f"parsed only {len(recs)} capability entries (floor {MIN_ENTRIES}); the "
            "parser has stopped matching the table's shape and every count above "
            "would be understated"
        )
    elif external < EXTERNAL_FLOOR:
        failures.append(
            f"{external} capabilities name an external artifact checker, below the "
            f"floor of {EXTERNAL_FLOOR}. This is the strand's primary metric and it "
            "may not fall silently"
        )
    for f in failures:
        print(f"CAPABILITY_ASSURANCE_ERROR|{f}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
