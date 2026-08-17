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

# --- ranking the gap (strand item B) ------------------------------------
# What an external checker would need to CONSUME. A logic whose evidence already
# names a refutation artifact is a plumbing job; one that names only a model
# replay needs an UNSAT proof format first, which is a research question.
UNSAT_ARTIFACT = re.compile(
    r"\bDRAT\b|\bLRAT\b|Farkas|resolution proof|unsat core|certificate", re.I
)
# `replay` unanchored: the table says "model replay" in one row and "is REPLAYED
# through the ground evaluator" in the next, and they mean the same thing. Band 1
# is tested first, so widening here cannot steal a logic that has a refutation
# artifact.
SAT_ARTIFACT = re.compile(r"replay|witness|model is (re)?checked", re.I)

BANDS = {
    1: "artifact already built — export it and point a checker at it",
    2: "model replay only — needs an UNSAT proof format first",
    3: "no refutation artifact named",
}

# The externally-checked count may not FALL. Measured 2026-08-17: 36 entries
# across 12 of 23 logics (11 when written; QF_RDL was gated 2026-08-17).
#
# This is the strand's primary metric, and the reason it needs a floor is that
# it had drifted UNMEASURED. `01-decide-vs-certify.md` said "Four name a
# kernel/Lean-checked proof … QF_LIA, QF_LRA, QF_NRA, quantifiers". All four are
# real, and seven more had joined them — QF_ABV, QF_BV, QF_UF, QF_UFLIA,
# QF_UFLRA, datatypes, reachability — mostly via Carcara. Nobody noticed,
# because counting required reading 101 prose fields.
EXTERNAL_FLOOR = 37
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


def logics(area: str) -> set[str]:
    """The logic(s) an `area` string names.

    The field is prose, and some entries legitimately span more than one logic:
    `"QF_ABV / QF_AUFBV"` and `"QF_UFLIA/UFLRA"` are capabilities covering both,
    not misspellings of a single area. Counting the raw strings therefore
    UNDERSTATES coverage — a logic reachable only through a compound entry looks
    absent — and rewriting them to a single name would delete the fact that the
    capability spans two.

    So the string is left alone and the COUNT is normalised instead: split on
    `/` and `,`, drop a trailing parenthetical gloss (`"QF_S (strings)"`,
    `"SAT (propositional)"`). Measured 2026-08-17, this moves the denominator
    from 23 area strings to the logics they actually name.

    A compound may ABBREVIATE the shared prefix: `"QF_UFLIA/UFLRA"` means
    `QF_UFLIA` and `QF_UFLRA`, not a logic called `UFLRA`. Splitting naively
    invents one, which inflates the denominator with a logic that does not
    exist — measured: 24 logics instead of 23, with a phantom `UFLRA` alongside
    the real `QF_UFLRA`. So a bare part inherits the first part's `QF_` prefix.
    """
    parts = [re.sub(r"\s*\(.*?\)\s*", " ", p).strip()
             for p in re.split(r"[/,]", area)]
    parts = [p for p in parts if p]
    if not parts:
        return set()
    prefix = "QF_" if parts[0].startswith("QF_") else ""
    out: set[str] = set()
    for i, name in enumerate(parts):
        if i and prefix and not name.startswith("QF_") and name.isupper():
            name = prefix + name
        out.add(name)
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


def rank(recs: list[dict[str, str]]) -> dict[str, tuple[int, set[str]]]:
    """Gap logics banded by how far they are from an external check.

    Derived, because a written-down ranking rots: item B names `QF_UF` and
    `datatypes` as candidates to rank, and both are externally checked already.

    Same caveat as `tier`: this reads the evidence PROSE, so it reports what the
    table claims exists, not what the code emits. It is a queue, not a gate.
    """
    external = {
        lg
        for r in recs
        if tier(r) == "external-artifact-checker"
        for lg in logics(r["area"])
    }
    out: dict[str, tuple[int, set[str]]] = {}
    for lg in {lg for r in recs for lg in logics(r["area"])} - external:
        ev = " ".join(
            r.get("evidence", "") for r in recs if lg in logics(r["area"])
        )
        hits = {h.lower() for h in UNSAT_ARTIFACT.findall(ev)}
        band = 1 if hits else (2 if SAT_ARTIFACT.search(ev) else 3)
        out[lg] = (band, hits)
    return out


def compound_only(recs: list[dict[str, str]]) -> set[str]:
    """Logics whose assurance is never stated on their own.

    `tier` is per ROW, so a row named `QF_IDL / QF_RDL` asserts one tier for both
    logics. Measured 2026-08-17 that is wrong for exactly that row: QF_RDL
    reconstructs to a Lean theory module and QF_IDL renders only an attestation
    (`crates/axeyum-solver/tests/difference_logic_lean_content.rs`). Reported so
    the gap list carries its own uncertainty.
    """
    solo = {
        lg for r in recs if len(logics(r["area"])) == 1 for lg in logics(r["area"])
    }
    return {
        lg for r in recs if len(logics(r["area"])) > 1 for lg in logics(r["area"])
    } - solo


def main(argv: list[str]) -> int:
    text = TABLE.read_text(encoding="utf-8")
    recs = entries(text)
    tiers = Counter(tier(r) for r in recs)
    assurance = Counter(r.get("assurance", "?") for r in recs)
    areas = {lg for r in recs for lg in logics(r["area"])}
    external = tiers["external-artifact-checker"]

    if "--quiet" not in argv:
        print(f"  areas: {len(areas)}   assurance: " +
              ", ".join(f"{k} {v}" for k, v in sorted(assurance.items())))
        for k in ("external-artifact-checker", "self-checker",
                  "differential-only", "unclassified"):
            print(f"    {tiers[k]:4d}  {k}")
        if tiers["unclassified"]:
            print("  unclassified areas: " + ", ".join(sorted(
                {lg for r in recs if tier(r) == "unclassified"
                 for lg in logics(r["area"])})))

    if "--rank" in argv:
        banded = rank(recs)
        shared = compound_only(recs)
        print(f"  gap ranked by distance to an external checker ({len(banded)} logics):")
        for band in sorted(BANDS):
            members = sorted(lg for lg, (b, _) in banded.items() if b == band)
            if not members:
                continue
            print(f"    band {band} — {BANDS[band]}")
            for lg in members:
                hits = ", ".join(sorted(banded[lg][1])) or "-"
                mark = "  [tier shared with another logic]" if lg in shared else ""
                print(f"      {lg:<20} artifact: {hits}{mark}")
        if shared:
            print("  assurance never stated per logic: " + ", ".join(sorted(shared)))

    covered = {
        lg
        for r in recs
        if tier(r) == "external-artifact-checker"
        for lg in logics(r["area"])
    }
    if "--quiet" not in argv:
        print(
            f"  logics: {len(covered)} of {len(areas)} have an external artifact "
            f"checker; {len(areas) - len(covered)} do not (rank them with --rank)"
        )

    print(f"CAPABILITY_ASSURANCE|entries={len(recs)}|areas={len(areas)}|"
          f"external={external}|self={tiers['self-checker']}|"
          f"differential={tiers['differential-only']}|"
          f"unclassified={tiers['unclassified']}|"
          f"logics_external={len(covered)}|logics_total={len(areas)}")

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
