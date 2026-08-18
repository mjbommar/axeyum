#!/usr/bin/env python3
"""Re-derive the numbers a fact asserts about its OWN `axiom_footprint`.

WHY THIS EXISTS. `F:schedule-critical-chain-infeasible` had its footprint
corrected 30 -> 26 on 2026-08-15. The array changed, the `--expect-axioms` flag
changed, and the two English sentences beside them did not: for three days the
fact said "the 30 axioms the kernel module actually rests on" inside a fact whose
footprint listed 26. Nothing could notice, because a derived number written into
prose has no link back to the thing it was derived from.

That is the failure this repository keeps rediscovering in other shapes -- a gate
that runs zero tests, a checker that exits 0 on completion alone, a doc comment
describing a route that was rewired underneath it. The fact ledger is the product
at N lanes, and axiom-freedom is its headline metric, so a fact whose prose
disagrees with its own footprint is worse than a fact with no prose at all.

# WHAT IT CHECKS

Only assertions a fact makes about ITS OWN `axiom_footprint`, recognized
STRUCTURALLY rather than by reading English. Two anchors, both already
conventions in the ledger rather than anything invented here:

  1. an `evidence[i].supports` whose text begins with the literal field name
     `axiom_footprint` -- 48 slots today, the ledger's established way of saying
     "this evidence entry is about the trusted surface";
  2. a `--expect-axioms N` flag inside any `checker_command`, which is a number
     in a command derived from the same array.

Inside anchor (1) a claim is classified into exactly one kind and checked:

  * `axiom_footprint: []`            -> the array must be literally empty
  * an explicit no-axiom claim       -> zero DECLARATION entries (see below)
  * exactly one cardinal in the slot -> it must equal the declaration count
  * exactly one BARE `N axioms` in that entry's `notes` -> same

"Declaration entries" are the footprint entries that name a kernel declaration
(`Real.add_comm`, `Classical.choice`, `axeyum.reconstruct.lra.hyp._2`) as opposed
to the semantic and route assumptions the same array also carries by convention
(`lean4export-3.1.0-stream-faithfulness`, `cas.exact-rational-polynomial-normal-form`).
The two are told apart by shape -- a declaration is a dotted identifier, an
assumption id is lowercase-hyphenated -- which on the committed ledger separates
32 declarations from 213 assumptions with no overlap. It matters: the import
route's footprint is three trust assumptions and zero declarations, and
"reaches no Lean axiom" is a claim about the second number, not the first.

# WHAT IT DOES *NOT* CHECK, and this list is the point

* **Any number in prose that is not about this fact's own footprint.** Measured
  2026-08-18: the 114 committed facts contain **3,243 numeric tokens** across
  their prose fields. This script binds **52** of them. The other 3,191 are
  mathematics ("the three Peano axioms"), instance shape ("seven dependencies"
  of a relational schema), timings, byte sizes, line counts, and measurements of
  other runs. Nothing here re-derives those, and a gate that claimed to would be
  worse than none -- three of the seven phrases matching a naive `N axioms`
  regex are about Peano's axioms, Armstrong's axioms, and a *different*
  theorem's footprint. Those two counts are themselves derived numbers in prose,
  so do not trust them here: every run PRINTS the live pair, and this paragraph
  is a dated reading of it, not the authority.
* **Whether the footprint array is itself correct.** That is the checker
  command's job (`--expect-axioms`, `Kernel::axiom_footprint`). This compares
  prose to the array; if the array is wrong, this passes.
* **Prose claims with no number in them.** The larger staleness found in that
  same fact on 2026-08-18 was a paragraph describing a facade that emitted a
  21-line structural shim, when the facade had emitted a real 62-line `Lra`
  module since 2026-08-15. No arithmetic check can see that.
* **The `statement`, top-level `notes`, `provenance`, or any evidence entry that
  is not footprint-anchored.** Deliberate: the anchor is what makes the subject
  of the sentence machine-decidable.
* **Ambiguous slots.** A slot with two cardinals ("six trusted declarations in
  our kernel's classification, three in Lean's") is not guessed at. It is
  counted as UNCHECKED and reported -- and the unchecked count is itself
  ratcheted, so silence cannot grow without someone raising a number here.

# EXIT STATUS DEPENDS ON WHAT IT FOUND

Nonzero iff a claim disagreed with the array, or the unchecked ceiling was
exceeded, or fewer anchored slots were found than the floor (a loader that stops
finding facts must not report a healthy zero). Each of those is a separate guard
with its own control in `scripts/tests/test_check_fact_derived_numbers.py`;
`scripts/tests/mutation_controls.py fact-derived-numbers` deletes them one at a
time and requires each deletion to kill a test.

Usage:
    python3 scripts/check-fact-derived-numbers.py
    python3 scripts/check-fact-derived-numbers.py --quiet
    python3 scripts/check-fact-derived-numbers.py --census   # every prose number,
                                                             # bound and unbound
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from dataclasses import dataclass, field
from typing import Any, Iterator

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"

# --- ratchets ---------------------------------------------------------------
# Measured 2026-08-18 on the committed ledger. FLOOR is a liveness guard: a
# loader that silently stops finding facts would otherwise report zero problems.
# CEILING bounds the anchored slots this script cannot bind to a number, so
# ambiguity has to be argued for rather than added.
MIN_ANCHORED_SLOTS = 45   # 48 anchored slots on 2026-08-18
MAX_UNCHECKED_SLOTS = 1   # exactly one today: F:prop-excluded-middle-classical

# A kernel declaration name: a dotted identifier. An assumption id in the same
# array is lowercase-hyphenated prose (`lean4export-3.1.0-stream-faithfulness`).
DECLARATION = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")

ANCHOR = "axiom_footprint"
EMPTY_LITERAL = "axiom_footprint: []"

CARDINALS = {
    "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
    "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
    "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50,
}
_CARDINAL_ALT = "|".join(sorted(CARDINALS, key=len, reverse=True))
CARDINAL_RE = re.compile(rf"(?i)\b(\d+|{_CARDINAL_ALT})\b")

# A BARE total: the noun follows the numeral immediately. `4 variable axioms` is
# a SUBSET and deliberately does not match -- that distinction is what lets the
# schedule fact's decomposition sentence be read for its total without guessing.
BARE_TOTAL_RE = re.compile(
    rf"(?i)\b(\d+|{_CARDINAL_ALT})\s+(?:axioms|axiom|trusted declarations)\b"
)

# Explicit no-axiom claims. Each is a phrase the ledger already uses; a slot that
# matches none of them and carries no cardinal is UNCHECKED, not passed.
NO_AXIOM_PHRASES = (
    "reaches no lean axiom",
    "reaches no axiom",
    "trusted surface is empty",
    "admits no trusted declaration",
    "trusted closure is empty",
)

EXPECT_AXIOMS_RE = re.compile(r"--expect-axioms[= ](\d+)")


def cardinal(token: str) -> int:
    return int(token) if token.isdigit() else CARDINALS[token.lower()]


@dataclass
class Claim:
    """One assertion about a fact's own footprint, and where it was read."""

    fact: str
    where: str
    kind: str  # empty-literal | no-axiom | count | ambiguous | unclassified
    asserted: int | None
    text: str


@dataclass
class Reading:
    claims: list[Claim] = field(default_factory=list)
    anchored_slots: int = 0
    declarations: dict[str, int] = field(default_factory=dict)
    footprint_len: dict[str, int] = field(default_factory=dict)


def declaration_count(footprint: list[str] | None) -> int:
    return sum(1 for a in (footprint or []) if DECLARATION.match(a))


def load(directory: pathlib.Path = FACTS) -> list[dict[str, Any]]:
    return [json.loads(p.read_text()) for p in sorted(directory.glob("*.json"))]


def _classify(text: str) -> tuple[str, int | None]:
    """Classify one footprint-anchored slot. Exactly one kind, by priority."""
    if EMPTY_LITERAL in text:
        return "empty-literal", None
    low = text.lower()
    if any(phrase in low for phrase in NO_AXIOM_PHRASES):
        return "no-axiom", None
    values = {cardinal(m.group(1)) for m in CARDINAL_RE.finditer(text)}
    if len(values) == 1:
        return "count", values.pop()
    if len(values) > 1:
        return "ambiguous", None
    return "unclassified", None


def read(facts: list[dict[str, Any]]) -> Reading:
    """Extract every footprint claim. Reading is separate from judging so the
    controls can drive each guard without hand-building a whole ledger."""
    out = Reading()
    for fact in facts:
        fid = fact.get("id", "<no id>")
        decls = declaration_count(fact.get("axiom_footprint"))
        out.declarations[fid] = decls
        out.footprint_len[fid] = len(fact.get("axiom_footprint") or [])
        for i, entry in enumerate(fact.get("evidence") or []):
            command = entry.get("checker_command") or ""
            for m in EXPECT_AXIOMS_RE.finditer(command):
                out.claims.append(
                    Claim(fid, f"evidence[{i}].checker_command", "expect-axioms",
                          int(m.group(1)), m.group(0))
                )
            supports = entry.get("supports") or ""
            if not supports.startswith(ANCHOR):
                continue
            out.anchored_slots += 1
            kind, value = _classify(supports)
            out.claims.append(Claim(fid, f"evidence[{i}].supports", kind, value, supports))
            # The entry's `notes` explains its `supports`, so inside an anchored
            # entry a BARE `N axioms` is a statement about the same array.
            notes = entry.get("notes") or ""
            totals = {cardinal(m.group(1)) for m in BARE_TOTAL_RE.finditer(notes)}
            if len(totals) == 1:
                out.claims.append(
                    Claim(fid, f"evidence[{i}].notes", "count", totals.pop(), notes[:120])
                )
            elif len(totals) > 1:
                out.claims.append(
                    Claim(fid, f"evidence[{i}].notes", "ambiguous", None, notes[:120])
                )
        # A top-level `notes` may also carry the flag when a fact documents its
        # own checker; the flag is machine-readable wherever it appears.
        for m in EXPECT_AXIOMS_RE.finditer(fact.get("notes") or ""):
            out.claims.append(
                Claim(fid, "notes", "expect-axioms", int(m.group(1)), m.group(0))
            )
    return out


def evaluate(
    reading: Reading,
    *,
    floor: int = MIN_ANCHORED_SLOTS,
    ceiling: int = MAX_UNCHECKED_SLOTS,
) -> list[str]:
    """Every guard here can fail on its own; the controls prove each one does."""
    failures: list[str] = []
    for c in reading.claims:
        decls = reading.declarations.get(c.fact, 0)
        total = reading.footprint_len.get(c.fact, 0)
        # GUARD empty-literal: the prose writes the array out; it must be empty.
        if c.kind == "empty-literal" and total != 0:
            failures.append(
                f"{c.fact} {c.where}: prose says `axiom_footprint: []` but the "
                f"array has {total} entr(ies)"
            )
        # GUARD no-axiom: an explicit no-axiom claim needs zero DECLARATIONS
        # (route/semantic assumptions in the same array are not axioms).
        if c.kind == "no-axiom" and decls != 0:
            failures.append(
                f"{c.fact} {c.where}: prose claims no axiom is reached, but the "
                f"footprint names {decls} kernel declaration(s)"
            )
        # GUARD supports-count: a lone cardinal in the anchored slot is the total.
        if c.kind == "count" and c.where.endswith(".supports") and c.asserted != decls:
            failures.append(
                f"{c.fact} {c.where}: prose asserts {c.asserted} axiom(s); the "
                f"footprint names {decls} kernel declaration(s)"
            )
        # GUARD notes-count: same, for the explaining `notes` of the same entry.
        if c.kind == "count" and c.where.endswith(".notes") and c.asserted != decls:
            failures.append(
                f"{c.fact} {c.where}: notes assert {c.asserted} axiom(s); the "
                f"footprint names {decls} kernel declaration(s)"
            )
        # GUARD expect-axioms: a number inside the command, derived from the array.
        if c.kind == "expect-axioms" and c.asserted != total:
            failures.append(
                f"{c.fact} {c.where}: `{c.text}` but the footprint array has "
                f"{total} entr(ies)"
            )
    unchecked = [c for c in reading.claims if c.kind in ("ambiguous", "unclassified")]
    # GUARD unchecked-ceiling: silence is the failure mode this whole script is
    # about, so the amount of it is pinned rather than merely printed.
    if len(unchecked) > ceiling:
        failures.append(
            f"{len(unchecked)} footprint claim(s) could not be bound to a number "
            f"(ceiling {ceiling}): "
            + ", ".join(f"{c.fact} {c.where}" for c in unchecked)
        )
    # GUARD floor: a reader that stops finding anchored slots must not look green.
    if reading.anchored_slots < floor:
        failures.append(
            f"only {reading.anchored_slots} footprint-anchored evidence slot(s) "
            f"found, floor is {floor} -- the ledger shrank or the reader is broken"
        )
    return failures


def prose_numeric_tokens(facts: list[dict[str, Any]]) -> int:
    """How many numbers live in prose at all -- the denominator for coverage."""
    number = re.compile(r"\b\d[\d,]*(?:\.\d+)?\b")

    def strings(o: Any, path: str = "") -> Iterator[tuple[str, str]]:
        if isinstance(o, dict):
            for k, v in o.items():
                yield from strings(v, f"{path}/{k}")
        elif isinstance(o, list):
            for i, v in enumerate(o):
                yield from strings(v, f"{path}[{i}]")
        elif isinstance(o, str):
            yield path, o

    total = 0
    for fact in facts:
        for path, s in strings(fact):
            if any(seg in path for seg in ("/formal", "checker_command", "/artifact",
                                           "/id", "/schema_version")):
                continue
            total += len(number.findall(s))
    return total


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--census", action="store_true",
                    help="list every footprint claim and its verdict")
    args = ap.parse_args()

    facts = load()
    reading = read(facts)
    failures = evaluate(reading)

    bound = [c for c in reading.claims if c.kind in ("empty-literal", "no-axiom",
                                                     "count", "expect-axioms")]
    unbound = [c for c in reading.claims if c not in bound]
    if args.census:
        for c in sorted(reading.claims, key=lambda c: (c.fact, c.where)):
            print(f"{c.kind:14s} {c.asserted if c.asserted is not None else '-':>4} "
                  f"decls={reading.declarations.get(c.fact, 0):<3} {c.fact} {c.where}")
    if not args.quiet or failures:
        total_prose = prose_numeric_tokens(facts)
        print(
            f"fact derived numbers: {len(facts)} fact(s), "
            f"{reading.anchored_slots} footprint-anchored slot(s), "
            f"{len(bound)} claim(s) re-derived, {len(unbound)} unchecked; "
            f"{total_prose} numeric token(s) in prose overall -- "
            f"this gate binds {len(bound)} of them and NONE of the rest "
            f"(see the module docstring for what that excludes)"
        )
    for f in failures:
        print(f"FAIL {f}", file=sys.stderr)
    if failures:
        print(f"{len(failures)} derived-number disagreement(s)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
