#!/usr/bin/env python3
"""UFLIA-TRACE -- does the term z3 substitutes ever enter OUR ground set?

    ground-membership.py <grounddump> <instances.inst>

`AXEYUM_QGROUNDDUMP` writes the accumulated ground set at each loop exit;
`proof-instances.py` writes the terms z3 actually substituted, one instance per
line, tab-separated. This asks, per instance argument, whether we ever built it.

The two situations it separates need completely different fixes and are
otherwise indistinguishable:

  PRESENT     we build the term and do not use it -- a selection/admission problem
  ABSENT      we never build the term at all       -- no cap, budget or ranking
                                                      change can reach it
  NOT-GROUND  the term still mentions one of z3's own BOUND variables (`?p_!9`),
              so it is not a ground term and cannot be in anyone's ground set.
              Folding these into ABSENT mixes "we did not build it" with "it is
              not the kind of thing that gets built", and the mixture reads as
              the first.

# The comparison this file got wrong first, and why the wrong one looked fine

The first version compared each substituted term against a `GROUND` ROW. A
`GROUND` row is a whole asserted CONJUNCT -- `(or (and true (and (= (IsHeap
Heap_) Smt.true) ...` -- not an individual term. So the test returned **ABSENT on
100 % of arguments on every core**, including bare declared constants
(`nullObject`, `this`, `J`), which cannot possibly be missing: `nullObject` occurs
215 times inside one 34-row dump. A 100 % ABSENT that includes a constant is the
signature of a comparison that never matches, not of a solver that never builds
one -- and read at face value it would have published "we never construct the
term z3 needs" as this lane's headline.

The right question is whether the term occurs ANYWHERE in the rendered ground
set, so the test is containment over the dump's text, with identifier boundaries
so `J` does not match inside `Java`.

# Two directions, two different strengths

**PRESENT is strong; ABSENT is a lower bound, never a proof.** Our dump holds
whatever the run accumulated before its deadline, so a term reported ABSENT may
be one a longer or quieter run would have built. Every row also carries a
NON-VACUITY CONTROL -- a synthetic identifier that cannot occur anywhere -- because
a containment test over a multi-megabyte corpus drifts toward answering PRESENT
for everything, and then the zero on the other side means nothing. Both failure
directions are guarded: `CAN-ANSWER-ABSENT` says the test can still say no.
"""

from __future__ import annotations

import collections
import re
import sys

WS = re.compile(r"\s+")
# A term that cannot occur in any SMT-LIB corpus, for the non-vacuity control.
IMPOSSIBLE = "axeyum__uflia_trace__control_symbol__must_be_absent"
# z3 renders a BOUND variable as `?x!3` / `?p_!9`. A substituted term containing
# one is not a ground term at all -- it is an instance made under a nested
# quantifier, whose argument still mentions that quantifier's own variable. Such
# a term cannot be in ANY solver's ground set, so counting it as ABSENT mixes
# "we did not build it" with "it is not the kind of thing that gets built", and
# the mixture reads as the first.
BOUND_VAR = re.compile(r"\?[A-Za-z_][A-Za-z0-9_.]*!")


def norm(s: str) -> str:
    return WS.sub(" ", s.strip())


def contains(haystack: str, needle: str) -> bool:
    """`needle` occurs in `haystack` at identifier boundaries.

    A bare symbol like `J` must not match inside `Java`; a compound like
    `(f a b)` is already delimited by its own parentheses, but the boundary test
    is harmless there and keeps one code path.
    """
    pattern = re.escape(needle)
    return re.search(rf"(?<![A-Za-z0-9_.]){pattern}(?![A-Za-z0-9_.])", haystack) is not None


def main() -> None:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) < 2:
        print(__doc__)
        sys.exit(2)
    dump_path, inst_path = args[0], args[1]

    rows = 0
    chunks: list[str] = []
    with open(dump_path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if line.startswith("GROUND "):
                parts = line.split(" ", 3)
                if len(parts) == 4:
                    rows += 1
                    chunks.append(norm(parts[3]))
    if not rows:
        print("NO-GROUND-DUMP  the dump is empty or was never written; this is "
              "not a measurement of absence")
        sys.exit(3)
    haystack = " ".join(chunks)

    # NON-VACUITY CONTROL, printed whether or not it is asked for: a containment
    # test over a large corpus that answered PRESENT for everything would produce
    # this file's headline by construction.
    control = "CAN-ANSWER-ABSENT" if not contains(haystack, IMPOSSIBLE) else "BROKEN"
    if control == "BROKEN":
        print("CONTROL FAILED: the impossible symbol was found; the containment "
              "test matches everything and every PRESENT below is meaningless")
        sys.exit(4)

    counts: collections.Counter[str] = collections.Counter()
    missing: list[str] = []
    with open(inst_path, encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if not line.startswith("INSTANCE"):
                continue
            for arg in line.rstrip("\n").split("\t")[1:]:
                if not arg.strip():
                    continue
                n = norm(arg)
                if BOUND_VAR.search(n):
                    counts["NOT-GROUND"] += 1
                elif contains(haystack, n):
                    counts["PRESENT"] += 1
                else:
                    counts["ABSENT"] += 1
                    missing.append(n)

    total = sum(counts.values())
    print(f"ground rows {rows}  chars {len(haystack)}  instance arguments {total}"
          f"  control {control}")
    for k in ("PRESENT", "ABSENT", "NOT-GROUND"):
        v = counts[k]
        pct = f"{100 * v / total:5.1f}%" if total else "   n/a"
        print(f"  {k:8s} {v:5d} {pct}")
    for m in sorted(set(missing))[:8]:
        print(f"  ABSENT-TERM {m[:140]}")


if __name__ == "__main__":
    main()
