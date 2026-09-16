#!/usr/bin/env python3
"""QUANT-SESSION-ARITH (ADR-2130) -- how much arithmetic actually moved OUT of
the abstraction and INTO the theory?

    engagement-compare.py <level0.txt> <level1.txt> <level2.txt>

Each input is an `engagement-probe.sh` capture. The number this lane is measured
on is the PER-CORE DIFFERENCE

    abstracted@level1  -  abstracted@level2

taken on cores where both arms reached the session-construction site. Level 1
abstracts every Boolean-position term the `EUF` encoder has no arm for; level 2
abstracts the same set MINUS the arithmetic order atoms it hosts instead. So the
difference is exactly the atoms that became real constraints, and it is the only
observation that separates "the lever engaged" from "the lever was built".

`abstracted=0` at level 2 ON ITS OWN says nothing: it is equally what a file with
no arithmetic prints and what a file whose arithmetic was entirely hosted prints.
That ambiguity is why this script exists rather than a grep.

Level 0 is read for a THIRD question, which is about ADR-2124 rather than about
this lane: how often does the shipped arm actually refuse to build the session?
ADR-2124's premise is that one integer comparison anywhere in the ground set
refuses it, so UFLIA takes the cold branch for its whole run. `built=` at level 0
measures that directly.

Exit 1 if nothing moved -- a lever that engaged nowhere must not report cleanly.
"""

import re
import sys
from pathlib import Path

LINE = re.compile(
    r"^\+[0-9.]+s\s+built=(?P<built>\d+)\s+level=(?P<level>\d+)\s+round=\d+\s+"
    r"ground=(?P<ground>\d+)\s+atoms=(?P<atoms>\d+)\s+hosted=(?P<hosted>\d+)\s+"
    r"abstracted=(?P<abstracted>\d+)\s+gates=(?P<gates>\d+)\s+shapes=(?P<shapes>\S+)\s+"
    r"(?P<core>\S+)"
)
NOLINE = re.compile(r"^NO-LINE\s+(?P<core>\S+)")

ARITH_OPS = ("IntLt", "IntLe", "IntGt", "IntGe")


def read(path):
    """core -> row, plus the set of cores that printed an ABSENCE."""
    rows, absent = {}, set()
    for raw in Path(path).read_text(errors="replace").split("\n"):
        m = LINE.match(raw)
        if m:
            rows[m.group("core")] = {
                "built": int(m.group("built")),
                "hosted": int(m.group("hosted")),
                "abstracted": int(m.group("abstracted")),
                "gates": int(m.group("gates")),
                "shapes": m.group("shapes"),
                "atoms": int(m.group("atoms")),
                "ground": int(m.group("ground")),
            }
            continue
        m = NOLINE.match(raw)
        if m:
            absent.add(m.group("core"))
    return rows, absent


def arith_in_shapes(shapes):
    """Arithmetic order atoms named in a shapes histogram, as a count."""
    total = 0
    for part in shapes.split(","):
        if ":" not in part:
            continue
        op, n = part.rsplit(":", 1)
        if op in ARITH_OPS and n.isdigit():
            total += int(n)
    return total


def main(argv):
    if len(argv) != 4:
        print(__doc__)
        return 2
    l0, l0_absent = read(argv[1])
    l1, l1_absent = read(argv[2])
    l2, l2_absent = read(argv[3])

    print("== ADR-2130: did the lever ENGAGE, and on how much? ==")
    print()
    for label, rows, absent in (("level 0", l0, l0_absent), ("level 1", l1, l1_absent), ("level 2", l2, l2_absent)):
        built = sum(1 for r in rows.values() if r["built"] == 1)
        host = sum(1 for r in rows.values() if r["hosted"] == 1)
        absn = sum(r["abstracted"] for r in rows.values())
        witha = sum(1 for r in rows.values() if r["abstracted"] > 0)
        arith = sum(arith_in_shapes(r["shapes"]) for r in rows.values())
        print(
            f"   {label}: site reached {len(rows):2d}  absent {len(absent):2d}"
            f"  built {built:2d}  hosting {host:2d}"
            f"  abstracted {absn:4d} on {witha:2d} cores  (arith among them {arith:4d})"
        )
    print()
    print("   'absent' is a core whose construction site was NEVER REACHED -- the loop")
    print("   exited first. It is not a zero and is not folded into one.")

    both = sorted(set(l1) & set(l2))
    print()
    print(f"-- the per-core delta, on the {len(both)} cores BOTH arms reached --")
    movers = []
    for core in both:
        a1, a2 = l1[core]["abstracted"], l2[core]["abstracted"]
        if a1 != a2:
            movers.append((core, a1, a2, l1[core]["shapes"]))
    total_moved = sum(a1 - a2 for _, a1, a2, _ in movers)
    print(f"   cores where the abstraction count CHANGED : {len(movers)} of {len(both)}")
    print(f"   atoms moved out of the abstraction        : {total_moved}")
    print()
    for core, a1, a2, shapes in movers:
        arith = arith_in_shapes(shapes)
        print(f"   L1 abstracted {a1:3d} -> L2 {a2:3d}  (of which arith at L1: {arith:3d})  {core[:58]}")

    regressions = [(c, a1, a2) for c, a1, a2, _ in movers if a2 > a1]
    if regressions:
        print()
        print("   !! level 2 abstracted MORE than level 1 on these cores, which it must never do:")
        for c, a1, a2 in regressions:
            print(f"      {a1} -> {a2}  {c}")

    print()
    print("-- ADR-2124's premise, checked directly: does the SHIPPED arm refuse the session? --")
    l0_built = sum(1 for r in l0.values() if r["built"] == 1)
    print(f"   level 0 reached the site on {len(l0)} cores and BUILT a session on {l0_built}")
    if l0:
        print(
            f"   so the shipped arm refuses on {len(l0) - l0_built} of {len(l0)}"
            f" -- ADR-2124 reads as if this were all of them"
        )

    if total_moved <= 0:
        print()
        print(
            "EXIT 1: nothing moved out of the abstraction. Level 2 hosted no atom\n"
            "        that level 1 did not already abstract, so the lever was BUILT\n"
            "        but never ENGAGED on this population. Do not read a null A/B\n"
            "        against it as evidence that hosting arithmetic does not help."
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
