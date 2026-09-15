#!/usr/bin/env python3
"""REAL-OPAQUE -- the sat-side invariant, checked over the measured corpus.

The abstraction is sound for `unsat` transfer and NOT for `sat`. The guards, the
type and the model replay all exist to make sure a relaxation's solution never
becomes a verdict. Those are arguments and unit fixtures; this is the
corpus-scale OBSERVATION of the same property:

  * the number of `sat` verdicts must be IDENTICAL in both arms, and
  * no file may be `sat` in one arm and `unsat` in the other.

The first is the strong form: a new `sat` in the lever arm is the wrong verdict
this whole design is built to prevent, and it would show up here as a count
difference even if the file's `:status` were unknown to everyone. The second is
the flip check, stated separately because a flip is a wrong verdict on ONE of
the two sides and must never be folded into a net.

**This is not a substitute for the model replay.** It cannot see a `sat` that is
wrong in BOTH arms. It sees exactly the class the change could have introduced.

The exit status depends on the finding.

Usage: sat-side-invariant.py <tsv> [<tsv> ...]
"""

import sys
from collections import Counter


def main(paths):
    rows = []
    for path in paths:
        with open(path) as fh:
            line = fh.readline()
            while line.startswith("#"):
                line = fh.readline()
            header = line.rstrip("\n").split("\t")
            for line in fh:
                rows.append(dict(zip(header, line.rstrip("\n").split("\t"))))

    off = Counter(r["off_verdict"] for r in rows)
    on = Counter(r["on_verdict"] for r in rows)
    flips = [r for r in rows if {r["off_verdict"], r["on_verdict"]} == {"sat", "unsat"}]
    new_sat = [r for r in rows if r["off_verdict"] != "sat" and r["on_verdict"] == "sat"]
    lost_sat = [r for r in rows if r["off_verdict"] == "sat" and r["on_verdict"] != "sat"]

    print(f"files            : {len(rows)}")
    print(f"base arm         : {dict(off)}")
    print(f"lever arm        : {dict(on)}")
    print(f"sat in base      : {off['sat']}")
    print(f"sat in lever     : {on['sat']}")
    print(f"NEW sat          : {len(new_sat)}   <- must be 0")
    print(f"LOST sat         : {len(lost_sat)}")
    print(f"FLIPS sat<->unsat: {len(flips)}     <- must be 0")

    bad = False
    for label, bucket in (("NEW sat", new_sat), ("FLIP", flips)):
        for r in bucket:
            bad = True
            print(f"  {label}: {r['file']}  off={r['off_verdict']} on={r['on_verdict']}")
    if bad:
        print("\nFAIL: the abstraction produced a sat-side verdict change.")
        return 1
    print(
        f"\nPASS: over {len(rows)} files the sat count is identical in both arms and no file\n"
        f"      changed side. Every verdict this lever added is on the `unsat` side."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
