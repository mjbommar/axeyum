#!/usr/bin/env python3
"""DT-ARRAY-ELEMENT -- read an interleaved A/B and print the only three
numbers that decide whether the lever ships.

    ab-summarize.py <ab-*.shard*.tsv ...>

  1. DISAGREEMENTS: rows where the two arms give a DIFFERENT DECIDED verdict.
     A `sat`/`unsat` flip is a soundness incident and is printed by name, not
     counted into a total.
  2. GAINS and LOSSES: `unknown` -> decided, and decided -> `unknown`.
  3. The denominators, because a share without one is not a measurement.

Equal totals do not imply equal rows, so the comparison is ROW BY ROW. The
exit status depends on the finding: a flip exits 3, a loss exits 2, a clean
run exits 0 -- a summariser that always exits 0 is the checker that cannot
fail.
"""

import os
import sys
from collections import Counter

DECIDED = ("sat", "unsat")


def main():
    paths = sys.argv[1:]
    if not paths:
        sys.stderr.write(__doc__)
        return 2
    rows = 0
    base = Counter()
    arm = Counter()
    gains = []
    losses = []
    flips = []
    first = Counter()
    for path in paths:
        with open(path) as fh:
            next(fh, None)
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) < 6:
                    continue
                rows += 1
                name, b, _bms, a, _ams, fst = f[0], f[1], f[2], f[3], f[4], f[5]
                base[b] += 1
                arm[a] += 1
                first[fst] += 1
                if b in DECIDED and a in DECIDED and b != a:
                    flips.append((name, b, a))
                elif b not in DECIDED and a in DECIDED:
                    gains.append((name, a))
                elif b in DECIDED and a not in DECIDED:
                    losses.append((name, b))
    if not rows:
        sys.stderr.write("NO ROWS READ\n")
        return 4

    print("rows=%d  (base-first %d / arm-first %d)"
          % (rows, first.get("base", 0), first.get("arm", 0)))
    print("base : %s" % dict(base))
    print("arm  : %s" % dict(arm))
    print("GAINS  (unknown -> decided): %d of %d" % (len(gains), rows))
    for name, v in gains:
        print("   +%-6s %s" % (v, os.path.basename(name)))
    print("LOSSES (decided -> unknown): %d of %d" % (len(losses), rows))
    for name, v in losses:
        print("   -%-6s %s" % (v, os.path.basename(name)))
    print("sat<->unsat FLIPS: %d" % len(flips))
    for name, b, a in flips:
        print("   !! %s base=%s arm=%s" % (os.path.basename(name), b, a))

    # NON-VACUITY. An arm that did nothing at all reports a perfect zero-diff
    # and reads as a pass, so say so rather than letting the zeros speak.
    if not gains and not losses and not flips:
        print("NOTE: the two arms agree on every row. That is consistent with "
              "the lever changing nothing on this population AND with the arm "
              "never having been enabled -- the two are not distinguishable "
              "from this file. Check the runner's env and the suite's "
              "off_arm/on_arm pair before reading it as a null result.")

    if flips:
        return 3
    if losses:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
