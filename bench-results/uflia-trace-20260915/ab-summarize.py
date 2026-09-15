#!/usr/bin/env python3
"""UFLIA-TRACE -- summarize the one-binary two-env-value A/B.

    ab-summarize.py <shard.tsv>...

Prints per-division and total counts, the movers, and the exit-status channel.

Three rules this printer follows because each has produced a wrong headline in
this repository:

* **Exit status is its own column.** A run can report `losses=0` by verdict while
  creating new aborts underneath it, so `A_rc`/`B_rc` are counted separately and
  the count is printed whether or not any verdict moved.
* **Every count carries its denominator**, and the denominator is the rows
  ACTUALLY MEASURED -- not the population the run was launched over. A partial
  sweep is reported as a partial sweep, because a division-level delta read off a
  prefix of a path-sorted list is not a sample of the division.
* **A verdict DISAGREEMENT (`sat` on one arm, `unsat` on the other) is reported
  first and is never folded into "movers".** A mover is a decided/undecided
  change; a disagreement is a wrong answer on one side, and one line of output
  must not be able to hide it inside the other.
"""

from __future__ import annotations

import collections
import sys

DECIDED = {"sat", "unsat"}


def division(path: str) -> str:
    return path.split("/", 1)[0]


def main() -> None:
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)

    rows = []
    for p in sys.argv[1:]:
        with open(p, encoding="utf-8") as handle:
            for line in handle:
                f = line.rstrip("\n").split("\t")
                if not f or f[0] == "file" or len(f) < 8:
                    continue
                rows.append(f)

    per: dict[str, collections.Counter[str]] = collections.defaultdict(
        collections.Counter
    )
    gains, losses, flips = [], [], []
    rc_a = rc_b = 0
    for f in rows:
        name, a, a_rc, b, b_rc = f[0], f[1], f[3], f[4], f[6]
        c = per[division(name)]
        c["n"] += 1
        c["A"] += a in DECIDED
        c["B"] += b in DECIDED
        rc_a += a_rc != "0"
        rc_b += b_rc != "0"
        if a in DECIDED and b in DECIDED and a != b:
            flips.append((name, a, b))
        elif a not in DECIDED and b in DECIDED:
            gains.append((name, a, b))
        elif a in DECIDED and b not in DECIDED:
            losses.append((name, a, b))

    print(f"rows measured {len(rows)}")
    print(f"\n{'division':12s} {'n':>5s} {'A':>5s} {'B':>5s} {'delta':>6s}")
    tn = ta = tb = 0
    for d in sorted(per):
        c = per[d]
        print(f"{d:12s} {c['n']:5d} {c['A']:5d} {c['B']:5d} {c['B'] - c['A']:+6d}")
        tn += c["n"]
        ta += c["A"]
        tb += c["B"]
    print(f"{'TOTAL':12s} {tn:5d} {ta:5d} {tb:5d} {tb - ta:+6d}")

    print(f"\nVERDICT DISAGREEMENTS (sat vs unsat): {len(flips)} of {len(rows)}")
    for name, a, b in flips:
        print(f"  FLIP {name} A={a} B={b}")
    print(
        f"raw gains {len(gains)}  raw losses {len(losses)}  -- RAW, not "
        f"re-checked; a single 24 s pairing carries a measured 1-1.5 % ambient "
        f"flip rate on these boxes, so these go through recheck-movers before "
        f"they are an effect"
    )
    for name, a, b in gains:
        print(f"  GAIN {name} A={a} B={b}")
    for name, a, b in losses:
        print(f"  LOSS {name} A={a} B={b}")
    print(f"\nnonzero exit status: A {rc_a} of {len(rows)}, B {rc_b} of {len(rows)}")


if __name__ == "__main__":
    main()
