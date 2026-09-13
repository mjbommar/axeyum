#!/usr/bin/env python3
"""Where the A/B's wall-clock increase actually went, per file.

An aggregate wall delta is not a diagnosis: "+93 % on AUFDTLIRA" is compatible
with every file slowing a little and with a handful of files running the full
budget where they used to refuse in milliseconds. Those are different findings
and only the second is the expected shape of a capability change, so this splits
the delta into the files that GAINED, the files that got slower without gaining,
and everything else.

Usage: wall-cost.py <dir-with-*.tsv>
"""

import glob
import os
import sys


def main() -> int:
    d = sys.argv[1]
    print(f"{'division':11} {'gain Δs':>9} {'gain n':>7} {'slower-no-gain Δs':>18} "
          f"{'n':>4} {'rest Δs':>9} {'total Δs':>9}")
    for p in sorted(glob.glob(os.path.join(d, "*.tsv"))):
        div = os.path.basename(p)[:-4]
        gain_d = rest_d = slow_d = 0.0
        gain_n = slow_n = 0
        worst = []
        with open(p, encoding="utf-8", errors="replace") as fh:
            fh.readline()
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) != 8:
                    continue
                f, base, bs, _, new, ns, _, _ = parts
                try:
                    delta = float(ns) - float(bs)
                except ValueError:
                    continue
                decided = ("sat", "unsat")
                if base not in decided and new in decided:
                    gain_d += delta
                    gain_n += 1
                elif delta > 1.0:
                    slow_d += delta
                    slow_n += 1
                    worst.append((delta, f))
                else:
                    rest_d += delta
        print(f"{div:11} {gain_d:9.1f} {gain_n:7} {slow_d:18.1f} {slow_n:4} "
              f"{rest_d:9.1f} {gain_d + slow_d + rest_d:9.1f}")
        for delta, f in sorted(worst, reverse=True)[:3]:
            print(f"            slower by {delta:6.1f}s, no gain: {f.split('/')[-1][:64]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
