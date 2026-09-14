#!/usr/bin/env python3
"""Summarize an interleaved A/B.

POLARITY: `base` = AXEYUM_MEMORY_LIMIT_MB unset (the board's configuration,
where every memory admission screen is inert); `arm` = the limit SET to the
value the harness is already enforcing with `ulimit -v`.  A GAIN is a file the
ARM decided and the base did not.

Soundness is checked against the file's declared `:status` in BOTH arms, and
the comparable denominator is printed beside the zero (ADR-1957): a
disagreement count without its denominator is not evidence.
"""

import sys
from collections import Counter

DEC = ("sat", "unsat")


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * ((p * (1 - p) / n + z * z / (4 * n * n)) ** 0.5) / d
    return (max(0.0, c - h), min(1.0, c + h))


def main():
    rows = []
    for path in sys.argv[1:]:
        with open(path) as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))

    base = sum(1 for r in rows if r["base"] in DEC)
    arm = sum(1 for r in rows if r["arm"] in DEC)
    gains = [r for r in rows if r["arm"] in DEC and r["base"] not in DEC]
    losses = [r for r in rows if r["base"] in DEC and r["arm"] not in DEC]
    flips = [r for r in rows if r["base"] in DEC and r["arm"] in DEC and r["base"] != r["arm"]]

    print(f"rows={len(rows)}")
    print(f"base (limit UNSET) = {base}")
    print(f"arm  (limit SET)   = {arm}")
    print(f"net = {arm - base:+d}   gains={len(gains)} losses={len(losses)} flips={len(flips)}")

    # Soundness, both arms, with the denominator.
    comparable = disagree = 0
    for r in rows:
        for a in ("base", "arm"):
            if r[a] in DEC and r["status"] in DEC:
                comparable += 1
                if r[a] != r["status"]:
                    disagree += 1
                    print(f"  DISAGREEMENT {a}={r[a]} status={r['status']} {r['file']}")
    print(f"\nsoundness vs declared :status -- comparable={comparable} disagreements={disagree}")

    # Exit-status distribution: the ABORT bucket is the thing the arm is meant
    # to convert, and it is invisible in a verdict count.
    print(f"\nexit status, base: {Counter(r['base_rc'] for r in rows).most_common()}")
    print(f"exit status, arm : {Counter(r['arm_rc'] for r in rows).most_common()}")
    ab_base = sum(1 for r in rows if r["base_rc"] == "134")
    ab_arm = sum(1 for r in rows if r["arm_rc"] == "134")
    print(f"process ABORTS (rc=134): base={ab_base} arm={ab_arm}  delta={ab_arm - ab_base:+d}")

    if gains:
        print(f"\n== GAINS ({len(gains)}) ==")
        for r in sorted(gains, key=lambda x: x["file"]):
            print(f"  {r['arm']:>5}  base={r['base']}(rc{r['base_rc']},{r['base_ms']}ms) "
                  f"arm_ms={r['arm_ms']} status={r['status']}  "
                  f"{r['file'].split('non-incremental/')[-1]}")
    if losses:
        print(f"\n== LOSSES ({len(losses)}) ==")
        for r in sorted(losses, key=lambda x: x["file"]):
            print(f"  base={r['base']} arm={r['arm']}(rc{r['arm_rc']},{r['arm_ms']}ms) "
                  f"status={r['status']}  {r['file'].split('non-incremental/')[-1]}")
    if flips:
        print(f"\n== FLIPS ({len(flips)}) -- verdict IDENTITY changed ==")
        for r in flips:
            print(f"  base={r['base']} arm={r['arm']} status={r['status']} {r['file']}")

    n = len(gains) + len(losses)
    if n:
        lo, hi = wilson(len(gains), n)
        print(f"\nWilson 95% on gains/(gains+losses) = {len(gains)}/{n}: [{lo:.3f}, {hi:.3f}]")

    # Movers file, for the 3x re-run and the authority check.
    with open("/nas3/data/axeyum/harness/qflra-gap/out/movers.txt", "w") as fh:
        for r in gains + losses + flips:
            fh.write(f"{r['file']}\n")
    print(f"\nmovers written: {len(gains) + len(losses) + len(flips)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
