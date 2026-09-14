#!/usr/bin/env python3
"""Summarise an interleaved A/B (`ab-run.sh` shards) and list every mover.

Classification is by DECIDEDNESS, not by string equality: `unknown` is a
first-class result here, so an arm that says `unknown` where the other decided
has not contradicted it (ADR-1957). The three buckets are disjoint:

    flip    both arms decided, and they DIFFER      -- a wrong verdict
    gain    base `unknown`/`none`, arm decided
    loss    base decided, arm `unknown`/`none`

Exit status depends on the finding: any `flip` fails.

Usage: summarize-ab.py <tag> <shard.tsv> [<shard.tsv> ...]
"""
import sys

DECIDED = {"sat", "unsat"}


def main():
    tag = sys.argv[1]
    rows = []
    for path in sys.argv[2:]:
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) < 9 or f[0] == "file":
                    continue
                rows.append(f)
    if not rows:
        print(f"{tag}: NO ROWS -- nothing was measured")
        return 2

    base_dec = sum(1 for r in rows if r[1] in DECIDED)
    arm_dec = sum(1 for r in rows if r[4] in DECIDED)
    flips = [r for r in rows if r[1] in DECIDED and r[4] in DECIDED and r[1] != r[4]]
    gains = [r for r in rows if r[1] not in DECIDED and r[4] in DECIDED]
    losses = [r for r in rows if r[1] in DECIDED and r[4] not in DECIDED]
    base_ms = sum(int(r[2]) for r in rows) / len(rows)
    arm_ms = sum(int(r[5]) for r in rows) / len(rows)

    print(f"{tag}: rows={len(rows)}  base_decided={base_dec}  arm_decided={arm_dec}  "
          f"net={arm_dec - base_dec:+d}")
    print(f"{tag}: gains={len(gains)}  losses={len(losses)}  sat<->unsat_flips={len(flips)}")
    print(f"{tag}: mean_ms base={base_ms:.0f} arm={arm_ms:.0f}  "
          f"delta={arm_ms - base_ms:+.0f}")
    for label, group in (("FLIP", flips), ("GAIN", gains), ("LOSS", losses)):
        for r in group:
            print(f"{tag}\t{label}\t{r[0]}\tbase={r[1]}({r[2]}ms)\tarm={r[4]}({r[5]}ms)"
                  f"\tfirst={r[7]}\tstatus={r[8]}")
    if flips:
        print(f"{tag}: FAIL -- {len(flips)} sat<->unsat flip(s)")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
