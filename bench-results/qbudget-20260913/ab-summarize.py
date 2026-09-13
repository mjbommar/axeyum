#!/usr/bin/env python3
"""Summarise one interleaved A/B division, and re-derive its census from the
base arm of the SAME runs.

EXITS NON-ZERO on a sat<->unsat flip and on a disagreement with `:status`, in
either arm. A summariser whose exit status does not depend on the finding is a
checker that cannot fail.

Usage: ab-summarize.py <division.tsv> [more.tsv ...]
"""

import collections
import sys

DECIDED = ("sat", "unsat")


def rows(path):
    with open(path, encoding="utf-8") as handle:
        header = handle.readline().rstrip("\n").split("\t")
        for line in handle:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != len(header):
                continue
            yield dict(zip(header, parts))


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    bad = 0
    for path in argv[1:]:
        rs = list(rows(path))
        if not rs:
            print(f"ABORT {path}: no rows")
            return 2
        base = sum(1 for r in rs if r["base"] in DECIDED)
        arm = sum(1 for r in rs if r["arm"] in DECIDED)
        gain = [r for r in rs if r["base"] not in DECIDED and r["arm"] in DECIDED]
        loss = [r for r in rs if r["base"] in DECIDED and r["arm"] not in DECIDED]
        flip = [
            r
            for r in rs
            if r["base"] in DECIDED and r["arm"] in DECIDED and r["base"] != r["arm"]
        ]
        print(f"=== {path}   n={len(rs)}")
        print(
            f"    base {base}   arm {arm}   net {arm - base:+d}   "
            f"gain {len(gain)}   loss {len(loss)}   sat<->unsat flips {len(flip)}"
        )
        for r in flip:
            print(f"    FLIP  {r['file']}  base={r['base']} arm={r['arm']}")
            bad += 1
        # `:status` is the only authority available inside the sweep itself.
        for arm_name in ("base", "arm"):
            checked = dis = 0
            for r in rs:
                if r["status"] in DECIDED and r[arm_name] in DECIDED:
                    checked += 1
                    if r["status"] != r[arm_name]:
                        dis += 1
                        print(
                            f"    DISAGREE({arm_name}) {r['file']} "
                            f"ours={r[arm_name]} :status={r['status']}"
                        )
                        bad += 1
            print(f"    vs :status [{arm_name}]: {checked - dis}/{checked}")
        for r in gain:
            print(f"    GAIN  {r['file']}  -> {r['arm']}  (base giveup: {r['base_giveup'][:64]})")
        for r in loss:
            print(f"    LOSS  {r['file']}  base={r['base']}  (arm giveup: {r['arm_giveup'][:64]})")
        # The re-derived census, from the BASE arm of these same runs.
        fam = collections.Counter()
        for r in rs:
            if r["base"] in DECIDED:
                continue
            fam[r["base_giveup"][:72]] += 1
        print(f"    --- base-arm give-up families ({sum(fam.values())} undecided rows)")
        for detail, n in fam.most_common(8):
            walls = [int(r["base_ms"]) for r in rs if r["base_giveup"][:72] == detail]
            walls.sort()
            med = walls[len(walls) // 2]
            print(f"      {n:4d}  median wall {med:6d} ms  ({24000 - med:+6d} left)  {detail}")
        bnd = collections.Counter(
            r["base_bound_by"] for r in rs if r["base"] not in DECIDED
        )
        print(f"    --- base-arm bound_by on undecided: {bnd.most_common(6)}")
    if bad:
        print(f"\nFAIL: {bad} flip(s)/disagreement(s)")
        return 1
    print("\nOK: no sat<->unsat flip and no :status disagreement in either arm")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
