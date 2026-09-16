#!/usr/bin/env python3
"""QUANT-ACTIVATION -- summarize the interleaved A/B rows (ADR-2120).

    ab-summarize.py <rows.tsv> [<rows.tsv> ...]

WHAT IS PRINTED AND WHY EACH COLUMN IS SEPARATE:

  * decided counts per division and the delta -- the headline;
  * VERDICT DISAGREEMENTS (`sat` on one arm, `unsat` on the other) at their own
    denominator. This is the only column that can indicate a soundness defect,
    and folding it into "delta" would hide one behind a good total;
  * NONZERO EXIT STATUS per arm, counted separately from the verdict. A run can
    report `losses=0` by verdict while creating new aborts underneath it, and
    the two are different failures;
  * raw GAINS and LOSSES, labelled RAW. A single 24 s pairing carries a measured
    1-1.5 % ambient flip rate on these boxes and ADR-1966 lost 11 of its 18
    movers to a re-check, so these are counts and not an effect until
    `recheck-movers.sh` has run over them.

The mover FILES are listed, not just counted, because a re-check needs the names
and because a summary that prints only a number cannot be audited.
"""

import collections
import os
import sys

DIVS = ("AUFDTLIRA", "AUFLIRA", "UF", "UFDTLIRA", "UFLIA", "UFNIA")


def read_rows(paths):
    rows = []
    for p in paths:
        if not os.path.exists(p):
            continue
        with open(p) as fh:
            header = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) != len(header):
                    continue
                rows.append(dict(zip(header, parts)))
    return rows


def division_of(path):
    head = path.split("/", 1)[0]
    return head if head in DIVS else "OTHER"


def main(argv):
    rows = read_rows(argv[1:])
    if not rows:
        print("no rows")
        return 1
    per = collections.defaultdict(lambda: collections.Counter())
    gains, losses, disagree = [], [], []
    rc_a = rc_b = 0
    for r in rows:
        d = division_of(r["file"])
        a, b = r["A"], r["B"]
        per[d]["n"] += 1
        per[d]["A"] += a in ("sat", "unsat")
        per[d]["B"] += b in ("sat", "unsat")
        if r["A_rc"] != "0":
            rc_a += 1
            per[d]["A_rc"] += 1
        if r["B_rc"] != "0":
            rc_b += 1
            per[d]["B_rc"] += 1
        if {a, b} == {"sat", "unsat"}:
            disagree.append(r["file"])
        if a == "unknown" and b in ("sat", "unsat"):
            gains.append(r["file"])
        if b == "unknown" and a in ("sat", "unsat"):
            losses.append(r["file"])

    print("== INTERLEAVED A/B, one binary at two env values ==")
    print("A = AXEYUM_QINST_POSITIVE_PATH unset (shipped)   B = 1")
    print("")
    hdr = ("division", "n", "A", "B", "delta", "A_rc!=0", "B_rc!=0")
    order = [d for d in DIVS if d in per] + [d for d in per if d not in DIVS]
    body = [
        (
            d,
            per[d]["n"],
            per[d]["A"],
            per[d]["B"],
            "%+d" % (per[d]["B"] - per[d]["A"]),
            per[d]["A_rc"],
            per[d]["B_rc"],
        )
        for d in order
    ]
    tot = (
        "TOTAL",
        sum(per[d]["n"] for d in per),
        sum(per[d]["A"] for d in per),
        sum(per[d]["B"] for d in per),
        "%+d" % sum(per[d]["B"] - per[d]["A"] for d in per),
        rc_a,
        rc_b,
    )
    widths = [
        max(len(str(x)) for x in [h] + [r[i] for r in body + [tot]])
        for i, h in enumerate(hdr)
    ]
    print("  ".join(h.ljust(w) for h, w in zip(hdr, widths)))
    for r in body + [tot]:
        print("  ".join(str(x).ljust(w) for x, w in zip(r, widths)))
    print("")
    print("VERDICT DISAGREEMENTS (sat on one arm, unsat on the other): %d of %d"
          % (len(disagree), len(rows)))
    for f in disagree:
        print("  DISAGREE %s" % f)
    print("")
    print("RAW movers, NOT re-checked -- a single 24 s pairing carries a measured")
    print("1-1.5 % ambient flip rate and ADR-1966 lost 11 of 18 movers to a re-check.")
    print("  gains  %d" % len(gains))
    for f in gains:
        print("    GAIN %s" % f)
    print("  losses %d" % len(losses))
    for f in losses:
        print("    LOSS %s" % f)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
