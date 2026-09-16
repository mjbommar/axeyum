#!/usr/bin/env python3
"""ADR-2132 sizing: the builds-per-file distribution, and where the movers sit in it.

The lever ADR-2125 built wins where the cubes are MANY and SMALL and loses where
they are FEW and LARGE, and it named the axis: `simplex_cold_builds`, a counter
the route trail already renders.  This reads that counter per file and answers
the two questions a screen needs before it can be written:

  1. what does the distribution look like, per division; and
  2. where do ADR-2125's one STABLE-GAIN and two STABLE-LOSSes fall in it.

A row that never reached the lazy-SMT loop reports NOTHING about this counter,
not zero.  The two are kept apart everywhere below -- ADR-2125's sizing had 20
such rows out of 200 and folding them in makes every share smaller for a reason
that has nothing to do with re-solving.  `SILENT` is printed as its own bucket.

Usage: builds-histogram.py <label>=<sizing.tsv>[,<sizing.tsv>...] ...
"""

import sys
from pathlib import Path

# ADR-2125 section 6.5.  Three raw movers, each re-checked 3x per arm.
MOVERS = {
    "QF_LRA/latendresse/ecoliMILPglycerolYices3-50000.smt2": "STABLE-LOSS",
    "QF_LRA/sc/sc-14.induction.cvc.smt2": "STABLE-GAIN",
    "QF_LRA/uart/uart-8.induction.cvc.smt2": "STABLE-LOSS",
}

# Bucket edges are powers of four from 1, so the two shapes the ADR named --
# "28 builds" and "850-1,050 builds" -- land in different buckets by a wide
# margin rather than by a boundary chosen after seeing them.
EDGES = [1, 4, 16, 64, 256, 1024, 4096]

THRESHOLD_PROBES = (1, 4, 16, 32, 64, 100, 128, 200, 256, 512)


def bucket(n):
    lo = None
    for e in EDGES:
        if n < e:
            break
        lo = e
    if lo is None:
        return "0"
    idx = EDGES.index(lo)
    hi = EDGES[idx + 1] - 1 if idx + 1 < len(EDGES) else None
    return f"{lo}-{hi}" if hi is not None else f"{lo}+"


def bucket_order():
    out = ["0"]
    for i, e in enumerate(EDGES):
        out.append(f"{e}-{EDGES[i + 1] - 1}" if i + 1 < len(EDGES) else f"{e}+")
    return out


def read(paths):
    rows = []
    for p in paths:
        with open(p, encoding="utf-8", errors="replace") as fh:
            head = fh.readline().rstrip("\n").split("\t")
            try:
                ib = head.index("cold_builds")
            except ValueError:
                print(f"   (no `cold_builds` column in {p})")
                continue
            iv = head.index("verdict")
            it = head.index("total_ms")
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) <= ib:
                    continue
                raw = f[ib].strip()
                rows.append(
                    {
                        "file": f[0],
                        "verdict": f[iv] if len(f) > iv else "",
                        "total_ms": f[it].strip() if len(f) > it else "",
                        # "" is SILENT: the trail line was absent.  Not zero.
                        "builds": None if raw == "" else int(raw),
                    }
                )
    return rows


def report(label, rows):
    silent = [r for r in rows if r["builds"] is None]
    spoke = [r for r in rows if r["builds"] is not None]
    print(f"== {label}: {len(rows)} rows | {len(spoke)} reached the loop | {len(silent)} SILENT")
    if not spoke:
        print("   (no row reached the lazy-SMT loop)\n")
        return
    counts = {}
    for r in spoke:
        counts[bucket(r["builds"])] = counts.get(bucket(r["builds"]), 0) + 1
    for b in bucket_order():
        if b in counts:
            print(f"   builds {b:>10}  {counts[b]:>4}  {'#' * min(counts[b], 60)}")
    vals = sorted(r["builds"] for r in spoke)
    nz = [v for v in vals if v > 0]

    def pct(p):
        return vals[min(len(vals) - 1, int(p * len(vals)))]

    print(
        f"   builds: min {vals[0]}  p25 {pct(0.25)}  median {pct(0.50)}"
        f"  p75 {pct(0.75)}  p90 {pct(0.90)}  max {vals[-1]}"
        f"   |  >0: {len(nz)} rows"
    )
    for t in THRESHOLD_PROBES:
        at = sum(1 for v in vals if v >= t)
        print(
            f"     at or above {t:>5} builds: {at:>4} of {len(spoke)} that spoke"
            f"  ({at * 100.0 / len(spoke):.1f} %)"
        )
    for r in rows:
        if r["file"] in MOVERS:
            b = "SILENT" if r["builds"] is None else r["builds"]
            print(
                f"   MOVER {MOVERS[r['file']]:<12} builds={b:<8}"
                f" total_ms={r['total_ms']:<8} {r['file']}"
            )
    print()


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    for arg in sys.argv[1:]:
        label, _, paths = arg.partition("=")
        ps = [Path(p) for p in paths.split(",")]
        missing = [p for p in ps if not p.is_file()]
        if missing:
            print(f"== {label}: NOT MEASURED -- missing {', '.join(str(m) for m in missing)}\n")
            continue
        report(label, read(ps))
    return 0


if __name__ == "__main__":
    sys.exit(main())
