#!/usr/bin/env python3
"""What the 15 round-trip-killed rows were actually building.

These rows reach `simplex-fallback-entry` and die before `dense-rows-built`:
the process is killed materialising the dense `m x nvars` matrix, so under the
BASE arm their `m` and `tableau_cells` are never printed and their post-removal
requirement is unknown.  They are also the rows where removing the round trip is
most likely to decide the outcome, so this re-runs them under
`AXEYUM_LRA_SPARSE_ROWS=1` -- where the row build is O(nnz) and cannot be the
killer -- and reads off the tableau they then try to build.

The question it answers: with the round trip gone, does the tableau alone fit
under the board's 8 GiB ceiling?

Usage: died-shapes.py <harness-dir>
"""

import glob
import gzip
import os
import re
import statistics
import sys

RATIONAL_BYTES = 32
CEILING_GIB = 8.0
MAX_TABLEAU_CELLS = 4_000_000
KV = re.compile(r"(\w+)=(\S+)")


def first(path, site):
    try:
        with gzip.open(path, "rt", errors="replace") as fh:
            for line in fh:
                if f"site={site}" in line:
                    return dict(KV.findall(line))
    except OSError:
        pass
    return {}


def main():
    root = sys.argv[1]
    rows = []
    for tsv in sorted(glob.glob(os.path.join(root, "out", "died.sh*.tsv"))):
        shard = re.search(r"died\.(sh\d+)\.tsv", tsv).group(1)
        logd = os.path.join(root, "logs", f"died-{shard}")
        with open(tsv) as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                r = dict(zip(head, line.rstrip("\n").split("\t")))
                log = os.path.join(logd, r["key"] + ".err.gz")
                r["_fw"] = first(log, "feasible_within-entry")
                r["_rb"] = first(log, "dense-rows-built")
                rows.append(r)

    print(f"rows={len(rows)}  (the 15 that die inside the round-trip build)")
    print("arm: AXEYUM_LRA_SPARSE_ROWS=1, board-identical 8 GiB / 24 s\n")

    reached = [r for r in rows if r["_fw"]]
    print(f"  reached feasible_within under the sparse arm: {len(reached)} of {len(rows)}")
    still_abort = [r for r in rows if r["rc"] == "134"]
    clean = [r for r in rows if r["rc"] != "134"]
    print(f"  STILL ABORT under the sparse arm: {len(still_abort)}")
    print(f"  terminate cleanly under the sparse arm: {len(clean)}")
    decided = [r for r in rows if r["verdict"] in ("sat", "unsat")]
    print(f"  DECIDED under the sparse arm: {len(decided)}   <- the only thing that is a board gain")

    print(
        f"\n{'rc':>4} {'verdict':>8} {'peakGiB':>8} {'nvars':>8} {'m':>8} {'nnz':>9} "
        f"{'roundtripGiB':>13} {'tableauGiB':>11} {'fits8':>6}  file"
    )
    fits = 0
    tabs = []
    for r in sorted(rows, key=lambda x: -int(x["_fw"].get("tableau_cells", 0) or 0)):
        fw, rb = r["_fw"], r["_rb"]
        nv = int(fw.get("nvars", rb.get("nvars", 0)) or 0)
        m = int(fw.get("m", 0) or 0)
        nnz = int(rb.get("nnz", 0) or 0)
        tc = int(fw.get("tableau_cells", 0) or 0)
        dc = int(rb.get("dense_cells", 0) or 0)
        tab = tc * RATIONAL_BYTES / (1024**3)
        rt = dc * RATIONAL_BYTES / (1024**3)
        pk = int(r["maxrss_kb"]) / (1024 * 1024) if r["maxrss_kb"].isdigit() else float("nan")
        ok = "yes" if 0 < tab <= CEILING_GIB else ("na" if tab == 0 else "no")
        if ok == "yes":
            fits += 1
        if tab:
            tabs.append(tab)
        print(
            f"{r['rc']:>4} {r['verdict']:>8} {pk:8.2f} {nv:>8,} {m:>8,} {nnz:>9,} "
            f"{rt:13.2f} {tab:11.2f} {ok:>6}  {os.path.basename(r['file'])[:50]}"
        )

    if tabs:
        print(
            f"\n  the tableau these rows need, with the round trip gone: median "
            f"{statistics.median(tabs):.2f} GiB   min {min(tabs):.2f}   max {max(tabs):.2f}"
        )
        over = sum(1 for r in rows if int(r["_fw"].get("tableau_cells", 0) or 0) > MAX_TABLEAU_CELLS)
        print(f"  of these, over MAX_TABLEAU_CELLS: {over} of {len(reached)} that reported")
    print(f"\n  tableau alone fits the 8 GiB ceiling on {fits} of {len(rows)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
