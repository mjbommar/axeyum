#!/usr/bin/env python3
"""Split the offline dense LRA route's peak RSS between its allocation sites.

ADR-2045 measured a 5.07 GiB median peak RSS over the QF_LRA undecided rows and
named two allocations on this route, but could price neither: `/usr/bin/time -v`
reports one number for the whole process.

This reads the `AXEYUM_LRADENSEPROBE` logs and reports, per file and over the
population:

  round-trip  the dense `m x nvars` matrix `lra.rs` built and `Tableau::new`
              immediately re-sparsified  (site `dense-rows-built` minus
              `simplex-fallback-entry`)
  tableau     the dense `m x (nvars+m)` tableau  (site `tableau-built` minus
              `feasible_within-entry`)
  rest        peak RSS minus the two, i.e. arena, skeleton, CNF, everything else

Two independent estimates are printed side by side and must agree, because
either alone could be wrong in a way the other is not:

  MEASURED    resident-set deltas across the probe points
  ARITHMETIC  cells x 32 bytes (`Rational` is two `i128`s, `Copy`)

A row that DIES in the tableau allocation still reports its shape, because the
shape is printed at `feasible_within-entry`, before the allocation. Its
`tableau` measured delta is `na` and only the arithmetic is available -- that is
stated per row rather than silently dropped.

Usage: profile.py <out-dir-with-profile.sh*.tsv-and-logs...>
"""

import glob
import gzip
import os
import re
import statistics
import sys

RATIONAL_BYTES = 32  # two i128s, Copy -- ADR-1702 keeps promoted values out of line
MAX_TABLEAU_CELLS = 4_000_000
KV = re.compile(r"(\w+)=(\S+)")


def episodes(path):
    """Every offline simplex solve in one probe log, in order.

    Segmented on `simplex-fallback-entry`, which is the route's entry; a file
    commonly enters it many times (once per cube), and the PEAK is set by the
    largest, not the first.
    """
    out, cur = [], None
    try:
        with gzip.open(path, "rt", errors="replace") as fh:
            lines = fh.readlines()
    except OSError:
        return out
    for line in lines:
        if "LRADENSEPROBE" not in line:
            continue
        kv = dict(KV.findall(line))
        site = kv.get("site")
        if site == "simplex-fallback-entry":
            if cur:
                out.append(cur)
            cur = {"entry": kv}
        elif cur is not None:
            cur[site] = kv
    if cur:
        out.append(cur)
    return out


def num(d, key):
    try:
        return int(d[key])
    except (KeyError, ValueError, TypeError):
        return None


def rss(ep, site):
    return num(ep.get(site, {}), "rss_kb")


def main():
    rows = []
    for d in sys.argv[1:]:
        for tsv in sorted(glob.glob(os.path.join(d, "out", "profile.sh*.tsv"))):
            shard = re.search(r"profile\.(sh\d+)\.tsv", tsv).group(1)
            logd = os.path.join(d, "logs", f"prof-{shard}")
            with open(tsv) as fh:
                head = fh.readline().rstrip("\n").split("\t")
                for line in fh:
                    r = dict(zip(head, line.rstrip("\n").split("\t")))
                    r["_log"] = os.path.join(logd, r["key"] + ".err.gz")
                    rows.append(r)

    print(f"rows={len(rows)}")
    recs = []
    for r in rows:
        eps = episodes(r["_log"])
        if not eps:
            recs.append({**r, "shape": None, "neps": 0})
            continue
        # The episode with the largest tableau -- it sets the peak.
        def cells(ep):
            return num(ep.get("feasible_within-entry", {}), "tableau_cells") or 0

        ep = max(eps, key=cells)
        nvars = num(ep["entry"], "nvars")
        m = num(ep.get("dense-rows-built", {}), "m")
        nnz = num(ep.get("dense-rows-built", {}), "nnz")
        tcells = cells(ep)
        dcells = num(ep.get("dense-rows-built", {}), "dense_cells")
        rt_meas = None
        if rss(ep, "dense-rows-built") is not None and rss(ep, "entry") is not None:
            rt_meas = rss(ep, "dense-rows-built") - rss(ep, "entry")
        tb_meas = None
        if rss(ep, "tableau-built") is not None and rss(ep, "feasible_within-entry") is not None:
            tb_meas = rss(ep, "tableau-built") - rss(ep, "feasible_within-entry")
        recs.append(
            {
                **r,
                "neps": len(eps),
                "shape": True,
                "nvars": nvars,
                "m": m,
                "nnz": nnz,
                "dense_cells": dcells,
                "tableau_cells": tcells,
                "rt_meas_kb": rt_meas,
                "tb_meas_kb": tb_meas,
                "rt_arith_kb": (dcells * RATIONAL_BYTES // 1024) if dcells else None,
                "tb_arith_kb": (tcells * RATIONAL_BYTES // 1024) if tcells else None,
            }
        )

    shaped = [r for r in recs if r["shape"]]
    print(f"rows reaching the offline simplex (shape reported) = {len(shaped)} of {len(recs)}")
    noshape = [r for r in recs if not r["shape"]]
    if noshape:
        print(f"  rows with NO probe episode = {len(noshape)}  (route never entered)")
        for r in noshape[:8]:
            print(f"    rc={r['rc']:>3} {r['verdict']:>7} {os.path.basename(r['file'])}")

    if not shaped:
        print("NO SHAPED ROWS -- the profile measured nothing; not a negative result.")
        return 1

    def med(key):
        vals = [r[key] for r in shaped if r.get(key) is not None]
        return statistics.median(vals) if vals else None

    print("\n== the shape of the systems handed to the dense engine ==")
    print(f"  nvars          median {med('nvars'):>12,.0f}")
    print(f"  m (rows)       median {med('m'):>12,.0f}")
    print(f"  nnz (real data)median {med('nnz'):>12,.0f}")
    print(f"  dense_cells    median {med('dense_cells'):>12,.0f}   (the round trip, m x nvars)")
    print(f"  tableau_cells  median {med('tableau_cells'):>12,.0f}   (the tableau, m x (nvars+m))")

    dens = [
        100.0 * r["nnz"] / r["tableau_cells"]
        for r in shaped
        if r.get("nnz") and r.get("tableau_cells")
    ]
    if dens:
        print(
            f"\n  tableau DENSITY (nnz / cells): median {statistics.median(dens):.4f} %"
            f"   min {min(dens):.4f} %   max {max(dens):.4f} %"
        )

    over = [r for r in shaped if (r["tableau_cells"] or 0) > MAX_TABLEAU_CELLS]
    print(
        f"\n  rows whose tableau exceeds MAX_TABLEAU_CELLS ({MAX_TABLEAU_CELLS:,}):"
        f" {len(over)} of {len(shaped)}"
    )
    if over:
        ratios = sorted((r["tableau_cells"] / MAX_TABLEAU_CELLS) for r in over)
        print(
            f"    over by: median {statistics.median(ratios):.1f}x  "
            f"min {ratios[0]:.1f}x  max {ratios[-1]:.1f}x"
        )

    print("\n== THE SPLIT: what fraction of the two allocations is the round trip? ==")
    for label, a, b in (
        ("ARITHMETIC (cells x 32B)", "rt_arith_kb", "tb_arith_kb"),
        ("MEASURED   (RSS deltas)", "rt_meas_kb", "tb_meas_kb"),
    ):
        fr = [
            100.0 * r[a] / (r[a] + r[b])
            for r in shaped
            if r.get(a) and r.get(b) and (r[a] + r[b]) > 0
        ]
        if fr:
            print(
                f"  {label}: n={len(fr):>3}  round-trip share median {statistics.median(fr):5.1f} %"
                f"   min {min(fr):4.1f} %   max {max(fr):4.1f} %"
            )
        else:
            print(f"  {label}: n=0  -- DID NOT MEASURE (no row reported both sites)")

    # Against the WHOLE process, which is what the 8 GiB ceiling actually bounds.
    peak = [
        (r, int(r["maxrss_kb"]))
        for r in shaped
        if r.get("maxrss_kb", "na").isdigit() and r.get("rt_arith_kb")
    ]
    if peak:
        share = sorted(100.0 * r["rt_arith_kb"] / p for r, p in peak)
        print(
            f"\n  round trip as a share of PEAK PROCESS RSS: n={len(share)}  "
            f"median {statistics.median(share):.1f} %   "
            f"min {share[0]:.1f} %   max {share[-1]:.1f} %"
        )
        big = sum(1 for s in share if s >= 10.0)
        print(f"    rows where it is >= 10 % of peak: {big} of {len(share)}")

    peaks = [int(r["maxrss_kb"]) for r in recs if r.get("maxrss_kb", "na").isdigit()]
    if peaks:
        print(
            f"\n  peak process RSS over these rows: median "
            f"{statistics.median(peaks) / (1024 * 1024):.2f} GiB   "
            f"max {max(peaks) / (1024 * 1024):.2f} GiB"
        )

    aborts = sum(1 for r in recs if r["rc"] == "134")
    print(f"\n  process ABORTS (rc=134): {aborts} of {len(recs)}")
    print(f"  episodes per file: median {statistics.median([r['neps'] for r in recs]):.0f}")

    # The two halves do NOT have the same answer, and averaging them hides it.
    # A row that ABORTS never finished its tableau, so its `tb_arith` is what it
    # WANTED, not what it got: the bytes it actually held at death are its peak
    # RSS, and the round trip is fully inside that. A row that spent the CLOCK
    # did build the tableau, so both figures are bytes that really existed.
    print("\n== the two halves answer differently, so they are split ==")
    ab = [r for r in shaped if r["rc"] == "134"]
    ck = [r for r in shaped if r["rc"] != "134"]
    for label, group in (("ABORT (rc=134)", ab), ("CLOCK (terminated)", ck)):
        if not group:
            print(f"  {label}: n=0")
            continue
        share = sorted(
            100.0 * r["rt_arith_kb"] / int(r["maxrss_kb"])
            for r in group
            if r.get("rt_arith_kb") and r["maxrss_kb"].isdigit()
        )
        need = sorted((r["tb_arith_kb"] or 0) / (1024 * 1024) for r in group)
        print(
            f"  {label}: n={len(group)}   round trip as a share of the bytes the "
            f"process ACTUALLY held: median {statistics.median(share):.1f} %"
            f"  (min {share[0]:.1f}, max {share[-1]:.1f})"
        )
        print(
            f"      the tableau it was building needs: median "
            f"{statistics.median(need):.2f} GiB   min {need[0]:.2f}   max {need[-1]:.2f}"
        )

    # THE PREDICTION, made before the A/B and testable by it.
    #
    # Removing the round trip frees exactly `rt_arith` bytes.  A row then fits
    # the board's 8 GiB ceiling only if everything else it needs still fits:
    # the tableau in full, plus whatever the process held besides the round trip.
    CEILING_KB = 8 * 1024 * 1024
    fits = []
    for r in shaped:
        if not (r.get("tb_arith_kb") and r["maxrss_kb"].isdigit()):
            continue
        rest = int(r["maxrss_kb"]) - (r["rt_arith_kb"] or 0)  # arena, skeleton, CNF, ...
        if r["rc"] == "134":
            # An aborting row's peak UNDERSTATES the tableau it had begun, so
            # `rest` is an over-estimate of the non-tableau part only if the
            # tableau had already grown.  Use the conservative form: assume the
            # process held nothing of the tableau yet, which FAVOURS the lever.
            need = max(rest, 0) + r["tb_arith_kb"]
        else:
            need = max(rest - (r["tb_arith_kb"] or 0), 0) + r["tb_arith_kb"]
        fits.append((r, need))
    would_fit = [r for r, need in fits if need <= CEILING_KB and r["rc"] == "134"]
    print(
        f"\n== PREDICTION (pre-A/B): of the {len(ab)} aborting rows, removing the "
        f"round trip lets {len(would_fit)} fit under the 8 GiB ceiling =="
    )
    print("   Conservative in the lever's FAVOUR: the aborting rows are credited")
    print("   with holding none of the tableau at the moment they died.")
    for r, need in sorted(fits, key=lambda x: x[1])[:6]:
        print(
            f"     needs {need / (1024 * 1024):8.2f} GiB  rc={r['rc']:>3}  "
            f"{os.path.basename(r['file'])[:64]}"
        )

    print("\n== per row ==")
    print(
        f"{'rc':>3} {'verdict':>7} {'peakGiB':>8} {'nvars':>7} {'m':>7} {'nnz':>9} "
        f"{'dense_MB':>9} {'tab_MB':>10} {'rt%':>6}  file"
    )
    for r in sorted(recs, key=lambda x: -(x.get("tableau_cells") or 0)):
        if not r["shape"]:
            print(f"{r['rc']:>3} {r['verdict']:>7} {'':>8} {'-- no probe episode --':>52}  "
                  f"{os.path.basename(r['file'])}")
            continue
        pk = int(r["maxrss_kb"]) / (1024 * 1024) if r["maxrss_kb"].isdigit() else float("nan")
        rt = r["rt_arith_kb"] or 0
        tb = r["tb_arith_kb"] or 0
        pct = 100.0 * rt / (rt + tb) if (rt + tb) else float("nan")

        # A row can report `simplex-fallback-entry` and then die (or decline)
        # before `dense-rows-built`, so `m`/`nnz` are absent. Print the gap
        # rather than crash on it: a missing field is a finding about that row.
        def fmt(v, w):
            return f"{v:>{w},}" if isinstance(v, int) else f"{'na':>{w}}"

        print(
            f"{r['rc']:>3} {r['verdict']:>7} {pk:8.2f} {fmt(r['nvars'], 7)} {fmt(r['m'], 7)} "
            f"{fmt(r['nnz'], 9)} {rt / 1024:9.1f} {tb / 1024:10.1f} {pct:5.1f}%  "
            f"{os.path.basename(r['file'])}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
