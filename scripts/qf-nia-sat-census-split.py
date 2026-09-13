#!/usr/bin/env python3
"""Split the post-ADR-1937 QF_NIA winnable census by POLARITY, then by cause
*within* the sat half -- and within that, by the three failure modes that a
model-finding lane has to tell apart:

  no-model       the search never produced a candidate (gave up / route declined)
  replay-failed  a model was produced and the exact-integer replay rejected it
  too-late       a model was produced and replayed, but past the clock

The three are different failures with different fixes, and the outer `give-up
detail` is what distinguishes them: the replay site in `lia.rs`/`combined.rs` is
the ONLY thing that emits "bounded integer model overflowed at width N
(assertion #K is false over exact integers)".

Method ADRs applied:
  ADR-1950  budget exhaustion is split by WHICH budget, and the remaining-budget
            distribution is published rather than summarised to a mean.
  ADR-1941  `attempts=` cannot classify a row; `bound_by` is the discriminator.
  ADR-1971  the DECLINE TIME is printed beside every class, because a rule added
            to a route that never runs reaches nothing.
"""
import argparse
import collections
import csv
import os
import re
import statistics
import subprocess

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()

# Each pattern maps a raw give-up detail to (honest cause, failure mode).
CLASSES = [
    (re.compile(r"bounded integer model overflowed at width (\d+)"),
     "replay-overflow", "replay-failed"),
    (re.compile(r"integer bit-blast width ladder: wall-clock timeout"),
     "ladder-clock", "no-model"),
    (re.compile(r"estimated (\d+) CNF clauses before lowering exceeds budget"),
     "cnf-budget", "no-model"),
    (re.compile(r"no model within the bounded integer width"),
     "in-range-unsat", "no-model"),
    (re.compile(r"integer constant .*does not fit the bounded width|"
                r"integer constant of \d+ bits is outside"),
     "const-width", "no-model"),
    (re.compile(r"combined-theory timeout after scalar backend"),
     "scalar-clock", "no-model"),
    (re.compile(r"watchdog fired"), "watchdog", "no-model"),
    (re.compile(r"distinct"), "distinct-ingest", "no-model"),
]


def classify(detail):
    for pat, cause, mode in CLASSES:
        if pat.search(detail):
            return cause, mode
    return "OTHER: " + detail[:60], "no-model"


def dist(values):
    if not values:
        return "-"
    v = sorted(values)
    return (f"min {v[0]:.1f} p25 {v[len(v) // 4]:.1f} med {statistics.median(v):.1f} "
            f"p75 {v[3 * len(v) // 4]:.1f} max {v[-1]:.1f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--census", default="bench-results/qf-nia-sat-20260913/census-78.tsv")
    ap.add_argument("--truth", default="bench-results/qf-nia-sat-20260913/remaining-winnable.tsv")
    ap.add_argument("--budget-ms", type=int, default=24000)
    args = ap.parse_args()

    truth = {r["file"]: r["truth"] for r in csv.DictReader(
        open(os.path.join(ROOT, args.truth)), delimiter="\t")}
    rows = list(csv.DictReader(open(os.path.join(ROOT, args.census)), delimiter="\t"))
    for r in rows:
        r["truth"] = truth[r["file"]]
        r["cause"], r["mode"] = classify(r["detail"])

    decided = [r for r in rows if r["verdict"] in ("sat", "unsat")]
    print(f"=== census: {len(rows)} remaining winnable files ===")
    print(f"we now decide {len(decided)} of them "
          f"(census ran on a fresh build of THIS tree, not the board)")
    pol = collections.Counter(r["truth"] for r in rows)
    print(f"polarity: sat {pol['sat']}  unsat {pol['unsat']}")

    print("\n=== POLARITY x FAILURE MODE ===")
    print(f"{'mode':16s} {'sat':>5s} {'unsat':>6s} {'all':>5s}")
    modes = collections.Counter((r["mode"], r["truth"]) for r in rows)
    for m in ("no-model", "replay-failed", "too-late", "decided"):
        s = modes[(m, "sat")]
        u = modes[(m, "unsat")]
        if s or u:
            print(f"{m:16s} {s:5d} {u:6d} {s + u:5d}")

    for pole in ("sat", "unsat"):
        sub = [r for r in rows if r["truth"] == pole]
        print(f"\n=== the {pole.upper()} half: {len(sub)} files, by honest cause ===")
        print(f"{'cause':22s} {'n':>3s}  {'decline time (s, ADR-1971)':38s} {'bound_by (ADR-1941)'}")
        by = collections.Counter(r["cause"] for r in sub)
        for cause, n in by.most_common():
            grp = [r for r in sub if r["cause"] == cause]
            walls = [float(r["wall_s"]) for r in grp]
            bb = collections.Counter(r["bound_by"] for r in grp)
            bbs = " ".join(f"{k}={v}" for k, v in bb.most_common(3))
            print(f"{cause:22s} {n:3d}  {dist(walls):38s} {bbs}")

    # ADR-1950: which budget, and how much of it was left.
    print("\n=== ADR-1950: WHICH budget bound, and what was left of the 24 s ===")
    print(f"{'cause':22s} {'n':>3s}  {'budget consumed by bound_by (ms)':40s} {'total_ms'}")
    for cause, n in collections.Counter(r["cause"] for r in rows).most_common():
        grp = [r for r in rows if r["cause"] == cause]
        bms = [int(r["bound_ms"]) for r in grp if r["bound_ms"] != "-1"]
        tms = [int(r["total_ms"]) for r in grp if r["total_ms"] != "-1"]
        print(f"{cause:22s} {n:3d}  {dist(bms):40s} {dist(tms)}")

    # The scheduling question: on the sat half, how much of the clock is spent by
    # a route that is NOT the one that produces our sat answers (the ladder)?
    print("\n=== the sat half: share of the clock spent OUTSIDE int-blast-ladder ===")
    sat = [r for r in rows if r["truth"] == "sat"]
    for r in sat:
        r["_bms"] = int(r["bound_ms"]) if r["bound_ms"] != "-1" else -1
        r["_tms"] = int(r["total_ms"]) if r["total_ms"] != "-1" else -1
    nonladder = [r for r in sat if r["bound_by"] not in ("int-blast-ladder", "none")]
    print(f"sat files whose LARGEST budget consumer is not the ladder: "
          f"{len(nonladder)} of {len(sat)}")
    bb = collections.Counter(r["bound_by"] for r in sat)
    for k, v in bb.most_common():
        grp = [r for r in sat if r["bound_by"] == k]
        print(f"   bound_by={k:22s} {v:3d} files   bound_ms {dist([r['_bms'] for r in grp if r['_bms'] >= 0])}")

    out = os.path.join(ROOT, "bench-results/qf-nia-sat-20260913/census-78-classified.tsv")
    with open(out, "w", newline="") as fh:
        cols = list(rows[0].keys())
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
