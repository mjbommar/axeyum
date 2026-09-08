#!/usr/bin/env python3
"""Score a warm-decider A/B run.

What this reports, and why it is not a wall-time ratio:

* The population is one axeyum LOSES, so in every arm nearly every file spends
  its whole budget. Wall time is pinned to the timeout and a ratio of 1.00 would
  be an artefact of the harness, not a measurement of the change.
* So the headline is (a) verdict changes and (b) how many live-set decisions the
  lazy loop got through in the SAME budget. A live-set decision is
  `theory_offline_checks + theory_filter_answers`: the rational filter answers
  some live sets outright, so counting only the offline half would score the
  filter's contribution as zero work.
* Files where no arm ever entered the theory are excluded from the throughput
  figures and reported separately -- a mean over files the code never ran on is
  a measurement of the denominator.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import statistics
import sys


def counter(row: dict, key: str) -> int:
    v = row["counters"].get(key)
    try:
        return int(v)
    except (TypeError, ValueError):
        return 0


def has_line(row: dict) -> bool:
    return bool(row["counters"])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", required=True)
    args = ap.parse_args()
    rows = json.load(open(args.rows))

    arms = []
    for r in rows:
        if r["arm"] not in arms:
            arms.append(r["arm"])

    by_file: dict[str, dict[str, dict]] = collections.defaultdict(dict)
    for r in rows:
        by_file[r["file"]][r["arm"]] = r

    print(f"arms: {arms}")
    print(f"files: {len(by_file)}")

    # --- 1. verdicts ------------------------------------------------------
    print("\n== verdicts ==")
    tally = {a: collections.Counter() for a in arms}
    disagreements = []
    flips = []
    for path, per in by_file.items():
        for a in arms:
            if a in per:
                tally[a][per[a]["verdict"]] += 1
        decided = {a: per[a]["verdict"] for a in arms if a in per}
        real = {v for v in decided.values() if v in ("sat", "unsat")}
        if len(real) > 1:
            disagreements.append((path, decided))
        elif real and any(v == "unknown" for v in decided.values()):
            flips.append((path, decided))
    for a in arms:
        print(f"  {a:8s} {dict(tally[a])}")
    print(f"  SOUNDNESS: {len(disagreements)} file(s) where two arms gave different decided verdicts")
    for path, d in disagreements:
        print(f"    !! {os.path.basename(path)} {d}")
    print(f"  coverage changes (decided in one arm, unknown in another): {len(flips)}")
    for path, d in flips:
        print(f"    ~  {os.path.basename(path)} {d}")

    # --- 2. where the theory actually ran ---------------------------------
    def decisions(r: dict) -> int:
        return counter(r, "theory_offline_checks") + counter(r, "theory_filter_answers")

    engaged = [
        p
        for p, per in by_file.items()
        if all(a in per for a in arms) and any(decisions(per[a]) > 0 for a in arms)
    ]
    no_line = [
        p
        for p, per in by_file.items()
        if any(a in per and not has_line(per[a]) for a in arms)
    ]
    print("\n== population the online LIA theory was actually entered on ==")
    print(f"  {len(engaged)} of {len(by_file)} files")
    print(f"  {len(no_line)} file(s) where some arm printed no `; lia-warm` line at all")

    if not engaged:
        print("  nothing to score -- the decider never ran")
        return 0

    # --- 3. throughput ----------------------------------------------------
    print("\n== live-set decisions in the same budget (offline + filter answers) ==")
    totals = {a: 0 for a in arms}
    per_file_ratio: dict[str, list[float]] = {a: [] for a in arms}
    base = arms[0]
    for p in engaged:
        per = by_file[p]
        b = decisions(per[base])
        for a in arms:
            totals[a] += decisions(per[a])
            if b > 0:
                per_file_ratio[a].append(decisions(per[a]) / b)
    for a in arms:
        med = statistics.median(per_file_ratio[a]) if per_file_ratio[a] else float("nan")
        print(
            f"  {a:8s} total={totals[a]:>9d}  "
            f"x{totals[a]/max(totals[base],1):.2f} vs {base}   "
            f"median per-file ratio {med:.2f}"
        )

    print("\n== offline decisions only (the stage the warm cache serves) ==")
    off_totals = {a: sum(counter(by_file[p][a], "theory_offline_checks") for p in engaged) for a in arms}
    for a in arms:
        print(f"  {a:8s} total={off_totals[a]:>9d}  x{off_totals[a]/max(off_totals[base],1):.2f} vs {base}")

    print("\n== the rational filter, where it ran ==")
    for a in arms:
        ans = sum(counter(by_file[p][a], "theory_filter_answers") for p in engaged)
        ref = sum(counter(by_file[p][a], "theory_filter_refuted") for p in engaged)
        print(f"  {a:8s} answered={ans:>9d}  refuted={ref:>9d}")

    print("\n== warm cache behaviour (warm arms only) ==")
    for a in arms:
        checks = sum(counter(by_file[p][a], "checks") for p in engaged)
        if checks == 0:
            print(f"  {a:8s} the warm decider was never entered (cold arm)")
            continue
        warm_u = sum(counter(by_file[p][a], "warm_updates") for p in engaged)
        rebuilds = sum(counter(by_file[p][a], "rebuilds") for p in engaged)
        kept = sum(counter(by_file[p][a], "delta_kept") for p in engaged)
        added = sum(counter(by_file[p][a], "delta_added") for p in engaged)
        removed = sum(counter(by_file[p][a], "delta_removed") for p in engaged)
        copied = sum(counter(by_file[p][a], "constraints_copied") for p in engaged)
        live = sum(counter(by_file[p][a], "constraints_live") for p in engaged)
        coll = sum(counter(by_file[p][a], "literal_collections") for p in engaged)
        hits = sum(counter(by_file[p][a], "literal_cache_hits") for p in engaged)
        print(f"  {a}:")
        print(f"    checks={checks} warm_updates={warm_u} ({100*warm_u/checks:.1f}%) rebuilds={rebuilds}")
        print(f"    literals kept={kept} added={added} removed={removed}"
              f"  -> {100*kept/max(kept+added,1):.1f}% of the live set reused")
        print(f"    constraints copied={copied} of {live} live"
              f"  -> {100*copied/max(live,1):.1f}% rebuilt per check")
        print(f"    literal collections={coll} cache hits={hits}"
              f"  -> {100*hits/max(coll+hits,1):.1f}% hit rate")
        reasons = collections.Counter()
        for p in engaged:
            for k, v in by_file[p][a]["counters"].items():
                if k.startswith("assembly_"):
                    reasons[k] += int(v)
        print(f"    assembly: {dict(reasons)}")

    print("\n== wall time (reported, NOT the score -- the population is budget-bound) ==")
    for a in arms:
        w = [by_file[p][a]["wall_ms"] for p in engaged if by_file[p][a]["wall_ms"]]
        print(f"  {a:8s} total={sum(w)}ms over {len(w)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
