"""Capability + soundness inventory over raw execution results.

Reads one or more raw-result JSON files (from `compete.py --dump-raw`, possibly
sharded) and produces a complete per-logic map for one solver:

  decided-correct : sat/unsat that agrees with the benchmark :status
                    (or the status is unknown, treated as correct)
  WRONG           : sat/unsat that DISAGREES with a known :status  <-- soundness
  declined        : the solver returned `unknown` (honest non-answer)
  no-answer       : timed out / aborted with no verdict

This is the "complete inventory" view: what the solver can decide across the
library, and — most importantly — whether it is ever wrong.

Usage:
    python3 inventory.py raw_0.json raw_1.json ... --solver axeyum \
        [--ceiling-s 900] [--out inventory.json]
"""

from __future__ import annotations

import argparse
import json
import os
from collections import defaultdict


def classify(reported, expected):
    if reported is None:
        return "no_answer"
    if reported == "unknown":
        return "declined"
    # reported is sat/unsat
    if expected is None:
        return "decided_correct"  # unknown status -> any decision counts
    return "decided_correct" if reported == expected else "WRONG"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("raw", nargs="+", help="raw-result JSON files")
    ap.add_argument("--solver", default="axeyum")
    ap.add_argument("--ceiling-s", type=float, default=None,
                    help="flag benchmarks whose wall time reached this ceiling")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    # logic -> class -> count ; plus solved-time stats and wrong/straggler lists
    per_logic: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    wrong: list[dict] = []
    stragglers: list[dict] = []
    solved_times: dict[str, list[float]] = defaultdict(list)
    n_total = 0

    for path in args.raw:
        with open(path, "r", encoding="utf-8") as fh:
            blob = json.load(fh)
        for bench, by_solver in blob.items():
            d = by_solver.get(args.solver)
            if d is None:
                continue
            n_total += 1
            logic = d["logic"]
            cls = classify(d["reported_status"], d["expected_status"])
            per_logic[logic][cls] += 1
            per_logic[logic]["total"] += 1
            if cls == "WRONG":
                wrong.append({
                    "benchmark": bench,
                    "logic": logic,
                    "reported": d["reported_status"],
                    "expected": d["expected_status"],
                })
            if cls == "decided_correct":
                solved_times[logic].append(d["wall_time"])
            if args.ceiling_s and d["wall_time"] >= args.ceiling_s - 5:
                stragglers.append({"benchmark": bench, "logic": logic,
                                   "wall": round(d["wall_time"], 1)})

    # --- report ---
    print(f"\n{'='*74}")
    print(f"AXEYUM COMPLETE INVENTORY  solver={args.solver}  benchmarks={n_total}")
    print("=" * 74)
    hdr = f"{'logic':<12} {'N':>5} {'correct':>8} {'declined':>9} {'no-ans':>7} {'WRONG':>6} {'decide%':>8}"
    print(hdr)
    print("-" * 74)
    agg = defaultdict(int)
    for logic in sorted(per_logic):
        c = per_logic[logic]
        N = c["total"]
        correct = c["decided_correct"]
        declined = c["declined"]
        noans = c["no_answer"]
        w = c["WRONG"]
        for k in ("total", "decided_correct", "declined", "no_answer", "WRONG"):
            agg[k] += c[k]
        decide_pct = 100.0 * correct / N if N else 0.0
        print(f"{logic:<12} {N:>5} {correct:>8} {declined:>9} {noans:>7} {w:>6} {decide_pct:>7.1f}%")
    print("-" * 74)
    N = agg["total"]
    print(f"{'ALL':<12} {N:>5} {agg['decided_correct']:>8} {agg['declined']:>9} "
          f"{agg['no_answer']:>7} {agg['WRONG']:>6} "
          f"{100.0*agg['decided_correct']/N if N else 0:>7.1f}%")

    print(f"\nSOUNDNESS: {agg['WRONG']} wrong answer(s) "
          f"{'<<< INVESTIGATE' if agg['WRONG'] else 'across the whole inventory — clean'}")
    for w in wrong:
        print(f"  WRONG {w['logic']} {os.path.basename(w['benchmark'])}: "
              f"said {w['reported']}, status {w['expected']}")

    # solved-time distribution
    print("\nsolved-time (decided-correct) wall seconds, per logic:")
    for logic in sorted(solved_times):
        ts = sorted(solved_times[logic])
        if not ts:
            continue
        med = ts[len(ts) // 2]
        print(f"  {logic:<12} n={len(ts):>4}  min={ts[0]:.2f}  med={med:.2f}  max={ts[-1]:.2f}")

    if args.ceiling_s:
        print(f"\nstragglers at/near the {args.ceiling_s:.0f}s ceiling "
              f"(candidates for a higher-limit re-run): {len(stragglers)}")
        for s in sorted(stragglers, key=lambda x: -x["wall"])[:20]:
            print(f"  {s['logic']} {os.path.basename(s['benchmark'])}  {s['wall']}s")

    if args.out:
        report = {
            "solver": args.solver,
            "n_total": n_total,
            "per_logic": {k: dict(v) for k, v in per_logic.items()},
            "aggregate": dict(agg),
            "wrong": wrong,
            "stragglers": stragglers,
        }
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2)
        print(f"\nwrote {args.out}")
    return 1 if agg["WRONG"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
