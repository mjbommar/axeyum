#!/usr/bin/env python3
"""Report run-to-run spread from repeated identical runs, per file and per arm.

Usage:
    python3 scripts/inprocess-cost-variance-report.py <variance.jsonl> [...]

WHAT THE SPREAD IS BEING ASKED

Two explanations for "inprocessing does not pay inside 24 s" need opposite work:

  (A) the passes are expensive at any budget — repeated identical runs agree;
  (B) a wall-clock cutoff halts a pass part-way, after its setup and before its
      benefit — the same instance at the same budget then varies run to run.

So the columns that matter are max/min of wall time, whether the VERDICT ever
changed across repeats, and whether the pass's truncation flag ever changed
across repeats. That last one is the sharpest: a file where `bve_deadline_expired`
is 1 on some repeats and 0 on others is (B) caught directly, without inferring it
from a timing spread that host load could equally explain.

But only a 1-versus-0 disagreement between runs that BOTH reported the flag
counts. A run the watchdog killed returns no counters at all, so its flag is
ABSENT — "we do not know whether the pass was cut off", not "it was not".
Counting absence as zero manufactures exactly the finding this script exists to
test for, which is why the missing runs are reported in their own column instead.

A verdict that flips across identical repeats is reported on its own line. It is
not a soundness problem (an undecided run reports `unknown`), but it is the thing
that makes a solved-count at this budget a coin flip rather than a measurement.
"""

import json
import statistics
import sys


def counter(row, key):
    return row.get("counters", {}).get(key)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    groups = {}
    total = 0
    for path in sys.argv[1:]:
        for line in open(path, encoding="utf-8"):
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            total += 1
            groups.setdefault((r["arm"], r["file"]), []).append(r)
    if not total:
        print("FAIL: no rows — this measured nothing", file=sys.stderr)
        return 1
    print(f"{total} runs, {len(groups)} (arm, file) groups\n")

    print("| arm | repeats | verdicts | min ms | median ms | max ms | max/min | bve trunc | load min-max | file |")
    print("|---|---:|---|---:|---:|---:|---:|---|---|---|")
    flips = []
    trunc_flips = []
    spreads = {}
    for (arm, f), rows in sorted(groups.items()):
        walls = [r["wall_ms"] for r in rows]
        verdicts = sorted({r["verdict"] for r in rows})
        # ABSENT IS NOT ZERO, and conflating them manufactures a finding. A run
        # the watchdog killed returns no counters at all, so its flag is missing
        # — that is "we do not know whether the pass was cut off", not "it was
        # not". Counted separately; only a genuine 0-vs-1 disagreement between
        # runs that BOTH reported is a flip.
        reported = [counter(r, "bve_deadline_expired") for r in rows]
        truncs = sorted({str(v) for v in reported if v is not None})
        missing = sum(1 for v in reported if v is None)
        loads = [r.get("load", 0.0) for r in rows]
        ratio = max(walls) / max(min(walls), 1)
        spreads.setdefault(arm, []).append(ratio)
        if len(verdicts) > 1:
            flips.append((arm, f, verdicts, walls))
        if len(truncs) > 1:
            trunc_flips.append((arm, f, truncs, walls))
        print(
            f"| {arm} | {len(rows)} | {'/'.join(verdicts)} | {min(walls)} | "
            f"{statistics.median(walls):.0f} | {max(walls)} | {ratio:.2f}x | "
            f"{'/'.join(truncs) if truncs else '-'}{f' (+{missing} no data)' if missing else ''} | "
            f"{min(loads):.1f}-{max(loads):.1f} | {f.split('/')[-1]} |"
        )

    print("\n## summary")
    for arm, r in sorted(spreads.items()):
        print(
            f"  {arm:8s} n={len(r):2d} groups  median max/min {statistics.median(r):.2f}x  "
            f"worst {max(r):.2f}x"
        )
    print(f"\n## verdict flipped across identical repeats: {len(flips)}")
    for arm, f, v, w in flips:
        print(f"  {arm}: {f.split('/')[-1]} -> {v}  walls {w}")
    print(
        f"\n## BVE truncation flag DISAGREED between two runs that both reported it: "
        f"{len(trunc_flips)}"
    )
    for arm, f, t, w in trunc_flips:
        print(f"  {arm}: {f.split('/')[-1]} -> bve_deadline_expired {t}  walls {w}")
    if not trunc_flips:
        print(
            "  none — on every file where the flag was reported at all, the pass was\n"
            "  either always cut off or never was. Truncation here is deterministic\n"
            "  saturation, not a race the clock sometimes wins."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
