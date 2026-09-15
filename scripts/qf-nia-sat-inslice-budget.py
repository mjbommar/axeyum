#!/usr/bin/env python3
"""The sizing bracket, measured against the clock an in-solver rung would really
have -- using the per-route `route-trail` timings rather than the whole-process
wall clock.

The surrogate ran the WHOLE ladder on the transformed file with a fresh 24 s
budget, so its wall time charges routes that would have run anyway.  What an
eager small-domain split actually changes is the query handed to
`int-blast-ladder`; every route before it still runs, on the ORIGINAL query, and
still costs what the census says it costs.  So the condition for a file to
convert is

    ladder_elapsed(transformed)  <=  24 s - total_ms(original)

both sides measured, neither assumed.  Reporting the surrogate's wall time
instead would have understated the bracket by charging the split for
`int-real-relax` and `nia-linearize`, which it does not remove.
"""
import argparse
import csv
import os
import subprocess
import sys
import time

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
D = os.path.join(ROOT, "bench-results/qf-nia-sat-20260913")
BUDGET_MS = 24000
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import route_trace_reader as rtr  # noqa: E402


def trail_of(cli, path, budget_ms):
    p = subprocess.run(["timeout", "-k", "5", "180", cli, path,
                        "--timeout-ms", str(budget_ms), "--trace"],
                       capture_output=True, text=True)
    out = p.stdout + p.stderr
    verdict = "none"
    for line in out.splitlines():
        if line.strip() in ("sat", "unsat", "unknown"):
            verdict = line.strip()
    # The shared reader (ADR-2101). The regex this replaces was anchored at
    # `^; route-trail `, which the watchdog path never prints -- it prints
    # `; partial route-trail ` -- so a file killed mid-search returned an
    # EMPTY per-route budget and read as "no route cost anything".
    found = None
    for line in out.splitlines():
        if line.startswith(rtr.TRAIL_PREFIX) or line.startswith(
            rtr.PARTIAL_TRAIL_PREFIX
        ):
            found = line
    if found is None:
        return verdict, {}
    try:
        trail = rtr.parse_trail_line(found, path)
    except rtr.RouteTraceError:
        return verdict, {}
    per = {}
    for a in trail.attempts:
        per[a.route] = per.get(a.route, 0) + (a.elapsed_ns or 0) / 1e6
    return verdict, per


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cli", required=True)
    ap.add_argument("--lindir", required=True)
    ap.add_argument("--out", default=os.path.join(D, "inslice-budget.tsv"))
    args = ap.parse_args()

    sur = {r["file"]: r for r in csv.DictReader(
        open(os.path.join(D, "eager-split-surrogate-29.tsv")), delimiter="\t")}
    cen = {r["file"]: r for r in csv.DictReader(
        open(os.path.join(D, "census-78-classified.tsv")), delimiter="\t")}

    rows = []
    for path, r in sur.items():
        if r["ours"] not in ("sat", "unsat"):
            continue
        lin = os.path.join(args.lindir, os.path.basename(path))
        t0 = time.time()
        verdict, per = trail_of(args.cli, lin, BUDGET_MS)
        ladder_ms = per.get("int-blast-ladder", -1.0)
        spent_ms = int(cen[path]["total_ms"])
        left_ms = BUDGET_MS - spent_ms
        rows.append({
            "file": path, "verdict": verdict,
            "ladder_ms_transformed": round(ladder_ms, 1),
            "pre_ladder_ms_original": spent_ms,
            "left_ms": left_ms,
            "fits": "yes" if 0 <= ladder_ms <= left_ms else "NO",
            "wall_s": round(time.time() - t0, 1),
        })

    rows.sort(key=lambda r: r["ladder_ms_transformed"])
    print(f"{'verdict':8s} {'ladder(T) ms':>13s} {'pre-ladder(O) ms':>17s} "
          f"{'left ms':>8s} {'fits':>5s}  file")
    for r in rows:
        print(f"{r['verdict']:8s} {r['ladder_ms_transformed']:13.1f} "
              f"{r['pre_ladder_ms_original']:17d} {r['left_ms']:8d} "
              f"{r['fits']:>5s}  {os.path.basename(r['file'])[:50]}")

    fits = sum(1 for r in rows if r["fits"] == "yes")
    print(f"\n=== in-solver bracket: {fits} of 29 cnf-budget sat files convert ===")
    print("    condition: ladder time on the TRANSFORMED query fits the budget the")
    print("    ORIGINAL query still has left when the ladder is reached.")
    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t")
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
