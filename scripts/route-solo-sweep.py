#!/usr/bin/env python3
"""Run every route ALONE on every file, and report the virtual best.

This is the measurement the 2026-09-07 route-attribution sweep wanted and could
not take: *"A strict virtual best runs each route alone on each file.
`SolverConfig` has no route-selection knob, so that is not measurable and is not
claimed."*  The dispatcher still has no such knob; `examples/route_solo` gets
around it by calling the route entry points directly, one route per process.

Two things come out, and the second one is not optional:

1. **The virtual best.**  Per file: which routes decide it alone inside the
   budget, and the cheapest one's cost.  A file the ladder loses that some
   single route decides in well under the budget is a portfolio prize; a file no
   route decides alone is not, however the ladder spends its clock.

2. **A cross-route soundness gate.**  Running N routes over one file yields N
   independent verdicts about the same query, and **this script exits 2 if any
   two of them disagree on `sat` vs `unsat`.**  Nothing else in this repository
   compares route against route at corpus scale; the differential fuzzes compare
   us against z3 on generated input, and the corpus sweep compares one shipped
   verdict against a recorded one.  The exit status depends on the finding, so a
   disagreement fails rather than being printed into a table nobody reads.

   A route reporting `unknown`, `error` or `panic` is not a disagreement --
   those are declines, and a decline is the normal case for a route outside its
   fragment.

## What a negative here does and does not mean

`route_solo` decides the FLAT ASSERTION VIEW with no preprocessing and no
admission test, and that view disagrees with the shipped front door on 134 of
397 benchmarks.  So a route that decides a file here would decide it in a
portfolio arm, but a route that declines here may still decide under the
dispatcher, which hands it a canonicalized, coercion-normalized query.  Every
count this prints is a LOWER bound.
"""

from __future__ import annotations

import argparse
import collections
import os
import pathlib
import subprocess
import sys
import time

DECIDED = ("sat", "unsat")


def load_expected(paths) -> dict:
    """`file -> reference verdict`, from the committed `<DIV>.census.tsv` files.

    Cross-route agreement is NOT a correctness check: five routes can agree with
    each other and all be wrong, and a portfolio built on that agreement would
    ship the error faster.  The census carries `declared` (the benchmark's own
    `:status`) and `reference_verdict`, and this compares against them.
    """
    expected = {}
    for p in paths:
        with open(p) as fh:
            header = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                row = dict(zip(header, line.rstrip("\n").split("\t")))
                want = row.get("reference_verdict") or row.get("declared") or ""
                if row.get("file") and want in DECIDED:
                    expected[row["file"]] = want
    return expected


def route_names(binary: str) -> list[str]:
    out = subprocess.run([binary, "--list"], capture_output=True, text=True, check=True)
    names = [l.strip() for l in out.stdout.splitlines() if l.strip()]
    if not names:
        raise SystemExit("route_solo --list returned nothing: refusing to sweep zero routes")
    return names


def run_route(binary, path, route, timeout_ms, cores, mem_mb, slack_s):
    """One route, one file, one process.  Returns (verdict, wall_ms, detail)."""
    cmd = []
    if cores:
        cmd += ["taskset", "-c", cores]
    cmd += [binary, path, "--route", route, "--timeout-ms", str(timeout_ms)]
    shell = 'ulimit -v %d; exec "$@"' % (mem_mb * 1024)
    try:
        proc = subprocess.run(
            ["/bin/sh", "-c", shell, "sh"] + cmd,
            capture_output=True,
            text=True,
            timeout=timeout_ms / 1000.0 + slack_s,
        )
        line = proc.stdout.strip().splitlines()
        if not line:
            # No line at all: the process died before printing.  That is a
            # memory or signal event, never "this route found nothing".
            return ("aborted", timeout_ms, f"exit={proc.returncode}")
        parts = (line[-1].split("\t") + ["", "", ""])[:4]
        return (parts[1], int(parts[2] or 0), parts[3])
    except subprocess.TimeoutExpired:
        return ("killed", timeout_ms, "outer wall timeout")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--binary", required=True, help="release route_solo")
    ap.add_argument("--files", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--division", default="?")
    ap.add_argument("--budget-ms", type=int, default=24_000)
    ap.add_argument("--memory-limit-mb", type=int, default=8192)
    ap.add_argument("--cores", default=None)
    ap.add_argument("--slack-s", type=int, default=20)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument(
        "--expected",
        nargs="*",
        default=[],
        help="committed <DIV>.census.tsv files; a route whose verdict "
        "contradicts the reference is a WRONG VERDICT and exits 3",
    )
    ap.add_argument(
        "--only",
        default=None,
        help="comma-separated route subset (for a second pass adding routes to "
        "an existing sweep; merge the TSVs, do not re-run what you have)",
    )
    args = ap.parse_args()

    routes = route_names(args.binary)
    if args.only:
        wanted = [r.strip() for r in args.only.split(",") if r.strip()]
        unknown = [r for r in wanted if r not in routes]
        if unknown:
            # An unknown name must fail loudly: a filter that silently matched
            # nothing would report a clean sweep of zero routes.
            raise SystemExit(f"--only names routes route_solo does not have: {unknown}")
        routes = wanted
    files = [l.strip() for l in pathlib.Path(args.files).read_text().splitlines() if l.strip()]
    if args.limit:
        files = files[: args.limit]

    expected = load_expected(args.expected)
    rows = []
    disagreements = []
    wrong = []
    for i, path in enumerate(files, 1):
        if not os.path.exists(path):
            continue
        started = time.monotonic()
        verdicts = {}
        for route in routes:
            verdict, wall_ms, detail = run_route(
                args.binary, path, route, args.budget_ms, args.cores,
                args.memory_limit_mb, args.slack_s,
            )
            verdicts[route] = (verdict, wall_ms, detail)
            rows.append({
                "division": args.division, "file": path, "route": route,
                "verdict": verdict, "wall_ms": wall_ms, "detail": detail,
            })
        deciders = {r: v for r, (v, _, _) in verdicts.items() if v in DECIDED}
        if len(set(deciders.values())) > 1:
            disagreements.append((path, deciders))
        want = expected.get(path)
        if want:
            for route, verdict in deciders.items():
                if verdict != want:
                    wrong.append((path, route, verdict, want))
        best = sorted(
            ((verdicts[r][1], r) for r in deciders),
        )
        summary = (f"{best[0][1]}@{best[0][0]}ms" if best else "no-route")
        print(f"[{i}/{len(files)}] {args.division} deciders={len(deciders)} "
              f"best={summary} ({time.monotonic() - started:.0f}s)  "
              f"{path.split('/')[-1]}", file=sys.stderr, flush=True)

    cols = ["division", "file", "route", "verdict", "wall_ms", "detail"]
    with open(args.out, "w") as fh:
        fh.write("\t".join(cols) + "\n")
        for r in rows:
            fh.write("\t".join(str(r[c]).replace("\t", " ") for c in cols) + "\n")
        fh.write(f"# division={args.division} files={len(files)} routes={len(routes)} "
                 f"budget_ms={args.budget_ms} cores={args.cores}\n")

    per_file = collections.defaultdict(dict)
    for r in rows:
        per_file[r["file"]][r["route"]] = (r["verdict"], r["wall_ms"])
    decided_by_some = 0
    fast = collections.Counter()
    for path, rs in per_file.items():
        winners = [(w, route) for route, (v, w) in rs.items() if v in DECIDED]
        if winners:
            decided_by_some += 1
            fast[min(winners)[1]] += 1
    print(f"\n{args.division}: {len(per_file)} files, "
          f"{decided_by_some} decided by at least one route running alone")
    for route, n in fast.most_common():
        print(f"  fastest-alone {route:<22} {n}")

    if wrong:
        print("\nWRONG VERDICT against the reference -- soundness alarm:", file=sys.stderr)
        for path, route, got, want in wrong:
            print(f"  {route:<22} said {got}, reference says {want}   {path}", file=sys.stderr)
        return 3
    if disagreements:
        print("\nCROSS-ROUTE VERDICT DISAGREEMENT -- soundness alarm:", file=sys.stderr)
        for path, deciders in disagreements:
            print(f"  {path}", file=sys.stderr)
            for route, verdict in sorted(deciders.items()):
                print(f"    {route:<22} {verdict}", file=sys.stderr)
        return 2
    checked = sum(1 for p in per_file if p in expected)
    print(f"cross-route soundness: no two routes disagreed on any file; "
          f"{checked} of {len(per_file)} files also checked against the reference verdict")
    if expected and checked == 0:
        # An "all clear" from a check that examined nothing is worse than no
        # check: the census paths must match the sweep's paths exactly.
        print("reference check matched ZERO files -- it did not run", file=sys.stderr)
        return 4
    return 0


if __name__ == "__main__":
    sys.exit(main())
