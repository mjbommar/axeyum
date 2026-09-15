#!/usr/bin/env python3
"""Re-census the QF_NIA winnable population on current main.

One file per process, `--timeout-ms <budget>` with a hard wall at 7.5x the
budget (a previous census used `timeout 32` around a 24 s budget and killed 17
processes under load, manufacturing false "no reason" rows).

Records, deliberately uncollapsed:
  verdict, give-up kind + detail, decided_by / bound_by / last / attempts,
  bound_ms / total_ms, the phase breadcrumb stack, wall, rc.

`attempts` is recorded so a reader can confirm the dispatch ran to the END of
the ladder rather than an early rung refusing and that refusal becoming the
file's answer.
"""
import argparse
import concurrent.futures as cf
import csv
import os
import re
import subprocess
import sys
import time

import subprocess as _sp
ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"],
               capture_output=True, text=True,
               cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
CLI = os.path.join(ROOT, "target/release/examples/smtcomp_cli")


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import route_trace_reader as rtr  # noqa: E402


def _trail_line(out: str) -> str | None:
    """The LAST route-trail line in a `--trace` run's output, complete or partial.

    Both spellings, because completeness is not this function's business --
    the reader reports it as a field.
    """
    found = None
    for line in out.splitlines():
        if line.startswith(rtr.TRAIL_PREFIX) or line.startswith(
            rtr.PARTIAL_TRAIL_PREFIX
        ):
            found = line
    return found


def run_one(path, budget_ms, wall_s, binary, env_extra=None):
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    t0 = time.time()
    try:
        p = subprocess.run(
            ["timeout", "-k", "5", str(wall_s), binary, path,
             "--timeout-ms", str(budget_ms), "--trace"],
            capture_output=True, text=True, env=env,
        )
        out, rc = p.stdout + p.stderr, p.returncode
    except Exception as exc:  # noqa: BLE001
        out, rc = f"HARNESS-EXC {exc}", -999
    wall = time.time() - t0

    verdict = "none"
    for line in out.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            verdict = s
    m = re.search(r"^; give-up kind=(\S+) detail=(.*)$", out, re.M)
    kind, detail = (m.group(1), m.group(2).strip()) if m else ("none", "none")
    # Route attribution off the shared reader (ADR-2101), never off the prose.
    # The regex this replaces was anchored at `^; route `, so a file the
    # watchdog killed -- which prints `; partial route ` -- fell into the
    # `else` and was censused as `bound_by=none bound_ms=-1`. That is
    # ADR-2075's defect exactly, in a census of the division it was found in.
    partial = "no"
    try:
        trail = rtr.parse_trail_line(_trail_line(out), path)
    except (rtr.RouteTraceError, TypeError):
        decided = bound = last = "none"
        bound_ms = total_ms = attempts = "-1"
    else:
        decided = trail.decided_by or "none"
        bound = trail.bound_by or "none"
        last = trail.last or "none"
        bound_ns = max((a.elapsed_ns or 0 for a in trail.attempts), default=0)
        bound_ms = str(bound_ns // 1_000_000)
        total_ms = str(trail.total_elapsed_ms if trail.total_elapsed_ms is not None else -1)
        attempts = str(trail.attempt_count)
        partial = "yes" if trail.partial else "no"
    m = re.search(r"^;\s*(?:partial\s+)?phase (stack=.*)$", out, re.M)
    phase = m.group(1).strip() if m else "none"
    return {
        "file": path, "verdict": verdict, "rc": rc, "wall_s": f"{wall:.1f}",
        "kind": kind, "detail": detail, "decided_by": decided,
        "bound_by": bound, "last": last, "bound_ms": bound_ms,
        "total_ms": total_ms, "attempts": attempts, "partial": partial,
        "phase": phase,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--budget-ms", type=int, default=24000)
    ap.add_argument("--wall-s", type=int, default=180)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--binary", default=CLI)
    args = ap.parse_args()

    files = [l.strip() for l in open(args.list) if l.strip()]
    print(f"{len(files)} files, {args.workers} workers, budget {args.budget_ms} ms, "
          f"wall {args.wall_s} s, binary {args.binary}", flush=True)
    rows = []
    done = 0
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(run_one, f, args.budget_ms, args.wall_s, args.binary): f
                for f in files}
        for fut in cf.as_completed(futs):
            rows.append(fut.result())
            done += 1
            if done % 10 == 0:
                print(f"  {done}/{len(files)}", flush=True)
    rows.sort(key=lambda r: r["file"])
    cols = ["file", "verdict", "rc", "wall_s", "kind", "detail", "decided_by",
            "bound_by", "last", "bound_ms", "total_ms", "attempts", "partial",
            "phase"]
    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t")
        w.writeheader()
        w.writerows(rows)
    print("wrote", args.out, len(rows), "rows")
    killed = [r for r in rows if r["rc"] not in (0,)]
    print("non-zero rc:", len(killed))
    noreason = [r for r in rows if r["kind"] == "none" and r["verdict"] == "unknown"]
    print("unknown with NO stated reason:", len(noreason))
    return 0


if __name__ == "__main__":
    sys.exit(main())
