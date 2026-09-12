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
    m = re.search(
        r"^; route decided_by=(\S+) bound_by=(\S+) last=(\S+) "
        r"bound_ms=(\d+) total_ms=(\d+) attempts=(\d+)", out, re.M)
    if m:
        decided, bound, last, bound_ms, total_ms, attempts = m.groups()
    else:
        decided = bound = last = "none"
        bound_ms = total_ms = attempts = "-1"
    m = re.search(r"^;\s*(?:partial\s+)?phase (stack=.*)$", out, re.M)
    phase = m.group(1).strip() if m else "none"
    return {
        "file": path, "verdict": verdict, "rc": rc, "wall_s": f"{wall:.1f}",
        "kind": kind, "detail": detail, "decided_by": decided,
        "bound_by": bound, "last": last, "bound_ms": bound_ms,
        "total_ms": total_ms, "attempts": attempts, "phase": phase,
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
            "bound_by", "last", "bound_ms", "total_ms", "attempts", "phase"]
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
