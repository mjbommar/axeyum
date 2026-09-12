#!/usr/bin/env python3
"""Interleaved per-file A/B over a file list.

Both arms of a file run back to back inside one worker, so the pair shares
ambient load, and the arm ORDER alternates by file index so a load trend cannot
systematically favour one arm.  One binary, two environments.
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
_ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"], capture_output=True,
                text=True,
                cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
CLI_DEFAULT = os.path.join(_ROOT, "target/release/examples/smtcomp_cli")


def one(binary, path, budget_ms, wall_s, env_extra, pin):
    env = dict(os.environ)
    env.update(env_extra)
    cmd = ["timeout", "-k", "5", str(wall_s)]
    if pin:
        cmd += ["taskset", "-c", pin]
    cmd += [binary, path, "--timeout-ms", str(budget_ms), "--trace"]
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
    wall = time.time() - t0
    out = p.stdout + p.stderr
    verdict = "none"
    for line in out.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            verdict = s
    m = re.search(r"^; give-up kind=(\S+) detail=(.*)$", out, re.M)
    giveup = f"kind={m.group(1)} detail={m.group(2).strip()}" if m else "none"
    return verdict, wall, giveup, p.returncode


def pair(idx, path, binary, budget_ms, wall_s, env_a, env_b, pin):
    order = idx % 2 == 0
    if order:
        a = one(binary, path, budget_ms, wall_s, env_a, pin)
        b = one(binary, path, budget_ms, wall_s, env_b, pin)
    else:
        b = one(binary, path, budget_ms, wall_s, env_b, pin)
        a = one(binary, path, budget_ms, wall_s, env_a, pin)
    return {"file": path, "order": "ab" if order else "ba",
            "a_verdict": a[0], "a_s": f"{a[1]:.1f}", "a_rc": a[3], "a_giveup": a[2],
            "b_verdict": b[0], "b_s": f"{b[1]:.1f}", "b_rc": b[3], "b_giveup": b[2]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--budget-ms", type=int, default=24000)
    ap.add_argument("--wall-s", type=int, default=180)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--binary", default=CLI_DEFAULT)
    ap.add_argument("--env-a", default="", help="k=v,k=v for arm A (baseline)")
    ap.add_argument("--env-b", default="", help="k=v,k=v for arm B (treatment)")
    ap.add_argument("--pin", default="", help="taskset core list, e.g. 0-7")
    args = ap.parse_args()

    def parse(s):
        return dict(kv.split("=", 1) for kv in s.split(",") if kv)

    env_a, env_b = parse(args.env_a), parse(args.env_b)
    files = [l.strip() for l in open(args.list) if l.strip()]
    print(f"{len(files)} files x 2 arms, workers={args.workers}, "
          f"budget={args.budget_ms}ms, pin={args.pin or 'none'}")
    print("  arm A env:", env_a or "{}")
    print("  arm B env:", env_b or "{}")
    rows, done = [], 0
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(pair, i, f, args.binary, args.budget_ms, args.wall_s,
                          env_a, env_b, args.pin) for i, f in enumerate(files)]
        for fu in cf.as_completed(futs):
            rows.append(fu.result())
            done += 1
            if done % 10 == 0:
                print(f"  {done}/{len(files)}", flush=True)
    rows.sort(key=lambda r: r["file"])
    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t")
        w.writeheader()
        w.writerows(rows)

    DEC = {"sat", "unsat"}
    a_dec = [r for r in rows if r["a_verdict"] in DEC]
    b_dec = [r for r in rows if r["b_verdict"] in DEC]
    gains = [r for r in rows if r["b_verdict"] in DEC and r["a_verdict"] not in DEC]
    losses = [r for r in rows if r["a_verdict"] in DEC and r["b_verdict"] not in DEC]
    flips = [r for r in rows if r["a_verdict"] in DEC and r["b_verdict"] in DEC
             and r["a_verdict"] != r["b_verdict"]]
    both = [r for r in rows if r["a_verdict"] in DEC and r["b_verdict"] in DEC]
    wa = sum(float(r["a_s"]) for r in rows)
    wb = sum(float(r["b_s"]) for r in rows)
    print(f"\nA decided {len(a_dec)}  B decided {len(b_dec)}")
    print(f"gains(B only) {len(gains)}  losses(A only) {len(losses)}  "
          f"VERDICT FLIPS {len(flips)}")
    print(f"wall A {wa:.0f}s  B {wb:.0f}s  delta {100*(wb-wa)/wa:+.1f}%")
    if both:
        ba = sum(float(r["a_s"]) for r in both)
        bb = sum(float(r["b_s"]) for r in both)
        print(f"both-decided ({len(both)}) wall ratio B/A {bb/ba:.3f}")
    for r in gains:
        print("  GAIN ", r["b_verdict"], r["b_s"], r["file"])
    for r in losses:
        print("  LOSS ", r["a_verdict"], r["a_s"], r["file"])
    for r in flips:
        print("  FLIP ", r["a_verdict"], "->", r["b_verdict"], r["file"])
    print("wrote", args.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
