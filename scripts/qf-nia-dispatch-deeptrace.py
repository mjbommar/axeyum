#!/usr/bin/env python3
"""Second pass: keep the WHOLE `--trace` stdout per file, so a later question
can be answered from the recorded run instead of a re-run under different load.

Writes one `<sha1-of-path>.trace` per file into `--out-dir`, plus an index TSV.
`AXEYUM_NIA_DEBUG=1` is set so the linearizer's products/mccormick/splits and
per-round outcomes are on stderr and captured too.
"""
import argparse
import concurrent.futures as cf
import csv
import hashlib
import os
import subprocess
import sys
import time


def run(path, budget_ms, wall_s, binary, out_dir, env_extra):
    env = dict(os.environ)
    env.update(env_extra)
    t0 = time.time()
    p = subprocess.run(
        ["timeout", "-k", "5", str(wall_s), binary, path,
         "--timeout-ms", str(budget_ms), "--trace"],
        capture_output=True, text=True, env=env)
    wall = time.time() - t0
    key = hashlib.sha1(path.encode()).hexdigest()[:16]
    dest = os.path.join(out_dir, key + ".trace")
    with open(dest, "w") as fh:
        fh.write(f"# file: {path}\n# rc: {p.returncode}\n# wall_s: {wall:.1f}\n")
        fh.write("# ---- stdout ----\n")
        fh.write(p.stdout)
        fh.write("# ---- stderr ----\n")
        fh.write(p.stderr)
    verdict = "none"
    for line in p.stdout.splitlines():
        if line.strip() in ("sat", "unsat", "unknown"):
            verdict = line.strip()
    return {"file": path, "key": key, "verdict": verdict,
            "rc": p.returncode, "wall_s": f"{wall:.1f}"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--index", required=True)
    ap.add_argument("--budget-ms", type=int, default=24000)
    ap.add_argument("--wall-s", type=int, default=180)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--binary", required=True)
    ap.add_argument("--env", default="AXEYUM_NIA_DEBUG=1")
    args = ap.parse_args()
    env_extra = dict(kv.split("=", 1) for kv in args.env.split(",") if kv)
    os.makedirs(args.out_dir, exist_ok=True)
    files = [l.strip() for l in open(args.list) if l.strip()]
    print(f"{len(files)} files, workers={args.workers}, env={env_extra}", flush=True)
    rows, done = [], 0
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(run, f, args.budget_ms, args.wall_s, args.binary,
                          args.out_dir, env_extra) for f in files]
        for fu in cf.as_completed(futs):
            rows.append(fu.result())
            done += 1
            if done % 10 == 0:
                print(f"  {done}/{len(files)}", flush=True)
    rows.sort(key=lambda r: r["file"])
    with open(args.index, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t")
        w.writeheader()
        w.writerows(rows)
    print("wrote", args.index, len(rows), "rows;", args.out_dir)
    return 0


if __name__ == "__main__":
    sys.exit(main())
