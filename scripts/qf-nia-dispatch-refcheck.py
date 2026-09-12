#!/usr/bin/env python3
"""Cross-check our verdicts against three independent authorities.

  1. the benchmark's own `(set-info :status …)`, read from the file text
  2. z3        -- `z3 -T:<SECONDS>`
  3. cvc5      -- `cvc5 --tlimit <MILLISECONDS>`   (units differ; that is the point)

Input TSV must have `file` and `verdict` columns.  Exit status depends on the
finding: non-zero if any disagreement is found, so this cannot pass vacuously.
A `--flip` control inverts every one of our verdicts and must produce
disagreements; a checker that reports 0 under `--flip` is broken.
"""
import argparse
import concurrent.futures as cf
import csv
import re
import subprocess
import sys

CVC5 = "/nas3/data/axeyum/harness/bin/cvc5"
STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")


def declared_status(path):
    try:
        with open(path, errors="replace") as fh:
            m = STATUS_RE.search(fh.read())
    except OSError:
        return "unreadable"
    return m.group(1) if m else "none"


def run_ref(cmd, wall):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=wall)
    except subprocess.TimeoutExpired:
        return "timeout"
    for line in (p.stdout + p.stderr).splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            return s
    return "none"


def check(path, ours, secs):
    z3v = run_ref(["z3", f"-T:{secs}", path], secs + 30)
    cvc = run_ref([CVC5, "--tlimit", str(secs * 1000), path], secs + 30)
    dec = declared_status(path)
    bad = []
    for name, other in (("status", dec), ("z3", z3v), ("cvc5", cvc)):
        if ours in ("sat", "unsat") and other in ("sat", "unsat") and ours != other:
            bad.append(name)
    authorities = sum(1 for o in (dec, z3v, cvc) if o in ("sat", "unsat"))
    return {"file": path, "ours": ours, "status": dec, "z3": z3v, "cvc5": cvc,
            "disagree": ",".join(bad) or "-", "authorities": authorities}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tsv")
    ap.add_argument("--out", required=True)
    ap.add_argument("--secs", type=int, default=60)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--verdict-col", default="verdict")
    ap.add_argument("--flip", action="store_true",
                    help="control: invert our verdicts; MUST produce disagreements")
    args = ap.parse_args()

    rows = [r for r in csv.DictReader(open(args.tsv), delimiter="\t")
            if r[args.verdict_col] in ("sat", "unsat")]
    if not rows:
        print("NOTHING TO CHECK: no decided rows in", args.tsv)
        return 1
    flip = {"sat": "unsat", "unsat": "sat"}
    print(f"checking {len(rows)} decided verdicts, {args.secs}s per reference"
          + (" [FLIP CONTROL]" if args.flip else ""))
    out = []
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(check, r["file"],
                          flip[r[args.verdict_col]] if args.flip else r[args.verdict_col],
                          args.secs) for r in rows]
        for f in cf.as_completed(futs):
            out.append(f.result())
    out.sort(key=lambda r: r["file"])
    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out[0].keys()), delimiter="\t")
        w.writeheader()
        w.writerows(out)
    dis = [r for r in out if r["disagree"] != "-"]
    noauth = [r for r in out if r["authorities"] == 0]
    print(f"wrote {args.out}: {len(out)} verdicts, {len(dis)} DISAGREEMENTS, "
          f"{len(noauth)} with no authority")
    for r in dis:
        print("  DISAGREE", r["disagree"], r["ours"], r["status"], r["z3"], r["cvc5"], r["file"])
    if args.flip:
        # control: the checker must be able to fail
        print("FLIP CONTROL:", len(dis), "disagreements")
        return 0 if dis else 1
    return 1 if (dis or noauth) else 0


if __name__ == "__main__":
    sys.exit(main())
