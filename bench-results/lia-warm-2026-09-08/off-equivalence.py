#!/usr/bin/env python3
"""Is `AXEYUM_LIA_WARM=off` the pre-existing path? Two binaries, same files.

The claim is a code-level one — `LiaWarmPolicy::OFF` builds no warm decider and
leaves the filter on, and `verify-extraction.py` shows the offline decider is
token-identical to main's. This is the binary form of the same question, which
is the one that would catch a difference the reading missed.

Verdicts must match exactly. The counters are NOT required to match: main's
binary has no warm group at all, and the lane's `off` arm reports it
`not-reached`, which is the correct different answer rather than a discrepancy.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

VERDICTS = {"sat", "unsat", "unknown"}
LIA = re.compile(r"^; (partial )?lia (.*)$", re.M)
LIA_UNAVAIL = re.compile(r"^; (partial )?lia unavailable:", re.M)


def counters(text):
    if LIA_UNAVAIL.search(text):
        return {}
    m = LIA.search(text)
    if not m:
        return {}
    return dict(f.split("=", 1) for f in m.group(2).split() if "=" in f)


def run(binary, path, budget_ms, env_extra):
    env = dict(os.environ)
    env.pop("AXEYUM_LIA_WARM", None)
    env.update(env_extra)
    try:
        out = subprocess.run(
            [binary, path, "--timeout-ms", str(budget_ms), "--trace"],
            env=env,
            capture_output=True,
            text=True,
            timeout=budget_ms / 1000.0 + 30,
        ).stdout
    except subprocess.TimeoutExpired:
        return "harness-timeout", {}
    verdict = "no-verdict"
    for line in reversed(out.strip().splitlines()):
        if line.strip() in VERDICTS:
            verdict = line.strip()
            break
    return verdict, counters(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--main-binary", required=True)
    ap.add_argument("--lane-binary", required=True)
    ap.add_argument("--files", required=True)
    ap.add_argument("--budget-ms", type=int, default=8000)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    files = [l.strip() for l in open(args.files) if l.strip()]
    if args.limit:
        files = files[: args.limit]

    rows, mismatches, decided = [], [], 0
    for i, path in enumerate(files):
        mv, mc = run(args.main_binary, path, args.budget_ms, {})
        lv, lc = run(args.lane_binary, path, args.budget_ms, {"AXEYUM_LIA_WARM": "off"})
        rows.append(
            {
                "file": path,
                "main_verdict": mv,
                "lane_off_verdict": lv,
                "main_offline_calls": mc.get("offline_calls"),
                "lane_offline_calls": lc.get("offline_calls"),
                "lane_warm_checks": lc.get("warm_checks"),
                "lane_warm_group": lc.get("warm"),
            }
        )
        if mv in ("sat", "unsat") or lv in ("sat", "unsat"):
            decided += 1
        if mv != lv:
            mismatches.append((path, mv, lv))
        print(
            f"[{i + 1}/{len(files)}] main={mv:8s} lane_off={lv:8s} "
            f"warm_checks={lc.get('warm_checks', '-')} {os.path.basename(path)}",
            flush=True,
        )

    json.dump(rows, open(args.out, "w"), indent=1)
    print(f"\nfiles: {len(files)}, of which decided by at least one arm: {decided}")
    print(f"verdict mismatches: {len(mismatches)}")
    for path, mv, lv in mismatches:
        print(f"  !! {os.path.basename(path)}: main={mv} lane_off={lv}")
    # A run where nothing was decided proves nothing about verdict equality.
    if decided == 0:
        print("VACUOUS: no file was decided by either arm")
        return 2
    # The lane's OFF arm must never enter the warm decider.
    entered = [r for r in rows if (r["lane_warm_checks"] or "0") != "0"]
    print(f"lane OFF runs that entered the warm decider: {len(entered)} (must be 0)")
    return 0 if not mismatches and not entered else 1


if __name__ == "__main__":
    sys.exit(main())
