#!/usr/bin/env python3
"""A/B the warm offline QF_LIA decider over the loss population, one binary.

Method, stated because the population makes the obvious metric meaningless:

* The population is budget-bound. Every file here is one axeyum's front door
  already fails to decide, so in BOTH arms nearly every run spends its whole
  timeout. Wall time is therefore pinned to the budget and a wall-time ratio of
  1.00 would say nothing at all.
* So the primary score is `theory_offline_checks` -- how many offline
  conjunctive decisions the lazy loop got through inside the same budget --
  recorded on both arms by the same counter, plus any verdict that changes from
  `unknown` to a decision.
* Arms ALTERNATE per repetition, so machine drift is shared between them rather
  than accumulating on whichever ran second.
* A verdict that DISAGREES between arms on a decided file is a soundness alarm
  and is reported as such, never averaged into a timing number.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time

WARM_LINE = re.compile(r"^; lia-warm (.*)$", re.M)
VERDICTS = {"sat", "unsat", "unknown"}


def parse_counters(text: str) -> dict[str, str]:
    m = WARM_LINE.search(text)
    if not m:
        return {}
    out = {}
    for field in m.group(1).split():
        if "=" in field:
            k, v = field.split("=", 1)
            out[k] = v
    return out


def run_one(binary: str, path: str, budget_ms: int, arm: str) -> dict:
    env = dict(os.environ)
    if arm == "off":
        env["AXEYUM_LIA_WARM"] = "off"
    elif arm == "filter":
        env["AXEYUM_LIA_WARM"] = "filter"
    else:
        env.pop("AXEYUM_LIA_WARM", None)
    started = time.monotonic()
    try:
        proc = subprocess.run(
            [binary, path, "--timeout-ms", str(budget_ms), "--trace"],
            env=env,
            capture_output=True,
            text=True,
            timeout=budget_ms / 1000.0 + 30,
        )
        out = proc.stdout
    except subprocess.TimeoutExpired:
        return {"verdict": "harness-timeout", "wall_ms": None, "counters": {}}
    wall_ms = int((time.monotonic() - started) * 1000)
    verdict = "no-verdict"
    for line in reversed(out.strip().splitlines()):
        if line.strip() in VERDICTS:
            verdict = line.strip()
            break
    return {"verdict": verdict, "wall_ms": wall_ms, "counters": parse_counters(out)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--files", required=True, help="file with one path per line")
    ap.add_argument("--budget-ms", type=int, default=24000)
    ap.add_argument("--reps", type=int, default=2)
    ap.add_argument("--arms", default="off,warm")
    ap.add_argument("--out", required=True)
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    arms = args.arms.split(",")
    files = [l.strip() for l in open(args.files) if l.strip()]
    if args.limit:
        files = files[: args.limit]

    rows = []
    for index, path in enumerate(files):
        for rep in range(args.reps):
            # Alternate the arm ORDER per repetition, so a machine that drifts
            # over the run does not hand the whole drift to one arm.
            order = arms if rep % 2 == 0 else list(reversed(arms))
            for arm in order:
                r = run_one(args.binary, path, args.budget_ms, arm)
                r.update({"file": path, "arm": arm, "rep": rep})
                rows.append(r)
                print(
                    f"[{index+1}/{len(files)}] rep{rep} {arm:6s} "
                    f"{r['verdict']:8s} {r['wall_ms']}ms "
                    f"offline={r['counters'].get('theory_offline_checks','-')} "
                    f"{os.path.basename(path)}",
                    flush=True,
                )
    with open(args.out, "w") as fh:
        json.dump(rows, fh, indent=1)
    print(f"wrote {args.out} ({len(rows)} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
