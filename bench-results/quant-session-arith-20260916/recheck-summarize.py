#!/usr/bin/env python3
"""QUANT-SESSION-ARITH (ADR-2130) -- classify each re-checked mover as
STABLE-GAIN, STABLE-LOSS or UNSTABLE.

    recheck-summarize.py <recheck-dir>

THE VERDICT COMES FROM `scripts/route_trace_reader.py`, NOT FROM A GREP, and
this script exists because the first version of the re-check did use a grep: a
`sed` over the trail JSON reported `none` for every `unknown` arm and for one
core that the paired probe had seen decide. A verdict extractor that cannot tell
"undecided" from "I could not parse this" turns an ambient result and a real one
into the same row.

A mover is STABLE only when EVERY pass agrees. ADR-2124's own re-check turned 2
raw gains into 1 stable and 1 ambient, and 6 raw losses into 5 stable and 1
ambient, so the raw column would have misled in both directions.

Exit 1 if any core FLIPS `sat` <-> `unsat` across the two arms.
"""

import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(REPO / "scripts"))

import route_trace_reader as rtr  # noqa: E402

DECIDED = ("sat", "unsat")


def verdict(path):
    try:
        trail = rtr.read_file(path)
    except rtr.NoTrailLine:
        return "no-trail"
    except rtr.RouteTraceError:
        return "trail-error"
    return trail.verdict or "unknown"


def main(argv):
    if len(argv) != 2:
        print(__doc__)
        return 2
    root = Path(argv[1])
    runs = defaultdict(dict)
    for out in sorted(root.glob("*.out")):
        # <core>.<arm>.<pass>.out
        stem = out.name[: -len(".out")]
        rest, passno = stem.rsplit(".", 1)
        core, arm = rest.rsplit(".", 1)
        runs[core].setdefault(arm, {})[int(passno)] = verdict(out)

    print("== ADR-2130: the movers, re-checked ==")
    print()
    flips = 0
    verdicts_seen = set()
    for core in sorted(runs):
        off = runs[core].get("off", {})
        on = runs[core].get("on", {})
        offs = [off[k] for k in sorted(off)]
        ons = [on[k] for k in sorted(on)]
        verdicts_seen.update(offs)
        verdicts_seen.update(ons)
        off_all = len(set(offs)) == 1
        on_all = len(set(ons)) == 1
        if off_all and on_all:
            o, n = offs[0], ons[0]
            if o in DECIDED and n in DECIDED and o != n:
                label = "FLIP"
                flips += 1
            elif o not in DECIDED and n in DECIDED:
                label = "STABLE-GAIN"
            elif o in DECIDED and n not in DECIDED:
                label = "STABLE-LOSS"
            else:
                label = "STABLE-SAME"
        else:
            label = "UNSTABLE"
        print(f"{label:12s}  off={','.join(offs)}  on={','.join(ons)}")
        print(f"              {core}")
    print()
    if verdicts_seen <= {"no-trail", "trail-error"}:
        print(
            "EXIT 2: every run failed to parse. This measured the extractor, not\n"
            "        the solver -- an unparseable arm is not an undecided one."
        )
        return 2
    if flips:
        print(f"EXIT 1: {flips} FLIP(s) -- a soundness defect.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
