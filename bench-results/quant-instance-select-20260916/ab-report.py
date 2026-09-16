#!/usr/bin/env python3
"""ADR-2133 A/B: the generation ladder OFF vs ON on the 53 UFLIA cores.

Interleaved per file -- same core file, same pinned physical core pair, OFF then
ON back to back -- so ambient load cancels in the difference instead of being
attributed to an arm.

The report's own non-vacuity check is the LAST line: if the two arms produce
byte-identical trace evidence on every core, the lever did not reach the code
on this population, and that is a finding about coverage, not about the lever.
"""

import collections
import os
import re
import sys

BASE = os.path.dirname(os.path.abspath(__file__))
AB = sys.argv[1] if len(sys.argv) > 1 else "/nas3/data/axeyum/lanes/quant-instance-select/ab0"

VERDICT = re.compile(r"^(sat|unsat|unknown)$", re.M)
DECIDED = re.compile(r"decided_by=(\S+)")
ELAPSED = re.compile(r"elapsed_ms=(\d+)")


def read(path):
    with open(path, errors="replace") as fh:
        text = fh.read()
    vs = VERDICT.findall(text)
    db = DECIDED.findall(text)
    el = ELAPSED.findall(text)
    return dict(
        verdict=vs[-1] if vs else "NONE",
        decided_by=db[-1] if db else "",
        ms=int(el[-1]) if el else None,
        text=text,
    )


def main():
    rows = []
    for shard in sorted(os.listdir(AB)):
        offdir = os.path.join(AB, shard, "off")
        if not os.path.isdir(offdir):
            continue
        for name in sorted(os.listdir(offdir)):
            on_path = os.path.join(AB, shard, "on", name)
            if not os.path.exists(on_path):
                continue
            rows.append((name, read(os.path.join(offdir, name)), read(on_path)))
    if not rows:
        print(f"no captures under {AB}", file=sys.stderr)
        return 2

    print(f"cores compared: {len(rows)}")
    off = collections.Counter(o["verdict"] for _, o, _ in rows)
    on = collections.Counter(n["verdict"] for _, _, n in rows)
    print(f"  OFF verdicts: {dict(off)}")
    print(f"  ON  verdicts: {dict(on)}")
    print(f"  decided (sat or unsat)  OFF {off['sat'] + off['unsat']}  ON {on['sat'] + on['unsat']}")

    gains, losses, flips = [], [], []
    for name, o, n in rows:
        ov, nv = o["verdict"], n["verdict"]
        if ov == nv:
            continue
        if ov == "unknown" and nv in ("sat", "unsat"):
            gains.append((name, nv, n["ms"]))
        elif nv == "unknown" and ov in ("sat", "unsat"):
            losses.append((name, ov, o["ms"]))
        else:
            flips.append((name, ov, nv))
    print(f"\n  GAINS  (unknown -> decided): {len(gains)}")
    for name, v, ms in gains:
        print(f"    {name[:66]:66s} -> {v} ({ms} ms)")
    print(f"  LOSSES (decided -> unknown): {len(losses)}")
    for name, v, ms in losses:
        print(f"    {name[:66]:66s} was {v} ({ms} ms)")
    print(f"  FLIPS  (sat <-> unsat): {len(flips)}  <- ANY nonzero here is a soundness stop")
    for name, ov, nv in flips:
        print(f"    {name[:66]:66s} {ov} -> {nv}")

    # Non-vacuity. If no capture differs in any byte, the lever never reached
    # the code and the zero above measures coverage, not the lever.
    differing = [name for name, o, n in rows if o["text"] != n["text"]]
    print(f"\n  cores whose two arms differ in ANY trace byte: {len(differing)} / {len(rows)}")
    if not differing:
        print(
            "  ** VACUOUS: the arms are byte-identical everywhere, so this A/B\n"
            "     says nothing about the lever -- it says the lever was not reached. **"
        )
    else:
        print(f"    e.g. {differing[0][:70]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
