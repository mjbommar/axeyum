#!/usr/bin/env python3
"""Summarize the ADR-2060 A/B against the rules pre-registered in
PREREGISTRATION.md, and make the EXIT STATUS depend on the finding.

Exit 0  = every registered rule held (verdict-neutral, exit-status-neutral, and
          the give-up channel DID move, so the arms are not the same binary).
Exit 3  = a rule was violated. The violation is printed per file.
Exit 4  = the run is VACUOUS (the give-up channel did not move, or a shard did
          not complete) and no conclusion may be drawn from it.

Every zero is printed with the denominator it is a zero out of, and every rate
below n = 100 carries a Wilson 95% interval.
"""

import math
import pathlib
import sys

COLS = [
    "file", "base", "base_rc", "base_ms", "base_giveup", "base_err",
    "arm", "arm_rc", "arm_ms", "arm_giveup", "arm_err", "first", "status",
]
DECIDED = {"sat", "unsat"}


def wilson(k, n, z=1.96):
    """Wilson 95% interval for k successes out of n. `None` when n == 0 --
    a rate over no observations is not a rate."""
    if n == 0:
        return None
    p = k / n
    d = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / d
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, centre - half), min(1.0, centre + half))


def fmt(k, n, label):
    iv = wilson(k, n)
    if iv is None:
        return f"{label}: {k}/{n} -- NOTHING COMPARABLE (denominator 0)"
    lo, hi = iv
    tail = f", Wilson 95% [{lo:.4f}, {hi:.4f}]" if n < 100 else ""
    return f"{label}: {k}/{n}{tail}"


def rc_class(rc):
    return {"0": "clean", "124": "wall-kill", "134": "abort"}.get(rc, f"exit-{rc}")


def main(paths, expected_rows):
    rows = []
    incomplete = []
    for p in paths:
        path = pathlib.Path(p)
        if not path.exists():
            incomplete.append(f"{p}: MISSING -- DID NOT RUN")
            continue
        lines = path.read_text().splitlines()
        if not lines or lines[0].split("\t") != COLS:
            incomplete.append(f"{p}: header mismatch -- DID NOT RUN")
            continue
        for line in lines[1:]:
            parts = line.split("\t")
            if len(parts) != len(COLS):
                incomplete.append(f"{p}: malformed row -- DID NOT RUN")
                continue
            rows.append(dict(zip(COLS, parts)))

    print(f"rows collected: {len(rows)} (expected {expected_rows})")
    for note in incomplete:
        print(f"  INCOMPLETE {note}")
    if incomplete or len(rows) != expected_rows:
        print("VERDICT: VACUOUS -- not every shard completed; no conclusion drawn")
        return 4

    # --- channel 3 first: are the two arms actually different binaries? ------
    moved_giveup = [r for r in rows if r["base_giveup"] != r["arm_giveup"]]
    print()
    print("CHANNEL 3 (give-up detail) -- MUST MOVE")
    print(f"  {fmt(len(moved_giveup), len(rows), 'rows whose give-up detail changed')}")
    if not moved_giveup:
        print("VERDICT: VACUOUS -- the detail channel did not move on ANY row, so the")
        print("         two arms cannot be shown to be different binaries.")
        return 4
    example = moved_giveup[0]
    print(f"  example: {pathlib.Path(example['file']).name}")
    print(f"    base: {example['base_giveup'][:200]}")
    print(f"    arm : {example['arm_giveup'][:200]}")

    # --- channel 1: verdicts -------------------------------------------------
    comparable = [r for r in rows if r["base"] != "none" or r["arm"] != "none"]
    both_parsed = [r for r in rows if r["base"] != "none" and r["arm"] != "none"]
    gains = [r for r in rows if r["arm"] in DECIDED and r["base"] not in DECIDED]
    losses = [r for r in rows if r["base"] in DECIDED and r["arm"] not in DECIDED]
    flips = [
        r for r in rows
        if r["base"] in DECIDED and r["arm"] in DECIDED and r["base"] != r["arm"]
    ]
    base_decided = [r for r in rows if r["base"] in DECIDED]
    arm_decided = [r for r in rows if r["arm"] in DECIDED]

    print()
    print("CHANNEL 1 (verdict) -- MUST NOT MOVE")
    print(f"  base decided {len(base_decided)}/{len(rows)}   "
          f"arm decided {len(arm_decided)}/{len(rows)}")
    print(f"  {fmt(len(gains), len(rows), 'GAINS (arm decided, base did not)')}")
    print(f"  {fmt(len(losses), len(rows), 'LOSSES (base decided, arm did not)')}")
    print(f"  {fmt(len(flips), len(both_parsed), 'FLIPS (sat<->unsat between arms)')}")
    print(f"  comparable denominator: both arms emitted a verdict line on "
          f"{len(both_parsed)}/{len(rows)}")

    # --- channel 2: exit status ---------------------------------------------
    rc_moves = [r for r in rows if rc_class(r["base_rc"]) != rc_class(r["arm_rc"])]
    both_clean = [r for r in rows if r["base_rc"] == "0" and r["arm_rc"] == "0"]
    print()
    print("CHANNEL 2 (exit status) -- MUST NOT MOVE")
    print(f"  {fmt(len(rc_moves), len(rows), 'rows whose exit CLASS changed')}")
    print(f"  both arms exited 0 on {len(both_clean)}/{len(rows)}")
    for r in rc_moves:
        print(f"    MOVED {pathlib.Path(r['file']).name}: "
              f"base {rc_class(r['base_rc'])} -> arm {rc_class(r['arm_rc'])}")

    # --- soundness -----------------------------------------------------------
    annotated = [r for r in rows if r["status"] in DECIDED]
    wrong = [
        (r, arm)
        for r in annotated
        for arm in ("base", "arm")
        if r[arm] in DECIDED and r[arm] != r["status"]
    ]
    print()
    print("SOUNDNESS")
    print(f"  {fmt(len(wrong), len(annotated), 'verdicts disagreeing with :status')}")
    print(f"  (denominator: rows carrying a :status annotation)")
    for r, arm in wrong:
        print(f"    WRONG {pathlib.Path(r['file']).name}: {arm} said {r[arm]}, "
              f":status is {r['status']}")

    # --- the finding ---------------------------------------------------------
    violations = len(gains) + len(losses) + len(flips) + len(rc_moves) + len(wrong)
    print()
    if violations:
        print(f"VERDICT: NOT NEUTRAL -- {violations} registered violation(s) above.")
        for r in gains:
            print(f"  GAIN  {r['file']}  base={r['base']} arm={r['arm']}")
        for r in losses:
            print(f"  LOSS  {r['file']}  base={r['base']} arm={r['arm']}")
        return 3
    print("VERDICT: VERDICT-NEUTRAL AND EXIT-STATUS-NEUTRAL, with the give-up")
    print(f"         detail channel moving on {len(moved_giveup)}/{len(rows)} rows,")
    print("         which is what proves the two arms are different binaries.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[2:], int(sys.argv[1])))
