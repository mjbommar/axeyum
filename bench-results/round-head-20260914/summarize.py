#!/usr/bin/env python3
"""Summarise lane ROUND-HEAD's census and reference sweeps.

Every ratio prints its DENOMINATOR on the same line (ADR-1957), every small-n
proportion gets a WILSON interval and never a normal one, and a zero count is
printed explicitly rather than omitted -- an omitted row and a zero row read the
same in a table and only one of them is a measurement.

Usage:
    summarize.py exits   <census/*.tsv> ...     # R2: the seven-way exit census
    summarize.py replay  <census/*.tsv> ...     # R3: the held-set replay
    summarize.py ref     <ref/*.tsv> ...        # the reference cost
    summarize.py noise   <noise/*.tsv> ...      # the same-arm noise floor
    summarize.py compare <census-glob> -- <ref-glob>   # ours vs the reference
"""

from __future__ import annotations

import csv
import math
import re
import statistics
import sys
from collections import Counter, defaultdict


def wilson(k: int, n: int) -> tuple[float, float]:
    """Wilson 95 % interval. Never the normal approximation: at k=0 the normal
    one is the degenerate [0, 0], which is how a lane publishes a confident
    zero it did not measure."""
    if n == 0:
        return (0.0, 0.0)
    z = 1.959963984540054
    p = k / n
    d = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / d
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, centre - half), min(1.0, centre + half))


def pct(k: int, n: int) -> str:
    if n == 0:
        return f"{k}/0 (no denominator)"
    lo, hi = wilson(k, n)
    return f"{k}/{n} = {100 * k / n:.1f} % [{100 * lo:.1f} %, {100 * hi:.1f} %]"


def read(paths: list[str]) -> list[dict]:
    rows: list[dict] = []
    for path in paths:
        with open(path, newline="") as handle:
            rows.extend(csv.DictReader(handle, delimiter="\t"))
    return rows


EXIT_RE = re.compile(r"kind=(\S+) exit=(\S+) rounds=(\d+) ground=(\d+)")
REPLAY_RE = re.compile(
    r"held-set-replay exit=(\S+) ground=(\d+) rounds=(\d+) verdict=(\S+) ms=(\d+)"
    r" budget_ms=(\d+)(?: why=(\S+))?"
)
SKIP_RE = re.compile(r"held-set-replay-skipped exit=(\S+) ground=(\d+)")


def parse_exits(cell: str) -> list[tuple[str, str, int, int]]:
    if not cell or cell == "none":
        return []
    return [
        (m.group(1), m.group(2), int(m.group(3)), int(m.group(4)))
        for m in EXIT_RE.finditer(cell)
    ]


def cmd_exits(paths: list[str]) -> int:
    rows = read(paths)
    n = len(rows)
    decided = [r for r in rows if r["c_verdict"] in ("sat", "unsat")]
    failing = [r for r in rows if r["c_verdict"] not in ("sat", "unsat")]
    print(f"population re-run at this lane's base: {n} rows")
    print(f"  now DECIDED by main (dropped from every ratio below): {len(decided)}")
    for r in decided:
        print(f"    {r['c_verdict']:5s} {r['file']}")
    print(f"  still failing (the denominator): {len(failing)}")
    print()

    # R1: is any row still giving up with the MERGED string?
    merged = [
        r
        for r in failing
        if "instantiation time budget exhausted" in r["c_giveup"]
        and "round head" not in r["c_giveup"]
        and "mid-round" not in r["c_giveup"]
        and "before a ground check" not in r["c_giveup"]
    ]
    print(f"R1  UNSPLIT give-up rows (a bug in the split, not a bucket): {len(merged)}")
    print()

    print("R2  exits entered, per row (a row may enter the loop several times)")
    per_row_last = Counter()
    per_exit = Counter()
    rows_with_any = 0
    ground_by_kind = defaultdict(list)
    rounds_by_kind = defaultdict(list)
    for r in failing:
        exits = parse_exits(r["c_exits"])
        if exits:
            rows_with_any += 1
            per_row_last[exits[-1][0]] += 1
        else:
            per_row_last["<no loop exit reached>"] += 1
        for kind, _variant, rounds, ground in exits:
            per_exit[kind] += 1
            ground_by_kind[kind].append(ground)
            rounds_by_kind[kind].append(rounds)

    # Every exit the loop HAS, printed even at zero -- an omitted row and a zero
    # row read the same in a table and only one of them is a measurement.
    # The LEFT column is the loop's own `census_kind()` string, derived from the
    # source and not from memory: `InstantiationLoopExit::census_kind` spells
    # Fixpoint as SHAPE, GrowthHeadroom as CLOCK and RoundCeiling as ROUND. A
    # first draft of this list guessed "FIXPOINT" and reported 14 fixpoint exits
    # as an UNLISTED EXIT while printing `FIXPOINT occurrences=0` beside it --
    # a zero that was the maintainer's memory, not a measurement.
    all_kinds = [
        ("SHAPE", "Fixpoint"),
        ("CLOCK", "GrowthHeadroom"),
        ("ROUND", "RoundCeiling"),
        ("timeout-round-head", "RoundHead (discards, NO final check)"),
        ("timeout-mid-round", "MidRound (checked, NOT decided)"),
        ("timeout-ground-check", "GroundCheck (no clock)"),
        ("ground-ceiling", "GroundCeiling"),
    ]
    for kind, what in all_kinds:
        occurrences = per_exit.get(kind, 0)
        last = per_row_last.get(kind, 0)
        g = ground_by_kind.get(kind, [])
        rd = rounds_by_kind.get(kind, [])
        extra = ""
        if g:
            extra = (
                f"  ground median={int(statistics.median(g))} max={max(g)}"
                f"  rounds median={int(statistics.median(rd))} max={max(rd)}"
            )
        print(
            f"  {kind:20s} {what:38s} occurrences={occurrences:4d}  "
            f"last-exit rows={last:4d}{extra}"
        )
    listed = {k for k, _w in all_kinds}
    for kind, count in sorted(per_exit.items()):
        if kind not in listed:
            print(f"  {kind:20s} {'':38s} occurrences={count:4d}   *** UNLISTED EXIT ***")
    print(f"  {'<no loop exit reached>':22s} rows={per_row_last.get('<no loop exit reached>', 0)}")
    print()
    print(f"  rows entering the loop at all: {pct(rows_with_any, len(failing))}")
    discard = sum(
        1
        for r in failing
        if any(k.startswith("timeout-") for k, _v, _r, _g in parse_exits(r["c_exits"]))
    )
    print(f"  rows hitting a DISCARDING exit (round-head/mid-round): {pct(discard, len(failing))}")
    big = sum(
        1
        for r in failing
        if any(
            k.startswith("timeout-") and g >= 400
            for k, _v, _r, g in parse_exits(r["c_exits"])
        )
    )
    print(f"  ... with a discarded set of >= 400 ground terms: {pct(big, len(failing))}")
    print()

    print("R2b  where the clock went (ADR-1941: the OPEN segment is the discriminator)")
    print("  bound_by (last route to hold the clock):")
    for route, count in Counter(r["c_bound_by"] for r in failing).most_common():
        print(f"    {route:34s} {count}")
    opens = [int(r["c_open_ms"]) for r in failing if r["c_open_ms"].isdigit()]
    print(f"  rows reporting an OPEN segment at all: {len(opens)} of {len(failing)}")
    if opens:
        print(
            f"    open_ms median={int(statistics.median(opens))} "
            f"min={min(opens)} max={max(opens)}"
        )
    print("  give-up kinds:")
    for kind, count in Counter(
        (r["c_giveup"].split(" detail=")[0] or "none") for r in failing
    ).most_common():
        print(f"    {kind:40s} {count}")
    return 0


def cmd_replay(paths: list[str]) -> int:
    rows = read(paths)
    failing = [r for r in rows if r["c_verdict"] not in ("sat", "unsat")]
    print(f"R3  held-set replay. Denominator = still-failing rows: {len(failing)}")
    for arm, cell in (
        ("R1 (24 s, min_ground=0)", "r1_lines"),
        ("R2 (60 s, min_ground>0)", "r2_lines"),
    ):
        if all((r.get(cell) or "") == "SKIPPED" for r in failing):
            print(f"  {arm}: SKIPPED (arm not run) -- distinct from 'ran and found nothing'")
            print()
            continue
        verdicts = Counter()
        why = Counter()
        by_exit = defaultdict(Counter)
        rows_with = 0
        rows_unsat = 0
        skipped = 0
        ground_seen: list[int] = []
        exhausted = 0
        for r in failing:
            hits = list(REPLAY_RE.finditer(r.get(cell, "") or ""))
            skipped += len(list(SKIP_RE.finditer(r.get(cell, "") or "")))
            if hits:
                rows_with += 1
            got_unsat = False
            for m in hits:
                verdict, ground, budget = m.group(4), int(m.group(2)), int(m.group(6))
                verdicts[verdict] += 1
                by_exit[m.group(1)][verdict] += 1
                ground_seen.append(ground)
                if m.group(7):
                    why[m.group(7)] += 1
                if int(m.group(5)) >= budget:
                    exhausted += 1
                if verdict == "unsat":
                    got_unsat = True
            if got_unsat:
                rows_unsat += 1
        total = sum(verdicts.values())
        print(f"  {arm}")
        print(f"    rows where the replay FIRED at all: {pct(rows_with, len(failing))}")
        print(f"    replays skipped by the min_ground gate: {skipped}")
        print(f"    replay verdicts ({total} replays): {dict(verdicts) or '{}'}")
        print(f"    replays that SPENT THEIR WHOLE FRESH BUDGET: {pct(exhausted, total)}")
        if ground_seen:
            ground_seen.sort()
            print(
                f"    ground set replayed: median={int(statistics.median(ground_seen))} "
                f"min={ground_seen[0]} max={ground_seen[-1]}"
            )
        print("    verdict by EXIT the set was held at:")
        for kind in sorted(by_exit):
            print(f"      {kind:22s} {dict(by_exit[kind])}")
        print("    why the replay returned `unknown` (its own reason, not a guess):")
        for reason, count in why.most_common():
            print(f"      {count:4d}  {reason}")
        if not why:
            print("      (none)")
        print(f"    *** ROWS WHOSE HELD SET REPLAYS UNSAT: {pct(rows_unsat, len(failing))}")
        # The blindness, published as a number rather than left as a zero.
        blind = 0
        for r in failing:
            exits = parse_exits(r["c_exits"])
            biggest = max((g for _k, _v, _r, g in exits), default=0)
            replayed = max(
                (int(m.group(2)) for m in REPLAY_RE.finditer(r.get(cell, "") or "")),
                default=-1,
            )
            if biggest > 0 and replayed < biggest:
                blind += 1
        print(
            f"    rows whose LARGEST discarded set was never replayed "
            f"(the probe races the watchdog): {pct(blind, len(failing))}"
        )
        print()
    return 0


def cmd_noise(paths: list[str]) -> int:
    """The noise floor, from a SAME-ARM repeat.

    With `r1_ms=0` the replay is off in both arms, so arm C and arm R1 are the
    identical shipped configuration run back to back on the same file on the
    same pinned core with the order rotating. Any difference between the two
    columns is ambient noise at fixed code -- which is what has to be bigger
    than a lever's effect before the lever means anything.
    """
    rows = read(paths)
    n = len(rows)
    print(f"noise floor: SAME arm twice per file, {n} rows")
    print("  (arm C and arm R1 are byte-identical configurations here; r1_ms=0)")
    same = sum(1 for r in rows if r["c_verdict"] == r["r1_verdict"])
    print(f"  verdict identical across the repeat: {pct(same, n)}")
    moved = [r for r in rows if r["c_verdict"] != r["r1_verdict"]]
    for r in moved:
        print(f"    {r['c_verdict']:7s} -> {r['r1_verdict']:7s}  {r['file']}")
    decided_c = sum(1 for r in rows if r["c_verdict"] in ("sat", "unsat"))
    decided_r = sum(1 for r in rows if r["r1_verdict"] in ("sat", "unsat"))
    print(f"  DIVISION TOTAL decided: pass A {decided_c}, pass B {decided_r}  "
          f"(band = |{decided_c - decided_r}| at FIXED CODE)")
    flips = sum(
        1
        for r in rows
        if {r["c_verdict"], r["r1_verdict"]} == {"sat", "unsat"}
    )
    print(f"  sat<->unsat flips across the repeat: {flips}")

    # Exit CLASS stability. A deadline exit and a break exit are different
    # buckets in the census table, so if the class itself is unstable the table
    # has a noise floor too and it must be published beside the table.
    def last_kind(cell: str) -> str:
        exits = parse_exits(cell)
        return exits[-1][0] if exits else "<none>"

    stable = 0
    comparable = 0
    for r in rows:
        a = last_kind(r["c_exits"])
        # Arm R1 logs loop-exit lines into r1_lines when the replay is off.
        b = last_kind(r.get("r1_lines", "") or "")
        if b == "<none>" and a == "<none>":
            continue
        comparable += 1
        if a == b:
            stable += 1
    print(f"  LAST-EXIT CLASS identical across the repeat: {pct(stable, comparable)}")
    return 0


def cmd_ref(paths: list[str]) -> int:
    rows = read(paths)
    n = len(rows)
    print(f"reference (cvc5 1.3.4), 24 s / 8 GiB / one pinned core: {n} rows")
    verdicts = Counter(r["verdict"] for r in rows)
    print(f"  verdicts: {dict(verdicts)}   (NONE is kept DISTINCT from unknown)")
    refuted = [r for r in rows if r["verdict"] == "unsat"]
    times = [int(r["cvc5_ms"]) for r in refuted if r["cvc5_ms"].isdigit()]
    print(f"  refuted: {pct(len(refuted), n)}")
    if times:
        times.sort()
        print(
            f"  cvc5 global::totalTime on the files it REFUTES (n={len(times)}): "
            f"min={times[0]} p25={times[len(times) // 4]} median={int(statistics.median(times))} "
            f"p75={times[3 * len(times) // 4]} max={times[-1]} ms"
        )
        for bound in (100, 500, 1000, 5000):
            k = sum(1 for t in times if t <= bound)
            print(f"    <= {bound:5d} ms: {pct(k, len(times))}")
    tuples = [int(r["tuples"]) for r in refuted if r["tuples"].isdigit()]
    quants = [int(r["quants"]) for r in refuted if r["quants"].isdigit()]
    if tuples:
        print(
            f"  instantiation TUPLES in the winning refutation: "
            f"median={int(statistics.median(tuples))} min={min(tuples)} max={max(tuples)}"
        )
        print(
            f"  quantifiers instantiated: "
            f"median={int(statistics.median(quants))} min={min(quants)} max={max(quants)}"
        )
    return 0


def cmd_compare(argv: list[str]) -> int:
    split = argv.index("--")
    ours = {r["file"]: r for r in read(argv[:split])}
    ref = {r["file"]: r for r in read(argv[split + 1 :])}
    shared = sorted(set(ours) & set(ref))
    print(f"comparable denominator (in BOTH sweeps): {len(shared)}")
    print(f"  ours only: {len(set(ours) - set(ref))}   reference only: {len(set(ref) - set(ours))}")
    pairs = []
    for f in shared:
        o, r = ours[f], ref[f]
        if r["verdict"] != "unsat" or o["c_verdict"] in ("sat", "unsat"):
            continue
        if not r["cvc5_ms"].isdigit():
            continue
        exits = parse_exits(o["c_exits"])
        pairs.append((f, int(r["cvc5_ms"]), int(o["c_ms"]), max((g for *_x, g in exits), default=0)))
    print(f"  rows the reference REFUTES and we still fail: {len(pairs)}")
    if not pairs:
        return 0
    ratios = sorted(ours_ms / max(1, ref_ms) for _f, ref_ms, ours_ms, _g in pairs)
    print(
        f"  our wall / cvc5 own clock: median={statistics.median(ratios):.0f}x "
        f"min={ratios[0]:.0f}x max={ratios[-1]:.0f}x"
    )
    grounds = sorted(g for *_x, g in pairs if g)
    if grounds:
        print(
            f"  our largest ground set at a loop exit: median={int(statistics.median(grounds))} "
            f"max={max(grounds)}  (n={len(grounds)})"
        )
    return 0


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    mode, rest = argv[1], argv[2:]
    if mode == "exits":
        return cmd_exits(rest)
    if mode == "replay":
        return cmd_replay(rest)
    if mode == "ref":
        return cmd_ref(rest)
    if mode == "noise":
        return cmd_noise(rest)
    if mode == "compare":
        return cmd_compare(rest)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
