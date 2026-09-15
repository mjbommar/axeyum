#!/usr/bin/env python3
"""REAL-OPAQUE -- summarise an interleaved A/B, verdicts AND exit statuses.

Reads one or more `ab-run.sh` TSVs and prints, per division:

  * verdict moves     off -> on, split into GAIN / LOSS / FLIP
  * EXIT-STATUS moves off -> on, split the same way

The second block is the one ADR-2045 did not have. Its arm was `losses=0` by
verdict count while creating FIVE new aborts on files that terminated cleanly in
the base; a verdict count cannot see that, because an aborted run and a genuine
`unknown` both read `unknown`. **A base-`ok` row that is non-`ok` in the lever
arm is a LOSS even when both verdicts read `unknown`**, and this script counts it
as one.

A FLIP is `sat <-> unsat`. It is a wrong verdict on one side or the other and is
reported separately from a gain, never folded into a net.

Usage: ab-summarize.py <label> <tsv> [<tsv> ...]
"""

import sys
from collections import Counter

DECIDED = {"sat", "unsat"}


def classify_verdict(off, on):
    if off == on:
        return "same"
    if off in DECIDED and on in DECIDED:
        return "FLIP"
    if on in DECIDED and off not in DECIDED:
        return "gain"
    if off in DECIDED and on not in DECIDED:
        return "LOSS"
    return "same-undecided"


def main(argv):
    label = argv[1]
    rows = []
    for path in argv[2:]:
        with open(path) as fh:
            # `ab-noise.sh` writes a leading `#` banner saying both halves are
            # the same arm. Skip comment lines rather than mistaking one for the
            # header, which would silently drop the file's first data row.
            line = fh.readline()
            while line.startswith("#"):
                line = fh.readline()
            header = line.rstrip("\n").split("\t")
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) != len(header):
                    print(f"MALFORMED ROW in {path}: {len(parts)} fields", file=sys.stderr)
                    return 2
                rows.append(dict(zip(header, parts)))

    verdict = Counter()
    exitmove = Counter()
    gains, losses, flips, exit_regressions = [], [], [], []

    for r in rows:
        v = classify_verdict(r["off_verdict"], r["on_verdict"])
        verdict[v] += 1
        if v == "gain":
            gains.append(r)
        elif v == "LOSS":
            losses.append(r)
        elif v == "FLIP":
            flips.append(r)

        oe, ne = r["off_exit"], r["on_exit"]
        if oe == ne:
            exitmove["same"] += 1
        elif oe == "ok" and ne != "ok":
            exitmove["REGRESSION"] += 1
            exit_regressions.append(r)
        elif oe != "ok" and ne == "ok":
            exitmove["improvement"] += 1
        else:
            exitmove["other-change"] += 1

    n = len(rows)
    print(f"== {label} ==  rows={n}  files={len({r['file'] for r in rows})}")
    print("  VERDICT   " + "  ".join(f"{k}={v}" for k, v in sorted(verdict.items())))
    print("  EXIT      " + "  ".join(f"{k}={v}" for k, v in sorted(exitmove.items())))
    print(f"  NET (gains - losses - flips) = {len(gains) - len(losses) - len(flips)}")
    print(f"  EXIT REGRESSIONS (base ok -> lever not ok) = {len(exit_regressions)}")

    # Denominators beside every zero (R3/R8): a zero over an empty population is
    # not the same statement as a zero over 200 rows, and neither is a zero over
    # a population where nothing was ever undecided to begin with.
    undecided_base = sum(1 for r in rows if r["off_verdict"] not in DECIDED)
    ok_base = sum(1 for r in rows if r["off_exit"] == "ok")
    print(f"  denominators: undecided in base = {undecided_base}/{n}, ok in base = {ok_base}/{n}")

    for title, bucket in (
        ("GAINS", gains),
        ("LOSSES", losses),
        ("FLIPS", flips),
        ("EXIT REGRESSIONS", exit_regressions),
    ):
        if not bucket:
            continue
        print(f"\n  -- {title} ({len(bucket)}) --")
        for r in bucket:
            print(
                f"     {r['file'].split('non-incremental/')[-1]}\n"
                f"        off={r['off_verdict']}/{r['off_exit']}/{r['off_route']} "
                f"{r['off_ms']}ms\n"
                f"        on ={r['on_verdict']}/{r['on_exit']}/{r['on_route']} "
                f"{r['on_ms']}ms  order={r['order']}"
            )

    # Wall clock, as a ratio, because a lever that buys rows by spending the
    # whole budget is a different trade from one that is free.
    off_ms = sum(int(r["off_ms"]) for r in rows)
    on_ms = sum(int(r["on_ms"]) for r in rows)
    if off_ms:
        print(f"\n  wall clock: off={off_ms / 1000:.1f}s on={on_ms / 1000:.1f}s "
              f"ratio={on_ms / off_ms:.2f}x")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
