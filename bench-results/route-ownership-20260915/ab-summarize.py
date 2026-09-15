#!/usr/bin/env python3
"""Summarise the ADR-2100 interleaved A/B.

Four channels, and each is reported SEPARATELY rather than folded into one
number, because they fail in different ways:

- **verdict**: gains, losses, and `sat`<->`unsat` FLIPS. A flip is not a loss and
  a loss is not a flip; the exit criterion is 0 of each and a combined "net"
  column would hide a flip behind a gain.
- **exit status**: its own column. ADR-2045 measured `losses=0` by verdict and
  five new ABORTS underneath it, so a run that keeps every verdict and changes
  how the process ended has changed something the verdict column cannot see.
- **soundness**: every decided row against the file's declared `:status`, with
  the COMPARABLE DENOMINATOR published beside the disagreement count. ADR-1957
  requires it, and ADR-1966 published a "three-way check" one of whose
  authorities was comparable on 0 of 23.
- **malformed rows**: counted and listed, never scored as unchanged. Reading a
  parse failure of the results file as "no movement" is how a measurement
  manufactures a null (ADR-1966 excluded 39 such rows by name).

Usage: ab-summarize.py <tsv>...
"""

import sys
from collections import defaultdict

DECIDED = {"sat", "unsat"}


def main():
    rows = defaultdict(list)
    malformed = []
    for path in sys.argv[1:]:
        for line in open(path):
            cells = line.rstrip("\n").split("\t")
            if cells[0] == "file":
                continue
            if len(cells) != 9:
                malformed.append((path, line.rstrip("\n")[:120]))
                continue
            rows[cells[0].split("/", 1)[0]].append(cells)

    print(
        f"{'division':<12} {'rows':>5} {'A':>4} {'B':>4} {'net':>5} "
        f"{'gain':>5} {'LOSS':>5} {'FLIP':>5} {'rc!=':>5} {'cmp':>5} {'DIS':>4}"
    )
    tot = defaultdict(int)
    loss_rows, flip_rows, rc_rows, dis_rows = [], [], [], []
    for div in sorted(rows):
        a_dec = b_dec = gain = loss = flip = rc_diff = comparable = disagree = 0
        for path, a, _a_ms, a_rc, b, _b_ms, b_rc, _first, status in rows[div]:
            a_dec += a in DECIDED
            b_dec += b in DECIDED
            if a not in DECIDED and b in DECIDED:
                gain += 1
            if a in DECIDED and b not in DECIDED:
                loss += 1
                loss_rows.append((path, a, b))
            if a in DECIDED and b in DECIDED and a != b:
                flip += 1
                flip_rows.append((path, a, b))
            if a_rc != b_rc:
                rc_diff += 1
                rc_rows.append((path, a_rc, b_rc))
            if status in DECIDED and b in DECIDED:
                comparable += 1
                if status != b:
                    disagree += 1
                    dis_rows.append((path, status, b))
        n = len(rows[div])
        print(
            f"{div:<12} {n:>5} {a_dec:>4} {b_dec:>4} {b_dec - a_dec:>+5} "
            f"{gain:>5} {loss:>5} {flip:>5} {rc_diff:>5} {comparable:>5} {disagree:>4}"
        )
        for key, val in (
            ("rows", n), ("a", a_dec), ("b", b_dec), ("gain", gain), ("loss", loss),
            ("flip", flip), ("rc", rc_diff), ("cmp", comparable), ("dis", disagree),
        ):
            tot[key] += val
    print(
        f"{'TOTAL':<12} {tot['rows']:>5} {tot['a']:>4} {tot['b']:>4} "
        f"{tot['b'] - tot['a']:>+5} {tot['gain']:>5} {tot['loss']:>5} "
        f"{tot['flip']:>5} {tot['rc']:>5} {tot['cmp']:>5} {tot['dis']:>4}"
    )
    print()
    print(f"malformed rows (excluded, not scored as unchanged): {len(malformed)}")
    for path, line in malformed[:10]:
        print(f"  {path}: {line}")
    for name, listing in (
        ("LOSSES", loss_rows), ("FLIPS", flip_rows),
        ("EXIT-STATUS DIFFERENCES", rc_rows), ("STATUS DISAGREEMENTS", dis_rows),
    ):
        print(f"\n{name}: {len(listing)}")
        for item in listing[:25]:
            print(f"  {item}")

    # The exit criterion, as an exit STATUS: a summary that prints a failure and
    # returns 0 is a checker that cannot fail.
    bad = tot["loss"] + tot["flip"] + tot["rc"] + tot["dis"] + len(malformed)
    print(f"\nCRITERION losses+flips+rc-differences+disagreements+malformed = {bad}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
