#!/usr/bin/env python3
"""Render the ADR-2122 A/B tables in Markdown, with every denominator printed.

This exists so the ADR's numbers are GENERATED from the committed TSVs rather
than transcribed from a terminal. A transcribed table is a second copy of the
data that can drift from the first, and the drift is invisible.

Three things it refuses to do:

  * report a division with no rows as "net +0" -- it prints **did not run**,
    because a division with no rows is not a division with no movement;
  * report a PARTIAL division without saying so -- if the row count is below
    the list's, the row is marked `PARTIAL n/N` and the share is computed on n;
  * imply a soundness denominator -- the `cmp` column is the rows that have BOTH
    a declared `:status` and a decided verdict, and it is printed beside the
    disagreement count.

Usage:
    ab-report.py <label>=<tsv>[:<expected-rows>] [...]
"""

from __future__ import annotations

import sys
from pathlib import Path

DECIDED = {"sat", "unsat"}


def load(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    lines = path.read_text().splitlines()
    if not lines:
        return []
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"), strict=False)) for ln in lines[1:] if ln.strip()]


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        sys.stderr.write(__doc__ or "")
        return 2
    print("| population | rows | A | B | net | gain | LOSS | FLIP | A rc≠0 | B rc≠0 | cmp | DIS |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    movers: list[str] = []
    dis: list[str] = []
    tot = [0] * 10
    for spec in argv[1:]:
        label, _, rest = spec.partition("=")
        p, _, expected = rest.partition(":")
        rows = load(Path(p))
        want = int(expected) if expected else None
        if not rows:
            print(f"| {label} | 0 | — | — | — | — | — | — | — | — | — | **did not run** |")
            continue
        a = sum(1 for r in rows if r["A"] in DECIDED)
        b = sum(1 for r in rows if r["B"] in DECIDED)
        g = [r for r in rows if r["A"] not in DECIDED and r["B"] in DECIDED]
        l = [r for r in rows if r["A"] in DECIDED and r["B"] not in DECIDED]
        f = [r for r in rows if r["A"] in DECIDED and r["B"] in DECIDED and r["A"] != r["B"]]
        arc = sum(1 for r in rows if r["A_rc"] != "0")
        brc = sum(1 for r in rows if r["B_rc"] != "0")
        cmp_rows = [r for r in rows if r["status"] in DECIDED and r["B"] in DECIDED]
        d = [r for r in cmp_rows if r["B"] != r["status"]]
        name = label
        if want is not None and len(rows) != want:
            name = f"{label} **PARTIAL {len(rows)}/{want}**"
        print(
            f"| {name} | {len(rows)} | {a} | {b} | {b - a:+d} | {len(g)} | {len(l)} | "
            f"{len(f)} | {arc} | {brc} | {len(cmp_rows)} | {len(d)} |"
        )
        for kind, rs in (("GAIN", g), ("LOSS", l), ("FLIP", f)):
            movers += [f"{label}\t{kind}\t{r['file']}\tA={r['A']}\tB={r['B']}" for r in rs]
        dis += [f"{label}\t{r['file']}\tdeclared={r['status']}\tB={r['B']}" for r in d]
        for i, v in enumerate([len(rows), a, b, b - a, len(g), len(l), len(f), arc, brc, len(cmp_rows)]):
            tot[i] += v
    print(
        f"| **TOTAL** | **{tot[0]}** | **{tot[1]}** | **{tot[2]}** | **{tot[3]:+d}** | "
        f"**{tot[4]}** | **{tot[5]}** | **{tot[6]}** | **{tot[7]}** | **{tot[8]}** | "
        f"**{tot[9]}** | **{len(dis)}** |"
    )
    print()
    print(f"MOVERS: {len(movers)}")
    for m in movers:
        print("  " + m)
    if not movers:
        print("  (none -- so the 3x recheck has a COMPARABLE DENOMINATOR OF 0, which is")
        print("   the absence of anything to re-check and not evidence of stability)")
    print()
    print(f"SOUNDNESS DISAGREEMENTS: {len(dis)}")
    for x in dis:
        print("  " + x)
    return 1 if dis else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
