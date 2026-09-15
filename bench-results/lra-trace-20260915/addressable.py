#!/usr/bin/env python3
"""Cross-tabulate OUR sub-bucket against whether any reference decides the row.

A bucket's SIZE and a bucket's ADDRESSABILITY are different quantities and this
lane found that they order the population differently: the largest bucket by
count is not the largest by how much of it any reference can reach at the same
budget. A lane that sizes work from the census alone picks the wrong one.

"Addressable" here means exactly one thing, stated so it cannot drift: at least
one of z3 `smt.arith.solver=6`, z3 `smt.arith.solver=2`, or cvc5 1.3.4 returned
`sat` or `unsat` on the SAME file under the SAME 24 s / 8 GiB envelope on the
same pinned core. It is not a claim that the row is winnable by us, and a row
nobody decides is not proof that it is unwinnable -- only that it is not
reachable by these three at this budget, which is the honest ceiling on what a
gap number can promise.

Usage:  addressable.py <buckets-93.tsv> <ref.*.tsv>...
"""

from __future__ import annotations

import sys
from pathlib import Path

DECIDED = {"sat", "unsat"}


def load(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    lines = path.read_text().splitlines()
    head = lines[0].split("\t")
    return head, [
        dict(zip(head, ln.split("\t"), strict=True)) for ln in lines[1:] if ln
    ]


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        sys.stderr.write(__doc__ or "")
        return 2
    _, brows = load(Path(argv[1]))
    decided: set[str] = set()
    seen: set[str] = set()
    for p in argv[2:]:
        _, rrows = load(Path(p))
        for r in rrows:
            seen.add(r["file"])
            if any(r[c] in DECIDED for c in ("z3s6", "z3s2", "cvc5")):
                decided.add(r["file"])

    missing = [r["file"] for r in brows if r["file"] not in seen]
    if missing:
        for m in missing:
            sys.stderr.write(f"NO REFERENCE ROW\t{m}\n")
        sys.stderr.write(
            f"addressable: {len(missing)} of {len(brows)} bucket rows have no "
            "reference row; the table below would be a measurement of the "
            "matched subset, not of the population\n"
        )
        return 2

    agg: dict[str, list[int]] = {}
    for r in brows:
        prose = r["detail"].split(";")[0].split("(")[0].strip()[:56]
        if prose.startswith("memory allocation of"):
            prose = "memory allocation of <n> bytes failed"
        key = f"{r['bucket']} | {prose}" if prose else r["bucket"]
        a = agg.setdefault(key, [0, 0])
        a[0] += 1
        if r["file"] in decided:
            a[1] += 1

    print(f"population {len(brows)}   addressable {len(decided)}")
    print()
    print(f"{'sub-bucket':<72}{'n':>4}{'addr':>6}{'share':>8}")
    print("-" * 90)
    for k, (tot, dec) in sorted(agg.items(), key=lambda kv: (-kv[1][1], -kv[1][0])):
        print(f"{k:<72}{tot:>4}{dec:>6}{dec / tot:>8.0%}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
