#!/usr/bin/env python3
"""Join the census buckets against which reference ENGINE decided each file.

ADR-2110, lane NRA-TRACE.

The question this answers is not "does z3 decide it" -- the head-to-head
answered that. It is which engine inside z3 decides it, because the two
candidates are a different amount of work for us:

  * `z3-nlsat` is model-constructing satisfiability with CAD cell projection.
  * `z3-lin` is incremental linearization with `smt.arith.nl.nra=false`, i.e.
    abstract each monomial, drive an LP, refute with tangent / order /
    monotonicity / Grobner lemmas -- the same shape as `axeyum-solver/src/nra.rs`.

So the split between those two arms IS the sizing of the gap. A file only
`z3-nlsat` decides is a file no amount of lemma work on our existing route
reaches; a file `z3-lin` decides is one our architecture can in principle hold.

`none` (no verdict token at all) and `unknown` are counted apart: the first is
a run that produced nothing, the second one that reported it could not decide.
Collapsing them would read an absent arm as a capability statement.
"""

from __future__ import annotations

import argparse
import collections
from pathlib import Path


def read_tsv(path: Path) -> tuple[list[str], list[list[str]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    return header, [line.split("\t") for line in lines[1:] if line]


DECIDED = ("sat", "unsat")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--census", required=True)
    ap.add_argument("--reference", required=True)
    ap.add_argument("--tsv")
    args = ap.parse_args()

    chead, crows = read_tsv(Path(args.census))
    census = {r[chead.index("file")]: dict(zip(chead, r, strict=False)) for r in crows}

    rhead, rrows = read_tsv(Path(args.reference))
    ref: dict[str, dict[str, str]] = collections.defaultdict(dict)
    ms: dict[str, dict[str, int]] = collections.defaultdict(dict)
    for r in rrows:
        row = dict(zip(rhead, r, strict=False))
        ref[row["file"]][row["arm"]] = row["verdict"]
        ms[row["file"]][row["arm"]] = int(row["ms"])

    arms = ["z3-default", "z3-nlsat", "z3-lin", "cvc5"]
    files = sorted(census)
    missing = [f for f in files if f not in ref]

    print(f"census files {len(files)}   reference files {len(ref)}\n")

    print("== per arm, over the files we do NOT decide ==")
    print(f"  {'arm':12s} {'sat':>5s} {'unsat':>6s} {'unknown':>8s} {'none':>5s} "
          f"{'decided':>8s}")
    for arm in arms:
        counts = collections.Counter(ref[f].get(arm, "absent") for f in files)
        decided = counts["sat"] + counts["unsat"]
        print(f"  {arm:12s} {counts['sat']:5d} {counts['unsat']:6d} "
              f"{counts['unknown']:8d} {counts['none']:5d} {decided:8d}")

    print("\n== BUCKET x REFERENCE ENGINE (files decided by each arm) ==")
    buckets: dict[str, list[str]] = collections.defaultdict(list)
    for f in files:
        buckets[census[f]["bucket"]].append(f)
    order = sorted(buckets, key=lambda k: (-len(buckets[k]), k))
    print(f"  {'bucket':52s} {'n':>3s} {'z3':>4s} {'nlsat':>6s} {'lin':>4s} "
          f"{'cvc5':>5s}")
    for key in order:
        members = buckets[key]

        def dec(arm: str, group: list[str] = members) -> int:
            return sum(1 for f in group if ref[f].get(arm) in DECIDED)

        print(f"  {key[:52]:52s} {len(members):3d} {dec('z3-default'):4d} "
              f"{dec('z3-nlsat'):6d} {dec('z3-lin'):4d} {dec('cvc5'):5d}")

    print("\n== the decisive split ==")
    nlsat_only = [
        f for f in files
        if ref[f].get("z3-nlsat") in DECIDED and ref[f].get("z3-lin") not in DECIDED
    ]
    lin_too = [
        f for f in files
        if ref[f].get("z3-lin") in DECIDED
    ]
    neither = [
        f for f in files
        if ref[f].get("z3-nlsat") not in DECIDED and ref[f].get("z3-lin") not in DECIDED
    ]
    print(f"  decided by the CAD engine and NOT by linearization : {len(nlsat_only):3d}")
    print(f"  decided by linearization too                        : {len(lin_too):3d}")
    print(f"  decided by neither z3 arm                           : {len(neither):3d}")

    print("\n  how fast the CAD engine was on the files only it decides:")
    times = sorted(ms[f].get("z3-nlsat", 0) for f in nlsat_only)
    if times:
        mid = times[len(times) // 2]
        under1s = sum(1 for t in times if t < 1000)
        print(f"    median {mid} ms, {under1s} of {len(times)} under 1 s, "
              f"max {times[-1]} ms")

    if args.tsv:
        cols = ("file", "bucket", "status", "n_vars", "max_degree",
                "z3_default", "z3_default_ms", "z3_nlsat", "z3_nlsat_ms",
                "z3_lin", "z3_lin_ms", "cvc5", "cvc5_ms")
        with open(args.tsv, "w", encoding="utf-8") as fh:
            fh.write("\t".join(cols) + "\n")
            for f in files:
                c = census[f]
                fh.write("\t".join(str(x) for x in (
                    f, c["bucket"], c["status"], c["n_vars"], c["max_degree"],
                    ref[f].get("z3-default", "absent"), ms[f].get("z3-default", ""),
                    ref[f].get("z3-nlsat", "absent"), ms[f].get("z3-nlsat", ""),
                    ref[f].get("z3-lin", "absent"), ms[f].get("z3-lin", ""),
                    ref[f].get("cvc5", "absent"), ms[f].get("cvc5", ""),
                )) + "\n")
        print(f"\nwrote {args.tsv}")

    if missing:
        print(f"\nreference-join: {len(missing)} census files with NO reference row",
              flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
