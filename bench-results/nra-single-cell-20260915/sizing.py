#!/usr/bin/env python3
"""Size the single-cell CAD slice against ADR-2110's 45 CAD-decided files.

Lane NRA-SINGLE-CELL, ADR-2121. Exit criterion 1.

ADR-2110 measured 45 of the 83 undecided QF_NRA files as "decided by z3's CAD
arm (`qfnra-nlsat`) and NOT by its incremental-linearization arm".  That set is
the population a model-constructing CAD route could in principle reach.  This
script asks the only question that sizes THIS lane's slice: how many of those 45
fall inside the bounds the slice actually accepts.

The bounds are declared here and enforced in code by `CellPolicy` --
`max_vars`, `max_degree`, and the pre-existing `MAX_ABS_COEFF = 1 << 40`
coefficient clearing that ADR-2110 claim 2 records as a capability gap this
slice does NOT close.

Two numbers come out, and they are different questions:

  * the BOUND ceiling  -- files inside (vars, degree, coefficient) only.
  * the SHAPE ceiling  -- of those, the ones that are also a single assertion
    with no top-level `or`, which is the conjunctive shape the first slice
    handles.  A file outside this is not out of reach in principle (the clause
    loop generalises) but is out of reach for the code this lane ships.

Neither is a prediction of wins.  A file inside the bounds is a file the route
is ALLOWED to attempt; whether it decides it is what the A/B measures.  Quoting
the ceiling as a win count is the error this docstring exists to prevent.
"""

from __future__ import annotations

import argparse
import collections
from pathlib import Path

DECIDED = ("sat", "unsat")

MAX_VARS = 4
MAX_DEGREE = 8
MAX_COEFF_LOG2 = 40


def read_tsv(path: Path) -> list[dict[str, str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    return [dict(zip(header, ln.split("\t"), strict=False)) for ln in lines[1:] if ln]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--join", required=True, help="reference-join-83.tsv")
    ap.add_argument("--shape", required=True, help="shape-83.tsv")
    ap.add_argument("--tsv", help="write the per-file verdict table here")
    args = ap.parse_args()

    join = {r["file"]: r for r in read_tsv(Path(args.join))}
    shape = {r["file"]: r for r in read_tsv(Path(args.shape))}

    if set(join) != set(shape):
        only_join = sorted(set(join) - set(shape))
        only_shape = sorted(set(shape) - set(join))
        print(f"PARTITION MISMATCH: join-only {len(only_join)} "
              f"shape-only {len(only_shape)}")
        for f in (only_join + only_shape)[:5]:
            print(f"  {f}")
        return 1

    files = sorted(join)
    print(f"population: {len(files)} undecided QF_NRA files (ADR-2110 census)\n")

    cad_only = [
        f for f in files
        if join[f]["z3_nlsat"] in DECIDED and join[f]["z3_lin"] not in DECIDED
    ]
    print(f"ADR-2110's CAD-only set (nlsat decides, lin does not): {len(cad_only)}")
    if len(cad_only) != 45:
        print(f"  CONTROL FAILED: ADR-2110 records 45, this join gives "
              f"{len(cad_only)}")
        return 1
    print("  control: reproduces ADR-2110's 45\n")

    rows = []
    reasons: collections.Counter[str] = collections.Counter()
    for f in cad_only:
        s = shape[f]
        nv, deg = int(s["n_vars"]), int(s["max_degree"])
        clog = int(s["max_abs_int_log2"])
        nass, top_or = int(s["n_assert"]), int(s["has_top_or"])
        out = []
        if nv > MAX_VARS:
            out.append("vars")
        if deg > MAX_DEGREE:
            out.append("degree")
        if clog > MAX_COEFF_LOG2:
            out.append("coeff")
        in_bounds = not out
        shape_out = list(out)
        if nass > 1:
            shape_out.append("multi-assert")
        if top_or:
            shape_out.append("top-or")
        in_shape = not shape_out
        reasons["+".join(out) if out else "IN-BOUNDS"] += 1
        rows.append((f, nv, deg, clog, nass, top_or, in_bounds, in_shape,
                     join[f]["status"], join[f]["z3_nlsat_ms"]))

    in_bounds = [r for r in rows if r[6]]
    in_shape = [r for r in rows if r[7]]

    print("== the ceiling ==")
    print(f"  bounds: vars <= {MAX_VARS}, degree <= {MAX_DEGREE}, "
          f"|coeff| <= 1<<{MAX_COEFF_LOG2}")
    print(f"  inside the BOUND ceiling : {len(in_bounds)} of {len(cad_only)}")
    print(f"  inside the SHAPE ceiling : {len(in_shape)} of {len(cad_only)}"
          f"   (also 1 assertion, no top-level or)\n")

    print("== why the rest are out (bound reasons only) ==")
    for key, n in reasons.most_common():
        print(f"  {key:24s} {n:3d}")

    excl_coeff = sum(1 for r in rows if r[3] > MAX_COEFF_LOG2)
    print(f"\n  excluded by the 1<<{MAX_COEFF_LOG2} coefficient clearing alone: "
          f"{excl_coeff} of {len(cad_only)}")

    print("\n== the in-bounds files, by declared status ==")
    st = collections.Counter(r[8] for r in in_bounds)
    for k, v in sorted(st.items()):
        print(f"  {k:10s} {v:3d}")

    if in_bounds:
        times = sorted(int(r[9]) for r in in_bounds if r[9])
        if times:
            print(f"\n  z3 nlsat on the in-bounds set: median "
                  f"{times[len(times) // 2]} ms, max {times[-1]} ms, "
                  f"{sum(1 for t in times if t < 1000)} of {len(times)} under 1 s")

    if args.tsv:
        cols = ("file", "n_vars", "max_degree", "max_abs_int_log2", "n_assert",
                "has_top_or", "in_bound_ceiling", "in_shape_ceiling",
                "declared_status", "z3_nlsat_ms")
        with open(args.tsv, "w", encoding="utf-8") as fh:
            fh.write("\t".join(cols) + "\n")
            for r in rows:
                fh.write("\t".join(str(x) for x in r) + "\n")
        print(f"\nwrote {args.tsv}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
