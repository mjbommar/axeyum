#!/usr/bin/env python3
"""ADR-2132: read the three-arm A/B, and the sizing its `off` arm carries.

Three arms of one lever: A = `off`, B = `on` (ADR-2125's arm, the reference),
C = `screened` (this lane's).  Two comparisons are printed and they answer
different questions -- A vs C is the ship decision, A vs B says whether the
screen changed anything that was there to change.  A `net +0` from C is
meaningless without B beside it: it is equally the reading of a screen that
worked and of a lever that never helped on this population.

Every table prints its own denominators.  A raw MOVER is never a finding here
either; the rows it names go to `recheck-movers.sh` 3x per arm.

Usage: ab3-summarize.py <label>=<ab3.tsv>[,<ab3.tsv>...] ...
"""

import sys
from pathlib import Path

DECIDED = ("sat", "unsat")


def read(paths):
    rows = []
    for p in paths:
        with open(p, encoding="utf-8", errors="replace") as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) < len(head):
                    continue
                rows.append(dict(zip(head, f)))
    return rows


def num(r, key):
    v = (r.get(key) or "").strip()
    try:
        return int(v)
    except ValueError:
        return None


def compare(rows, x, y, xname, yname):
    """One arm against another: gains, losses, flips, and the soundness column."""
    gain = []
    loss = []
    flip = []
    dis = []
    cmp_denom = 0
    xd = yd = 0
    for r in rows:
        xv, yv = r[f"{x}_verdict"], r[f"{y}_verdict"]
        xd += xv in DECIDED
        yd += yv in DECIDED
        if xv in DECIDED and yv in DECIDED and xv != yv:
            flip.append(r["file"])
        elif xv not in DECIDED and yv in DECIDED:
            gain.append(r["file"])
        elif xv in DECIDED and yv not in DECIDED:
            loss.append(r["file"])
        # Soundness against the file's own declared `:status`. A file with no
        # `set-info :status` is in NO denominator -- the comparable denominator
        # is printed rather than implied.
        st = r.get("status", "none")
        if st in DECIDED:
            for arm in (x, y):
                v = r[f"{arm}_verdict"]
                if v in DECIDED:
                    cmp_denom += 1
                    if v != st:
                        dis.append((r["file"], arm, v, st))
    xrc = sum(1 for r in rows if num(r, f"{x}_rc") not in (0, None))
    yrc = sum(1 for r in rows if num(r, f"{y}_rc") not in (0, None))
    print(
        f"  {xname:>9} vs {yname:<9} rows {len(rows):>4}  "
        f"{xname} {xd:>4}  {yname} {yd:>4}  net {yd - xd:+4d}  "
        f"gain {len(gain):>3}  LOSS {len(loss):>3}  FLIP {len(flip):>3}  "
        f"{xname} rc!=0 {xrc:>3}  {yname} rc!=0 {yrc:>3}  cmp {cmp_denom:>4}  DIS {len(dis):>3}"
    )
    for f in gain:
        print(f"      raw GAIN ({xname}->{yname})  {f}")
    for f in loss:
        print(f"      raw LOSS ({xname}->{yname})  {f}")
    for f in flip:
        print(f"      raw FLIP ({xname}->{yname})  {f}")
    for f, arm, v, st in dis:
        print(f"      DISAGREEMENT {f} arm={arm} said {v}, file declares {st}")
    return gain + loss + flip


def mechanism(rows):
    """Did each treatment arm actually run, and did the screen do its job?"""
    for arm, name in (("b", "on"), ("c", "screened")):
        built = sum(1 for r in rows if r.get(f"{arm}_warm_build") == "built")
        checks = sum(num(r, f"{arm}_warm_checks") or 0 for r in rows)
        restarts = sum(num(r, f"{arm}_warm_restarts") or 0 for r in rows)
        peak = max((num(r, f"{arm}_warm_fill_peak") or 0 for r in rows), default=0)
        colds = sum(num(r, f"{arm}_cold_builds") or 0 for r in rows)
        print(
            f"  {name:>9}: rows `built` {built:>4}   cubes answered {checks:>7}   "
            f"cold tableaux left {colds:>7}   cold_restarts {restarts:>3}   "
            f"max fill peak (nnz) {peak:>8}"
        )
    a_cold = sum(num(r, "a_cold_builds") or 0 for r in rows)
    print(f"  {'off':>9}: cold tableaux {a_cold:>7} (the denominator the two above removed from)")
    # The screen's own signature: it must open on FEWER rows than `on` builds on.
    both = [
        r
        for r in rows
        if r.get("b_warm_build") == "built" or r.get("c_warm_build") == "built"
    ]
    on_only = sum(
        1 for r in both if r.get("b_warm_build") == "built" and r.get("c_warm_build") != "built"
    )
    c_only = sum(
        1 for r in both if r.get("c_warm_build") == "built" and r.get("b_warm_build") != "built"
    )
    print(
        f"  the screen REFUSED {on_only} of the rows `on` kept a basis on, and opened on "
        f"{c_only} that `on` did not (the second should be 0)"
    )


def cost(rows):
    """Wall clock on the rows ALL THREE arms decide, and the -9.2 % split."""
    common = [
        r
        for r in rows
        if all(r[f"{a}_verdict"] in DECIDED for a in ("a", "b", "c"))
        and all(num(r, f"{a}_total_ms") is not None for a in ("a", "b", "c"))
    ]
    if not common:
        print("  no row is decided by all three arms; no cost comparison")
        return
    tot = {a: sum(num(r, f"{a}_total_ms") for r in common) for a in ("a", "b", "c")}
    print(f"  rows all three decide: {len(common)}")
    for a, name in (("a", "off"), ("b", "on"), ("c", "screened")):
        d = (tot[a] - tot["a"]) * 100.0 / tot["a"] if tot["a"] else 0.0
        print(f"    {name:>9} total {tot[a]:>9} ms   {d:+7.1f} % against off")

    # THE ATTRIBUTION. Both terms are differences between fields that are ON the
    # trail line, on one interleaved pair of arms over one file -- no
    # counterfactual, no model. See `LazySmtCounters::warm_cube_solve`.
    for arm, name in (("b", "on"), ("c", "screened")):
        sized = [
            r
            for r in common
            if r.get(f"{arm}_warm_build") == "built"
            and all(
                num(r, k) is not None
                for k in (
                    "a_cube_simplex_ms",
                    "a_cube_collect_ms",
                    f"{arm}_cube_simplex_ms",
                    f"{arm}_cube_collect_ms",
                    f"{arm}_warm_solve_ms",
                    f"{arm}_warm_sync_ms",
                )
            )
        ]
        if not sized:
            print(f"    {name}: no row both decides everywhere and kept a basis; NO SPLIT")
            continue
        basis = sum(
            num(r, "a_cube_simplex_ms")
            - num(r, f"{arm}_cube_simplex_ms")
            - num(r, f"{arm}_warm_solve_ms")
            - num(r, f"{arm}_warm_sync_ms")
            for r in sized
        )
        linear = sum(
            num(r, "a_cube_collect_ms") - num(r, f"{arm}_cube_collect_ms") for r in sized
        )
        sync = sum(num(r, f"{arm}_warm_sync_ms") for r in sized)
        solve = sum(num(r, f"{arm}_warm_solve_ms") for r in sized)
        total = basis + linear
        share = (lambda v: f"{v * 100.0 / total:6.1f} %" if total else "     -- ")
        print(
            f"    {name}: over {len(sized)} rows that decided everywhere AND kept a basis --\n"
            f"        saved by the BASIS         {basis:>8} ms  {share(basis)}\n"
            f"        saved by the LINEARIZATION {linear:>8} ms  {share(linear)}\n"
            f"        (the warm arm PAID: sync {sync} ms + solve {solve} ms)"
        )


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    movers = []
    for arg in sys.argv[1:]:
        label, _, paths = arg.partition("=")
        ps = [Path(p) for p in paths.split(",")]
        missing = [p for p in ps if not p.is_file()]
        if missing:
            print(f"== {label}: DID NOT RUN -- missing {', '.join(str(m) for m in missing)}\n")
            continue
        rows = read(ps)
        print(f"== {label}: {len(rows)} rows")
        movers += compare(rows, "a", "c", "off", "screened")
        movers += compare(rows, "a", "b", "off", "on")
        print("  -- mechanism --")
        mechanism(rows)
        print("  -- cost --")
        cost(rows)
        print()
    if movers:
        print("RAW MOVERS (feed to recheck-movers.sh; a raw mover is not a finding):")
        for f in sorted(set(movers)):
            print(f"  {f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
