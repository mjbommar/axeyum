#!/usr/bin/env python3
"""ADR-2125 A/B: verdict movement, soundness, and cost, per population.

Every table prints the rows it actually has. A division's denominator is never
implied, and a population with no rows is reported as **did not run** rather than
as zero movement -- ADR-2111's exposure arm had to make exactly that distinction
after reporting four empty divisions, and ADR-2122 repeated it.

Columns:
  A / B    rows each arm DECIDED (sat or unsat)
  gain     B decided, A did not          LOSS     A decided, B did not
  FLIP     both decided, and disagreed -- a sat/unsat contradiction, the worst
           outcome this instrument can report
  cmp      rows whose file declares a `:status` AND that some arm decided: the
           COMPARABLE denominator for the soundness column
  DIS      verdicts contradicting the declared `:status`

The mechanism columns are printed beside them because a `net +0` from an arm that
never ran is indistinguishable from a `net +0` from one that ran and did not
help -- ADR-2111 shipped a lever whose arm was INERT on its own target population
and had to publish that reading.

Usage: ab-summarize.py <tag> <ab.*.tsv>...
"""

import statistics
import sys


def load(paths):
    rows, header = [], None
    for path in paths:
        try:
            lines = open(path).read().splitlines()
        except OSError:
            continue
        if not lines:
            continue
        cols = lines[0].split("\t")
        if header is None:
            header = cols
        elif header != cols:
            sys.exit(f"ABORT: {path} has a different header; refusing to pool")
        for line in lines[1:]:
            parts = line.split("\t")
            if len(parts) == len(cols):
                rows.append(dict(zip(cols, parts)))
    return rows


def decided(v):
    return v in ("sat", "unsat")


def main(tag, paths):
    rows = load(paths)
    if not rows:
        print(f"{tag}: DID NOT RUN (0 rows) -- not the same statement as zero movement")
        return
    a = sum(1 for r in rows if decided(r["a_verdict"]))
    b = sum(1 for r in rows if decided(r["b_verdict"]))
    gains = [r for r in rows if decided(r["b_verdict"]) and not decided(r["a_verdict"])]
    losses = [r for r in rows if decided(r["a_verdict"]) and not decided(r["b_verdict"])]
    flips = [
        r
        for r in rows
        if decided(r["a_verdict"])
        and decided(r["b_verdict"])
        and r["a_verdict"] != r["b_verdict"]
    ]

    cmp_n, dis = 0, []
    for r in rows:
        st = r.get("status", "none")
        if st not in ("sat", "unsat"):
            continue
        for arm in ("a", "b"):
            v = r[f"{arm}_verdict"]
            if not decided(v):
                continue
            cmp_n += 1
            if v != st:
                dis.append((r["file"], arm, v, st))

    arc = sum(1 for r in rows if r["a_rc"] != "0")
    brc = sum(1 for r in rows if r["b_rc"] != "0")

    print(f"=== {tag} ===")
    print(
        f"rows {len(rows)}   A {a}   B {b}   net {b - a:+d}   "
        f"gain {len(gains)}   LOSS {len(losses)}   FLIP {len(flips)}   "
        f"A rc!=0 {arc}   B rc!=0 {brc}   cmp {cmp_n}   DIS {len(dis)}"
    )
    for f, arm, v, st in dis:
        print(f"  DISAGREEMENT arm {arm}: said {v}, file declares {st} -- {f}")
    for label, rs in (("GAIN", gains), ("LOSS", losses), ("FLIP", flips)):
        for r in rs:
            print(f"  {label}: {r['file']}  A={r['a_verdict']} B={r['b_verdict']}")

    # The mechanism. A row where `warm_cube_build` is not `built` is a row this
    # lever could not have moved, and pooling it with the rest hides an inert
    # arm behind a population that never reached the route.
    builds = {}
    for r in rows:
        builds[r.get("b_warm_build", "") or "none"] = (
            builds.get(r.get("b_warm_build", "") or "none", 0) + 1
        )
    # `off` in ARM B never means "the lever is off" -- the lever is read once per
    # process and arm B always has it on. It means `record_warm_cube_build` was
    # never called, i.e. the `; lazy-smt` line came from the NRA or NIA loop
    # rather than the linear one (the three loops share these counters). `none`
    # means no `; lazy-smt` line at all. Spelled out because a reader who takes
    # `off` at face value would conclude the arm was disabled on those rows.
    print(
        "  arm B `warm_cube_build`: "
        + "  ".join(f"{k}={v}" for k, v in sorted(builds.items()))
        + "   [in arm B, `off` = the LINEAR lazy-SMT loop was never entered]"
    )
    live = [r for r in rows if r.get("b_warm_build") == "built"]
    if live:
        checks = sum(int(r["b_warm_checks"] or 0) for r in live)
        decl = sum(int(r["b_warm_declines"] or 0) for r in live)
        restarts = sum(int(r["b_warm_cold_restarts"] or 0) for r in live)
        acold = sum(int(r["a_cold_builds"] or 0) for r in live)
        bcold = sum(int(r["b_cold_builds"] or 0) for r in live)
        print(
            f"  over the {len(live)} rows where the decider was built: "
            f"{checks} cubes answered, {decl} declined; "
            f"from-scratch tableaux {acold} -> {bcold}"
        )
        # The tripwire. A warm basis that is being rebuilt gives identical
        # verdicts, identical counts, and differs only in the clock.
        print(
            f"  warm_cube_cold_restarts total: {restarts}"
            + ("" if restarts == 0 else "   <-- NONZERO: the basis was NOT kept")
        )

    # Cost, on the rows BOTH arms decide. Verdicts are not the only axis, and a
    # lever that buys nothing can still cost something.
    both = [
        r
        for r in rows
        if decided(r["a_verdict"]) and decided(r["b_verdict"]) and r["a_ms"] and r["b_ms"]
    ]
    if both:
        at = sum(int(r["a_ms"]) for r in both)
        bt = sum(int(r["b_ms"]) for r in both)
        delta = 100.0 * (bt - at) / at if at else 0.0
        am = statistics.median(int(r["a_ms"]) for r in both)
        bm = statistics.median(int(r["b_ms"]) for r in both)
        print(
            f"  cost over the {len(both)} rows both decide: "
            f"A {at} ms   B {bt} ms   {delta:+.1f} %   median A {am} ms  B {bm} ms"
        )
    print()


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2:])
