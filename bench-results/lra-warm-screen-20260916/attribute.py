#!/usr/bin/env python3
"""ADR-2132: decompose the warm decider's theory-layer saving, from the captures.

# Why this is not two terms

[ADR-2125] measured the warm basis at -9.2 % of wall clock and told its successor
not to credit that to the basis without splitting it, naming TWO things a cube
the decider answers skips: the from-scratch simplex and the per-cube
linearization.  Written as two terms, that split did not reconcile.  On
`QF_LRA/clock_synchro/clocksynchro_2clocks.main_invar.base.smt2` the `on` arm is
**1,906 ms** faster and the two terms account for **64 ms** of it.

The captures say why.  Both arms run the SAME 128 rounds and learn the same 127
blocking clauses; the whole difference is `theory_ms`, 1,905 -> 7.  And of the
off arm's 1,905 ms, only 23 + 45 = 68 are collect + simplex.  The rest is
`cube_fm_ms`: on that file the COLD path decides its cubes by
**Fourier-Motzkin**, and the warm decider is not replacing a cold simplex with a
warm one -- it is replacing a different ENGINE.

That is a third term, and it is the biggest one on these rows.  ADR-2125 was
careful that the WARM side never answers from Fourier-Motzkin (a theory with no
warm tableau refuses rather than falling back, so an A/B of the lever is not an
A/B of two engines).  Nothing made the COLD side stop using it, and nothing had
to -- but it means a saving measured against that cold side is partly an engine
swap, and a reader told "the basis is worth 4 % of the clock" would draw the
wrong conclusion from it.

So the decomposition here is THREE terms plus a residual, and the residual is
printed rather than absorbed:

    linearization = off.cube_collect_ms  - arm.cube_collect_ms
    fourier       = off.cube_fm_ms       - arm.cube_fm_ms
    basis         = off.cube_simplex_ms  - arm.cube_simplex_ms
                                         - arm.warm_cube_solve_ms
                                         - arm.warm_cube_sync_ms
    residual      = (off.theory_ms - arm.theory_ms) - (the three above)

Every term is a difference between fields that are ON the trail line of one
interleaved pair of arms over one file.  No counterfactual, no model.

Usage: attribute.py <capture-dir> [<capture-dir>...]
"""

import re
import sys
from pathlib import Path

FIELDS = (
    "cube_collect_ms",
    "cube_fm_ms",
    "cube_simplex_ms",
    "warm_cube_solve_ms",
    "warm_cube_sync_ms",
    "warm_cube_build",
    "warm_cube_checks",
    "theory_ms",
    "lra_rounds",
    "cube_decisions",
    "blocking_clauses",
    "skeleton_ms",
)


def read_trail(path):
    """The `; lazy-smt` line's fields, or None when the file has no such line.

    None is NOT an empty reading: a capture with no trail line says nothing
    about this loop, and folding that into zeros would put rows in a denominator
    they have no business in.
    """
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    m = re.search(r"^; lazy-smt .*$", text, re.MULTILINE)
    if not m:
        return None
    out = {}
    for tok in m.group(0).split():
        k, _, v = tok.partition("=")
        if k in FIELDS:
            out[k] = v
    return out


def num(d, k):
    try:
        return int(d.get(k, ""))
    except (TypeError, ValueError):
        return None


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    arms = {"b": "on", "c": "screened"}
    totals = {a: dict(lin=0, fm=0, basis=0, resid=0, delta=0, rows=0) for a in arms}
    per_row = []
    for d in sys.argv[1:]:
        for a_path in sorted(Path(d).glob("*.a.out")):
            stem = a_path.name[: -len(".a.out")]
            a = read_trail(a_path)
            if a is None:
                continue
            for arm, name in arms.items():
                t = read_trail(a_path.with_name(f"{stem}.{arm}.out"))
                if t is None or t.get("warm_cube_build") != "built":
                    continue
                vals = {}
                ok = True
                for key, src in (
                    ("a_col", (a, "cube_collect_ms")),
                    ("a_fm", (a, "cube_fm_ms")),
                    ("a_sx", (a, "cube_simplex_ms")),
                    ("a_th", (a, "theory_ms")),
                    ("t_col", (t, "cube_collect_ms")),
                    ("t_fm", (t, "cube_fm_ms")),
                    ("t_sx", (t, "cube_simplex_ms")),
                    ("t_th", (t, "theory_ms")),
                    ("t_sv", (t, "warm_cube_solve_ms")),
                    ("t_sy", (t, "warm_cube_sync_ms")),
                ):
                    v = num(*src)
                    if v is None:
                        ok = False
                        break
                    vals[key] = v
                if not ok:
                    continue
                lin = vals["a_col"] - vals["t_col"]
                fm = vals["a_fm"] - vals["t_fm"]
                basis = vals["a_sx"] - vals["t_sx"] - vals["t_sv"] - vals["t_sy"]
                delta = vals["a_th"] - vals["t_th"]
                resid = delta - (lin + fm + basis)
                tt = totals[arm]
                tt["lin"] += lin
                tt["fm"] += fm
                tt["basis"] += basis
                tt["resid"] += resid
                tt["delta"] += delta
                tt["rows"] += 1
                per_row.append((name, delta, lin, fm, basis, resid, stem))

    print("PER-ROW, the ten largest theory-layer savings (ms)")
    print(f"{'arm':<10}{'Δtheory':>9}{'lineariz':>9}{'fourier':>9}{'basis':>9}{'residual':>10}  file")
    for r in sorted(per_row, key=lambda r: -r[1])[:10]:
        name, delta, lin, fm, basis, resid, stem = r
        print(f"{name:<10}{delta:>9}{lin:>9}{fm:>9}{basis:>9}{resid:>10}  {stem[:52]}")

    print("\nPOOLED over every row where the decider was BUILT and both arms have a trail")
    for arm, name in arms.items():
        t = totals[arm]
        if not t["rows"]:
            print(f"  {name}: no such row")
            continue
        d = t["delta"]

        def share(v):
            return f"{v * 100.0 / d:6.1f} %" if d else "    -- "

        print(
            f"  {name}: {t['rows']} rows, theory-layer saving {d} ms\n"
            f"      linearization {t['lin']:>9} ms {share(t['lin'])}\n"
            f"      FOURIER-MOTZKIN {t['fm']:>7} ms {share(t['fm'])}\n"
            f"      basis         {t['basis']:>9} ms {share(t['basis'])}\n"
            f"      residual      {t['resid']:>9} ms {share(t['resid'])}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
