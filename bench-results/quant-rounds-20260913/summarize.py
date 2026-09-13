#!/usr/bin/env python3
"""Derive every number this lane quotes from the committed TSVs.

Nothing in the README is transcribed: run this and the tables come out.

  summarize.py exit     -- which loop exit fired, per division (the bracket)
  summarize.py sweep    -- the round-ceiling value sweep
  summarize.py control  -- does the route under test run on the control sets
  summarize.py shape    -- what the fixpoint looks like (the next lane's lever)
"""

import collections
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
OUT = HERE / "out"
ARMS = ["shipped", "1024", "2048", "4096"]


def rows(path: pathlib.Path) -> list[dict[str, str]]:
    lines = path.read_text().splitlines()
    if not lines:
        return []
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:] if ln.strip()]


def pct(n: int, d: int) -> str:
    return f"{100.0 * n / d:5.1f}%" if d else "    -"


def cmd_exit() -> int:
    """The sizing bracket: 177 blocked is not 177 reachable."""
    files = sorted(OUT.glob("exit-*.tsv"))
    if not files:
        print("no exit-*.tsv in out/", file=sys.stderr)
        return 2
    grand: collections.Counter[str] = collections.Counter()
    print(f"{'population':12s} {'n':>4s}  {'SHAPE':>6s} {'CLOCK':>6s} {'ROUND':>6s} "
          f"{'OTHER':>6s}  max_rounds_entered")
    for f in files:
        rs = rows(f)
        kinds = collections.Counter(r["exit_kind"] for r in rs)
        grand.update(kinds)
        seen = [int(r["rounds"]) for r in rs if r["rounds"].isdigit()]
        print(f"{f.stem.removeprefix('exit-'):12s} {len(rs):4d}  "
              f"{kinds['SHAPE']:6d} {kinds['CLOCK']:6d} {kinds['ROUND']:6d} "
              f"{kinds['OTHER'] + kinds['NOGIVEUP']:6d}  {max(seen) if seen else '-'}")
    total = sum(grand.values())
    print(f"{'TOTAL':12s} {total:4d}  "
          f"{grand['SHAPE']:6d} {grand['CLOCK']:6d} {grand['ROUND']:6d} "
          f"{grand['OTHER'] + grand['NOGIVEUP']:6d}")
    print()
    print(f"ROUND-bound rows: {grand['ROUND']} of {total} ({pct(grand['ROUND'], total)})")
    print("The round ceiling is 512.  A row is ROUND-bound only if it entered 512")
    print("rounds; every other row stopped for a reason no round lever addresses.")
    return 0


def cmd_sweep() -> int:
    """Does raising the ceiling decide anything, and what does it cost?"""
    files = sorted(OUT.glob("sweep-*.tsv"))
    if not files:
        print("no sweep-*.tsv in out/", file=sys.stderr)
        return 2
    for f in files:
        rs = rows(f)
        print(f"== {f.stem.removeprefix('sweep-')}  n={len(rs)}")
        base = "shipped"
        for arm in ARMS:
            dec = sum(1 for r in rs if r[f"{arm}_verdict"] in ("sat", "unsat"))
            gained = sum(
                1 for r in rs
                if r[f"{arm}_verdict"] in ("sat", "unsat")
                and r[f"{base}_verdict"] not in ("sat", "unsat")
            )
            lost = sum(
                1 for r in rs
                if r[f"{base}_verdict"] in ("sat", "unsat")
                and r[f"{arm}_verdict"] not in ("sat", "unsat")
            )
            ms = sorted(int(r[f"{arm}_ms"]) for r in rs)
            med = ms[len(ms) // 2] if ms else 0
            tot = sum(ms)
            print(f"   {arm:8s} decided={dec:4d}  gained={gained:3d} lost={lost:3d}  "
                  f"median_ms={med:6d}  total_s={tot / 1000:8.1f}")
        # A verdict that moves between arms without being a gain or a loss is a
        # DISAGREEMENT, and it would be the soundness-relevant finding here.
        bad = [
            r for r in rs
            if len({r[f"{a}_verdict"] for a in ARMS} - {"unknown", "none"}) > 1
        ]
        print(f"   conflicting decided verdicts across arms: {len(bad)}")
        for r in bad[:5]:
            print("     " + r["file"] + " " + " ".join(r[f"{a}_verdict"] for a in ARMS))
    return 0


def cmd_control() -> int:
    """Is the control vacuous?  ADR-1945's lane found half of its was."""
    files = sorted(OUT.glob("hit-*.tsv"))
    if not files:
        print("no hit-*.tsv in out/", file=sys.stderr)
        return 2
    print(f"{'division':12s} {'n':>4s}  {'q:egraph':>9s} {'e-matching':>11s}  "
          f"{'decided':>8s}   verdict mix")
    for f in files:
        rs = rows(f)
        eg = sum(1 for r in rs if r["egraph_rung"] == "yes")
        em = sum(1 for r in rs if r["emat_giveup"] == "yes")
        dec = sum(1 for r in rs if r["verdict"] in ("sat", "unsat"))
        mix = collections.Counter(r["verdict"] for r in rs)
        print(f"{f.stem.removeprefix('hit-'):12s} {len(rs):4d}  {eg:9d} {em:11d}  "
              f"{dec:8d}   " + " ".join(f"{k}={v}" for k, v in sorted(mix.items())))
    print()
    print("`q:egraph` counts files whose route trail ATTEMPTED the e-graph")
    print("instantiation refuter.  A division at 0 cannot detect any change to it.")
    return 0


def cmd_shape() -> int:
    """What the fixpoint looks like -- where the next lane's lever is."""
    files = sorted(OUT.glob("shape-*.tsv"))
    if not files:
        print("no shape-*.tsv in out/", file=sys.stderr)
        return 2
    for f in files:
        rs = rows(f)
        print(f"== {f.stem.removeprefix('shape-')}  n={len(rs)}")
        g = collections.Counter(r["ground"] for r in rs)
        print("   ground-set size at fixpoint: "
              + "  ".join(f"{k}:{v}" for k, v in sorted(g.items(), key=lambda kv: -kv[1])))
        empty = sum(1 for r in rs if r["ground"] == "0")
        print(f"   EMPTY e-graph (ground=0): {empty} of {len(rs)} ({pct(empty, len(rs))})")
        tl = sum(1 for r in rs if r["triggerless"].isdigit() and int(r["triggerless"]) > 0)
        print(f"   at least one TRIGGERLESS universal: {tl} of {len(rs)} ({pct(tl, len(rs))})")
    return 0


def cmd_cost() -> int:
    """What raising the ceiling COSTS on work we already decide.

    A round cap turns a slow `unknown` into a fast one; raising it runs the
    reverse.  ADR-1945 measured exactly that: 33 of 35 non-gainers became
    clock-bound and two files went from a 0.5 s verdict to a 25 s watchdog.
    So the number that matters here is LOST, not gained.
    """
    files = sorted(OUT.glob("cost-*.tsv"))
    if not files:
        print("no cost-*.tsv in out/", file=sys.stderr)
        return 2
    tot: collections.Counter[str] = collections.Counter()
    a_ms: list[int] = []
    b_ms: list[int] = []
    flagged: list[tuple[str, dict[str, str]]] = []
    n = 0
    decided = ("sat", "unsat")
    for f in files:
        for r in rows(f):
            n += 1
            a, b = r["a_verdict"], r["b_verdict"]
            if a in decided and b not in decided:
                tot["LOST"] += 1
                flagged.append(("LOST", r))
            elif a not in decided and b in decided:
                tot["GAINED"] += 1
                flagged.append(("GAINED", r))
            elif a in decided and b in decided and a != b:
                # A sat/unsat disagreement between arms would be the
                # soundness-relevant finding, so it is its own bucket and is
                # never folded into "both decided".
                tot["DISAGREE"] += 1
                flagged.append(("DISAGREE", r))
            elif a in decided:
                tot["same-decided"] += 1
            else:
                tot["same-undecided"] += 1
            a_ms.append(int(r["a_ms"]))
            b_ms.append(int(r["b_ms"]))
    print(f"cost control (already-decided rows), arm B = AXEYUM_QINST_ROUNDS=4096 (8x)")
    print(f"  rows                {n}")
    for k in ("same-decided", "same-undecided", "GAINED", "LOST", "DISAGREE"):
        print(f"  {k:18s}{tot[k]}")
    a_ms.sort()
    b_ms.sort()
    if a_ms:
        print(f"  median ms           shipped={a_ms[len(a_ms) // 2]}  8x={b_ms[len(b_ms) // 2]}")
        print(f"  total s             shipped={sum(a_ms) / 1000:.1f}  8x={sum(b_ms) / 1000:.1f}")
        print(f"  rows over 20 s      shipped={sum(1 for m in a_ms if m > 20000)}  "
              f"8x={sum(1 for m in b_ms if m > 20000)}")
    for kind, r in flagged[:20]:
        print(f"  {kind}: {r['file']} shipped={r['a_verdict']}/{r['a_ms']}ms "
              f"8x={r['b_verdict']}/{r['b_ms']}ms first={r['first']}")
    return 0


def cmd_roundprobe() -> int:
    """The unambiguous bracket: does the ROUND string appear ANYWHERE in a run?

    `exit`'s classification reads the FIRST give-up line, which several ladder
    rungs compete to write, so a `0` there is a weaker claim than it looks.
    This scans the whole trace.  The give-up-line count is the coverage
    control: a row with 0 give-up lines AND 0 round hits is UNMEASURED, not a
    negative.
    """
    files = sorted(OUT.glob("round-*.tsv"))
    if not files:
        print("no round-*.tsv in out/", file=sys.stderr)
        return 2
    n = rnd = fix = head = unmeasured = 0
    for f in files:
        rs = rows(f)
        n += len(rs)
        for r in rs:
            g = int(r["giveup_lines"])
            hit = int(r["round_anywhere"])
            rnd += 1 if hit else 0
            fix += 1 if int(r["fixpoint_anywhere"]) else 0
            head += 1 if int(r["headroom_anywhere"]) else 0
            if g == 0 and hit == 0:
                unmeasured += 1
        print(f"  {f.stem.removeprefix('round-'):10s} n={len(rs)}")
    print()
    print(f"rows                                {n}")
    print(f"  round budget string ANYWHERE      {rnd}   <- the bracket")
    print(f"  fixpoint string anywhere          {fix}")
    print(f"  growth-headroom string anywhere   {head}")
    print(f"  UNMEASURED (no give-up line)      {unmeasured}")
    if unmeasured:
        print("  a row with no give-up line at all is not a negative; it is a row")
        print("  this instrument did not see.")
    return 0


def cmd_recheck() -> int:
    """Independent re-runs of every row that did not come back SHAPE."""
    files = sorted(OUT.glob("recheck-*.tsv"))
    if not files:
        print("no recheck-*.tsv in out/", file=sys.stderr)
        return 2
    for f in files:
        rs = rows(f)
        kinds = collections.Counter(r["exit_kind"] for r in rs)
        print(f"  {f.stem:12s} n={len(rs)}  "
              + "  ".join(f"{k}={v}" for k, v in sorted(kinds.items())))
    total_round = sum(
        1 for f in files for r in rows(f) if r["exit_kind"] == "ROUND"
    )
    solves = sum(len(rows(f)) for f in files)
    print()
    print(f"ROUND across {solves} re-run solves: {total_round}")
    return 0


COMMANDS = {
    "exit": cmd_exit,
    "roundprobe": cmd_roundprobe,
    "recheck": cmd_recheck,
    "sweep": cmd_sweep,
    "control": cmd_control,
    "shape": cmd_shape,
    "cost": cmd_cost,
}

if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in COMMANDS:
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    raise SystemExit(COMMANDS[sys.argv[1]]())
