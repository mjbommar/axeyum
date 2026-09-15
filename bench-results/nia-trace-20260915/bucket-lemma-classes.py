#!/usr/bin/env python3
"""Bucket the 78 z3-decided QF_NIA files by which machinery produced conflicts.

ADR-2112, and the reason it is written as a CROSS-TAB rather than a ranking:
a file lights several counters, so "which class decided it" has no single
answer from `-st`. What the counters DO support is "which machinery produced a
conflict here", and the partition that matters downstream -- whether `nlsat`
was needed at all -- is a clean yes/no per file.

A MEASUREMENT BOUNDARY, stated because it bounds every conclusion drawn from
this table: z3 pools basics, order, monotonicity and tangent lemmas into ONE
counter, `arith-nla-lemmas` (`src/math/lp/lp_settings.h:127`). A release z3
cannot separate them; only a TRACE build can. So this table can say the lemma
layer fired and cannot say which lemma family did -- and no claim here rests on
attributing a file to `order` rather than `tangent`.

usage: bucket-lemma-classes.py <z3-stats.tsv> [<z3-trace.tsv>]
"""

import collections
import statistics
import sys


def load_stats(path: str) -> dict[str, dict[str, float]]:
    per_file: dict[str, dict[str, float]] = collections.defaultdict(dict)
    with open(path) as handle:
        next(handle, None)
        for line in handle:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 3:
                continue
            name, key, value = parts
            if key == "__verdict__":
                per_file[name]["__verdict__"] = value  # type: ignore[assignment]
                continue
            try:
                per_file[name][key] = float(value)
            except ValueError:
                continue
    return per_file


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    stats = load_stats(argv[1])
    if not stats:
        print("no rows: an empty capture is not a result", file=sys.stderr)
        return 1

    times: dict[str, int] = {}
    if len(argv) > 2:
        with open(argv[2]) as handle:
            next(handle, None)
            for line in handle:
                f = line.rstrip("\n").split("\t")
                if len(f) > 4 and f[1] == "qfnia" and f[3].isdigit():
                    times[f[0]] = int(f[3])

    decided = {
        name: s for name, s in stats.items() if s.get("__verdict__") in {"sat", "unsat"}
    }
    print(f"files captured {len(stats)}   of those DECIDED by `qfnia` {len(decided)}")
    other = len(stats) - len(decided)
    if other:
        kinds = collections.Counter(
            s.get("__verdict__") for s in stats.values()
            if s.get("__verdict__") not in {"sat", "unsat"}
        )
        print(f"  not decided in THIS run: {other}  {dict(kinds)}")
        print("  (the population was chosen from a prior sweep; a file that")
        print("   decided there and not here is ambient, and is kept visible)")

    def fired(s: dict[str, float], key: str) -> bool:
        return s.get(key, 0.0) > 0.0

    classes = [
        ("grobner", "arith-grobner-conflicts", "nla_grobner.cpp"),
        ("horner", "arith-horner-conflicts", "horner.cpp"),
        ("nlsat", "nlsat-conflicts", "src/nlsat/"),
        ("nla-lemmas (POOLED)", "arith-nla-lemmas", "basics+order+monotone+tangent"),
        ("monomial-bounds", "arith-nla-add-bounds", "nla_intervals.cpp"),
        ("int-branch", "arith-branch", "int branch-and-bound"),
        ("int-gomory", "arith-gomory-cuts", "gomory cuts"),
        ("int-cube", "arith-cube-calls", "cube/HNF"),
    ]

    print("\n=== how many of the decided files had each machinery CONFLICT/FIRE ===")
    for label, key, where in classes:
        hit = [n for n, s in decided.items() if fired(s, key)]
        pct = 100.0 * len(hit) / len(decided) if decided else 0.0
        med = (
            f"{statistics.median([times[n] for n in hit if n in times]):.0f} ms"
            if [n for n in hit if n in times]
            else "n/a"
        )
        print(f"  {label:<22} {len(hit):>3} of {len(decided)} ({pct:5.1f} %)  "
              f"z3 median {med:>9}   [{where}]")

    print("\n=== THE PARTITION THAT MATTERS: is `nlsat` needed? ===")
    with_nlsat = {n for n, s in decided.items() if fired(s, "nlsat-conflicts")}
    without = set(decided) - with_nlsat
    for label, group in (("nlsat DID conflict", with_nlsat), ("nlsat did NOT", without)):
        med = (
            f"{statistics.median([times[n] for n in group if n in times]):.0f} ms"
            if [n for n in group if n in times]
            else "n/a"
        )
        print(f"  {label:<22} {len(group):>3} of {len(decided)}   z3 median {med}")
    print("  -> the second group is decided by the LEMMA layer plus linear")
    print("     arithmetic alone, which is the part this ADR is about;")
    print("     the first is lane NRA-TRACE's (ADR-2110) subject.")

    print("\n=== among the files nlsat did NOT need, what fired ===")
    tally: collections.Counter[str] = collections.Counter()
    for name in without:
        s = decided[name]
        lit = [label for label, key, _ in classes if fired(s, key) and label != "nlsat"]
        tally["+".join(lit) if lit else "(nothing: simplification / linear only)"] += 1
    for combo, count in tally.most_common():
        print(f"  {count:>3}  {combo}")

    print("\n=== among the files nlsat DID conflict on, did anything else too ===")
    tally2: collections.Counter[str] = collections.Counter()
    for name in with_nlsat:
        s = decided[name]
        lit = [label for label, key, _ in classes if fired(s, key) and label != "nlsat"]
        tally2["+".join(lit) if lit else "(nlsat alone)"] += 1
    for combo, count in tally2.most_common():
        print(f"  {count:>3}  {combo}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
