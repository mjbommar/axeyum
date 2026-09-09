#!/usr/bin/env python3
"""Per-file reading of the `; lazy-smt` instrument from a trace-sweep directory.

Written 2026-09-08 for the nineteen `QF_LRA` files that exhaust 24 s inside the
OFFLINE lazy-SMT refinement loop. `scripts/trace-sweep-report.py` answers "which
route consumed the budget"; this answers the next question, "and what did that
route's rounds buy", which after the Farkas fix is the whole question on this
population.

Usage:

    scripts/lra-lazy-report.py <sweep-dir> [<sweep-dir> ...]

Every field is printed as it was read. `reading=` comes first for the same
reason the trace line prints it first: a zero from an instrument that never
armed is not a measurement, and `not-reached` / `entered-no-rounds` are
different statements from `measured`.
"""

import os
import re
import sys


def parse(directory):
    index = {}
    with open(os.path.join(directory, "index.tsv"), encoding="utf-8") as handle:
        for line in handle:
            parts = line.rstrip("\n").split("\t")
            if parts[0] == "index":
                continue
            index[parts[0]] = (os.path.basename(parts[1]), parts[2], parts[3])
    rows = []
    for key in sorted(index, key=int):
        path = os.path.join(directory, f"{key}.log")
        with open(path, encoding="utf-8", errors="replace") as handle:
            text = handle.read()
        match = re.search(r"^; lazy-smt .*$", text, re.M)
        fields = {}
        if match:
            for token in match.group(0).split()[2:]:
                if "=" in token:
                    name, value = token.split("=", 1)
                    fields[name] = value
        rows.append((key, index[key], fields))
    return rows


def number(fields, name):
    try:
        return int(fields.get(name, 0))
    except ValueError:
        return 0


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    for directory in argv[1:]:
        print(f"### {directory}")
        header = (
            f"{'#':>3} {'verdict':<8} {'wall':>6} {'file':<34} {'probe':<21} "
            f"{'rounds':>6} {'atoms':>6} {'width':>6} {'flips':>7} {'same':>5} "
            f"{'sk_ms':>6} {'th_ms':>6} {'fm_ms':>6} {'sx_ms':>6} {'decl':>5} "
            f"{'sx_n':>5} {'col_ms':>6} {'reading'}"
        )
        print(header)
        for key, (name, verdict, wall), fields in parse(directory):
            if not fields:
                print(f"{key:>3} {verdict:<8} {wall:>6} {name:<34} NO LAZY-SMT LINE")
                continue
            rounds = number(fields, "lra_rounds") + number(fields, "nra_rounds")
            entries = number(fields, "lra_entries") + number(fields, "nra_entries")
            clauses = number(fields, "blocking_clauses")
            literals = number(fields, "blocking_literals")
            width = literals / clauses if clauses else 0.0
            churn_rounds = max(rounds - entries, 0)
            flips = number(fields, "cube_flips")
            mean_flips = flips / churn_rounds if churn_rounds else 0.0
            print(
                f"{key:>3} {verdict:<8} {wall:>6} {name:<34} "
                f"{fields.get('online_probe', '?'):<21} "
                f"{rounds:>6} {number(fields, 'atoms'):>6} {width:>6.2f} "
                f"{mean_flips:>7.1f} {number(fields, 'cube_identical'):>5} "
                f"{number(fields, 'skeleton_ms'):>6} {number(fields, 'theory_ms'):>6} "
                f"{number(fields, 'cube_fm_ms'):>6} {number(fields, 'cube_simplex_ms'):>6} "
                f"{number(fields, 'cube_fm_declines'):>5} "
                f"{number(fields, 'cube_simplex_calls'):>5} "
                f"{number(fields, 'cube_collect_ms'):>6} {fields.get('reading', '?')}"
            )
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
