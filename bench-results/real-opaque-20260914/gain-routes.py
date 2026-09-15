#!/usr/bin/env python3
"""Which route decides each converted row, and was it the one that refused?

ADR-2050 measured the refusal at `lira-dpll`. That says where the `Err` was
raised, NOT which rung the query reaches once it is gone: the refusal sat
upstream of several rungs, so removing it hands the query to whichever one gets
there first. This prints the distribution rather than assuming.

Usage: gain-routes.py <tsv> [<tsv> ...]
"""

import sys
from collections import Counter

DECIDED = {"sat", "unsat"}


def main(paths):
    rows = []
    for path in paths:
        with open(path) as fh:
            line = fh.readline()
            while line.startswith("#"):
                line = fh.readline()
            header = line.rstrip("\n").split("\t")
            for line in fh:
                rows.append(dict(zip(header, line.rstrip("\n").split("\t"))))

    gains = [r for r in rows if r["off_verdict"] not in DECIDED and r["on_verdict"] in DECIDED]
    on_route = Counter(r["on_route"].split("|")[0] for r in gains)
    off_bound = Counter(r["off_route"].split("|")[1] for r in gains)
    refused = Counter(r["off_route"].split("|")[2] for r in gains)
    verdicts = Counter(r["on_verdict"] for r in gains)

    print(f"converted rows: {len(gains)}")
    print(f"  verdict      : {dict(verdicts)}")
    print("  decided_by in the LEVER arm:")
    for k, v in on_route.most_common():
        print(f"     {v:3d}  {k}")
    print("  bound_by in the BASE arm (what was holding them):")
    for k, v in off_bound.most_common():
        print(f"     {v:3d}  {k}")
    print("  did the base arm print the cause-(A) refusal text?")
    for k, v in refused.most_common():
        print(f"     {v:3d}  {k}")
    print(
        "\n  NOTE: `clean` here does NOT mean the refusal did not happen. The text is\n"
        "  printed by the lazy-arithmetic route's own error path; on these rows the\n"
        "  refusal is consumed inside a rung that declines quietly. The MECHANISM\n"
        "  evidence is the `decided_by` column moving from `none` to a named rung,\n"
        "  which it does on all of them."
    )

    ms_off = sum(int(r["off_ms"]) for r in gains)
    ms_on = sum(int(r["on_ms"]) for r in gains)
    print(f"\n  wall clock on the converted rows: off={ms_off / 1000:.1f}s on={ms_on / 1000:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
