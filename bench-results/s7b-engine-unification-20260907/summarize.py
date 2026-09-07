#!/usr/bin/env python3
"""Summarise an S7b before/after TSV: decided counts, PAR-2, and every
verdict that moved. Exit status depends on the finding: a verdict that
contradicts the file's declared `:status`, or a file decided before and
undecided after, is a nonzero exit."""
import sys

BUDGET_MS = 24000


def main(path):
    rows = []
    with open(path) as handle:
        header = handle.readline()
        for line in handle:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 6:
                continue
            rows.append(parts)
    decided = {"before": 0, "after": 0}
    par2 = {"before": 0, "after": 0}
    contradictions = []
    lost = []
    gained = []
    for f, declared, bv, bms, av, ams in rows:
        for arm, verdict, ms in (("before", bv, bms), ("after", av, ams)):
            ms = int(ms)
            if verdict in ("sat", "unsat"):
                decided[arm] += 1
                par2[arm] += min(ms, BUDGET_MS)
                if declared in ("sat", "unsat") and verdict != declared:
                    contradictions.append((f, arm, verdict, declared))
            else:
                par2[arm] += 2 * BUDGET_MS
        if bv in ("sat", "unsat") and av not in ("sat", "unsat"):
            lost.append(f)
        if av in ("sat", "unsat") and bv not in ("sat", "unsat"):
            gained.append(f)
    print(f"{path}: {len(rows)} files")
    print(f"  decided  before={decided['before']}  after={decided['after']}")
    print(f"  PAR-2    before={par2['before']}  after={par2['after']}"
          f"  ({100.0 * (par2['after'] - par2['before']) / max(par2['before'], 1):+.1f}%)")
    print(f"  gained ({len(gained)}): " + ", ".join(x.split('/')[-1] for x in gained))
    print(f"  lost   ({len(lost)}): " + ", ".join(x.split('/')[-1] for x in lost))
    for f, arm, verdict, declared in contradictions:
        print(f"  CONTRADICTION {arm} {verdict} != declared {declared}: {f}")
    return 1 if (contradictions or lost) else 0


if __name__ == "__main__":
    status = 0
    for path in sys.argv[1:]:
        status |= main(path)
    sys.exit(status)
