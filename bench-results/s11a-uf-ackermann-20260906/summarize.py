#!/usr/bin/env python3
"""S11a before/after summary: decided counts, PAR-2, and per-file verdict deltas.

usage: summarize.py <before.tsv> <after.tsv> [timeout_ms] [declared.tsv]

`declared.tsv` is optional; when given it must be a census TSV with `file` and
`declared` columns, and any verdict contradicting `declared` is reported as P0.
PAR-2 is the standard scoring: wall for a decided file, 2*timeout otherwise.
"""

import csv
import sys

csv.field_size_limit(10**9)


def load(path):
    with open(path) as handle:
        return {r["file"]: r for r in csv.DictReader(handle, delimiter="\t")}


def par2(rows, timeout_ms):
    total = 0.0
    for r in rows.values():
        if r["verdict"] in ("sat", "unsat"):
            total += int(r["wall_ms"])
        else:
            total += 2 * timeout_ms
    return total / 1000.0


def main():
    before_path, after_path = sys.argv[1], sys.argv[2]
    timeout_ms = int(sys.argv[3]) if len(sys.argv) > 3 else 24000
    declared = {}
    if len(sys.argv) > 4:
        with open(sys.argv[4]) as handle:
            for r in csv.DictReader(handle, delimiter="\t"):
                declared[r["file"]] = r.get("declared", "")

    before, after = load(before_path), load(after_path)
    shared = [f for f in before if f in after]
    if len(shared) != len(before) or len(shared) != len(after):
        print(
            f"WARNING: before={len(before)} after={len(after)} shared={len(shared)}",
            file=sys.stderr,
        )

    def decided(rows):
        return sum(1 for f in shared if rows[f]["verdict"] in ("sat", "unsat"))

    print(f"files                 {len(shared)}")
    print(f"decided before        {decided(before)}")
    print(f"decided after         {decided(after)}")
    print(f"PAR-2 before (s)      {par2({f: before[f] for f in shared}, timeout_ms):.1f}")
    print(f"PAR-2 after  (s)      {par2({f: after[f] for f in shared}, timeout_ms):.1f}")

    gained, lost, changed = [], [], []
    for f in shared:
        b, a = before[f]["verdict"], after[f]["verdict"]
        if b == a:
            continue
        if b in ("sat", "unsat") and a in ("sat", "unsat"):
            changed.append((f, b, a))
        elif a in ("sat", "unsat"):
            gained.append((f, a))
        else:
            lost.append((f, b))

    print(f"\ngained ({len(gained)}):")
    for f, v in gained:
        print(f"  +{v:5s} {f.split('/')[-1]}")
    print(f"lost ({len(lost)}):")
    for f, v in lost:
        print(f"  -{v:5s} {f.split('/')[-1]}")
    print(f"verdict FLIPS ({len(changed)}):  <- any entry here is P0")
    for f, b, a in changed:
        print(f"  !{b}->{a} {f}")

    # P0: a verdict contradicting the declared status, in either arm.
    p0 = []
    for f in shared:
        want = declared.get(f, "")
        if want not in ("sat", "unsat"):
            continue
        for arm, rows in (("before", before), ("after", after)):
            got = rows[f]["verdict"]
            if got in ("sat", "unsat") and got != want:
                p0.append((arm, f, want, got))
    print(f"\nP0 verdicts contradicting `declared` ({len(p0)}):")
    for arm, f, want, got in p0:
        print(f"  {arm}: declared={want} got={got}  {f}")
    return 1 if (p0 or changed) else 0


if __name__ == "__main__":
    sys.exit(main())
