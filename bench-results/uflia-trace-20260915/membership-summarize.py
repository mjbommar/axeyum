#!/usr/bin/env python3
"""UFLIA-TRACE -- aggregate `membership-run.sh`'s per-core blocks.

    membership-summarize.py <membership.log>

Prints the three buckets at their shared denominator, the cores that produced no
dump (which are NOT zeros and are counted separately), and a sample of the
ABSENT terms, because a bucket sized by its label says nothing about what is in
it.
"""

from __future__ import annotations

import re
import sys

ROW = re.compile(r"^\s+(PRESENT|ABSENT|NOT-GROUND)\s+(\d+)")


def main() -> None:
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)

    files = nodump = 0
    counts = {"PRESENT": 0, "ABSENT": 0, "NOT-GROUND": 0}
    per_core: list[tuple[str, int, int, int]] = []
    absent_terms: list[str] = []
    cur = ""
    cur_counts = {"PRESENT": 0, "ABSENT": 0, "NOT-GROUND": 0}

    def flush() -> None:
        if cur and any(cur_counts.values()):
            per_core.append(
                (cur, cur_counts["PRESENT"], cur_counts["ABSENT"], cur_counts["NOT-GROUND"])
            )

    with open(sys.argv[1], encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if line.startswith("===="):
                flush()
                cur = line.strip()[5:]
                cur_counts = {"PRESENT": 0, "ABSENT": 0, "NOT-GROUND": 0}
                files += 1
                continue
            if "NO-GROUND-DUMP" in line:
                nodump += 1
                continue
            if "ABSENT-TERM" in line:
                absent_terms.append(line.strip()[12:][:100])
                continue
            m = ROW.match(line)
            if m:
                counts[m.group(1)] += int(m.group(2))
                cur_counts[m.group(1)] += int(m.group(2))
    flush()

    total = sum(counts.values())
    print(f"cores {files}  cores with no dump {nodump}  instance arguments {total}")
    if not total:
        print("  NOTHING MEASURED -- not a finding about presence either way")
        return
    for k in ("PRESENT", "ABSENT", "NOT-GROUND"):
        print(f"  {k:11s} {counts[k]:5d}  {100 * counts[k] / total:5.1f}%")
    print("\nper core (present / absent / not-ground):")
    for name, p, a, n in per_core:
        print(f"  {name[:66]:66s} {p:5d} {a:4d} {n:4d}")
    if absent_terms:
        print("\nsample ABSENT terms -- a bucket's LABEL says nothing about what is in it:")
        for a in sorted(set(absent_terms))[:10]:
            print(f"    {a}")


if __name__ == "__main__":
    main()
