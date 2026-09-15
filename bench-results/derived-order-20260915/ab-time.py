#!/usr/bin/env python3
"""The TIME column ADR-2106 is actually about.

`bench-results/route-ownership-20260915/ab-summarize.py` is the verdict/exit-
status/`:status`/malformed summary and is reused unchanged -- four channels,
each reported separately, with the exit criterion as an exit status. It does
not report clock, because ADR-2100 was a correctness change.

ADR-2106 is a TIME change: the sizing found a ceiling of 3 files of 115 and a
reorderable prefix of 628,792 ms over 65 files. So the number that says whether
the derived order did what it was derived to do is wall clock on the rows BOTH
arms decide -- a row only one arm decides has no comparable clock, and a row
neither decides is two budget expiries and says nothing about routing.

Reported separately from the verdict table on purpose. A time saving does not
license a loss, and a combined score would let one pay for the other.

Usage: ab-time.py <tsv>...
"""

from __future__ import annotations

import statistics
import sys
from collections import defaultdict

DECIDED = {"sat", "unsat"}


def main() -> int:
    rows = defaultdict(list)
    for path in sys.argv[1:]:
        for line in open(path, encoding="utf-8"):
            cells = line.rstrip("\n").split("\t")
            if cells[0] == "file" or len(cells) != 9:
                continue
            rows[cells[0].split("/", 1)[0]].append(cells)

    print(
        f"{'division':<12} {'both':>5} {'A total s':>10} {'B total s':>10} "
        f"{'saved s':>9} {'A med ms':>9} {'B med ms':>9} {'B faster':>9} {'B slower':>9}"
    )
    any_saving = False
    detail = []
    for div in sorted(rows):
        a_ms, b_ms, faster, slower = [], [], 0, 0
        for path, a, am, _arc, b, bm, _brc, _first, _status in rows[div]:
            if a not in DECIDED or b not in DECIDED:
                continue
            am_i, bm_i = int(am), int(bm)
            a_ms.append(am_i)
            b_ms.append(bm_i)
            # A 200 ms band, so ordinary run-to-run jitter is not counted as a
            # direction. The claim here is about seconds, not milliseconds.
            if bm_i < am_i - 200:
                faster += 1
                detail.append((am_i - bm_i, div, path, am_i, bm_i))
            elif bm_i > am_i + 200:
                slower += 1
                detail.append((am_i - bm_i, div, path, am_i, bm_i))
        if not a_ms:
            print(f"{div:<12} {0:>5}   (no row decided by BOTH arms)")
            continue
        saved = (sum(a_ms) - sum(b_ms)) / 1000.0
        if saved > 0:
            any_saving = True
        print(
            f"{div:<12} {len(a_ms):>5} {sum(a_ms) / 1000.0:>10.1f} "
            f"{sum(b_ms) / 1000.0:>10.1f} {saved:>+9.1f} "
            f"{statistics.median(a_ms):>9.0f} {statistics.median(b_ms):>9.0f} "
            f"{faster:>9} {slower:>9}"
        )

    detail.sort(key=lambda t: -abs(t[0]))
    print("\nlargest per-file clock differences on rows BOTH arms decide "
          "(positive = B faster):")
    for delta, div, path, am, bm in detail[:20]:
        print(f"  {delta:>+8} ms  {div:<10} A={am:>6} B={bm:>6}  {path}")

    # Exit status depends on the finding: a reorder that was derived to save
    # time and saves none on every division is a null result, and must not
    # print like a success.
    return 0 if any_saving else 3


if __name__ == "__main__":
    raise SystemExit(main())
