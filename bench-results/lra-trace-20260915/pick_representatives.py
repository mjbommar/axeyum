#!/usr/bin/env python3
"""Pick ONE representative row per sub-bucket, deterministically.

"Representative" is a claim, so the rule is written down rather than chosen by
eye: within a sub-bucket (channel, bucket, the first clause of the prose) take
the row whose `file` sorts first. That is reproducible from the committed table
by anyone, it does not depend on shard order or on which host ran the row, and
it cannot be quietly re-picked later to suit a conclusion.

It is NOT a random sample and does not claim to be: with sub-buckets of 1-21
rows a "typical" row is not a defined object, and the point of these files is to
carry a side-by-side trace, not to estimate a population mean. Every population
number in the ADR comes from all 93 rows, never from these.

Usage:  pick_representatives.py <buckets.tsv>
"""

from __future__ import annotations

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        sys.stderr.write(__doc__ or "")
        return 2
    lines = Path(argv[1]).read_text().splitlines()
    head = lines[0].split("\t")
    rows = [dict(zip(head, ln.split("\t"), strict=True)) for ln in lines[1:] if ln]
    groups: dict[tuple[str, str, str], list[dict[str, str]]] = {}
    for r in rows:
        prose = r["detail"].split(";")[0].split("(")[0].strip()[:60]
        # An allocation failure names the SIZE of the request that tipped the
        # process over, which is a different number on every row. Grouping on it
        # would make 40 aborts into 40 sub-buckets of one, which is not a
        # classification -- it is the size histogram wearing a bucket's name.
        # The size is reported separately, by `bucket_summary.py`.
        if prose.startswith("memory allocation of"):
            prose = "memory allocation of <n> bytes failed"
        key = (r["channel"], r["bucket"], prose)
        groups.setdefault(key, []).append(r)
    print("n\tchannel\tbucket\tprose\tfile")
    for key in sorted(groups):
        members = sorted(groups[key], key=lambda r: r["file"])
        print(f"{len(members)}\t{key[0]}\t{key[1]}\t{key[2]}\t{members[0]['file']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
