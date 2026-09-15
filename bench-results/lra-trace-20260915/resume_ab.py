#!/usr/bin/env python3
"""Resume an interrupted `ab-run.sh` shard: drop a torn row, emit what is left.

A shard of this A/B was killed mid-write and left its last line TRUNCATED --
`...\tun` where a verdict belongs. Two things follow and both are the point of
this script:

  * a torn row must be DELETED, not parsed. `ab-summarize.py` already counts
    malformed rows separately and refuses to score them as unchanged (reading a
    parse failure as "no movement" is how a measurement manufactures a null),
    but a torn row that happens to have the right field count would score, so it
    is removed at the source instead of trusted to be caught downstream.
  * the resume list must be derived from what the TSV actually holds, not from
    a row count. The shard writes one row per file in list order, but a
    count-based resume assumes that and cannot notice a file that was skipped as
    unreadable.

It rewrites the TSV in place (keeping only complete rows) and prints the
remaining absolute paths, in the original list's order, to stdout.

# READ THIS BEFORE USING IT: confirm the shard is actually dead

This script was written because a shard *looked* dead -- its row count had moved
by two in forty minutes and `ps -eo pid,etime,cmd | grep '[a]b-run.sh' | head -4`
showed only the OTHER shard. It was not dead. `head -4` had cut the listing
short, and reading that absence as death produced a SECOND writer pinned to the
same physical core pair as the first, which is the one thing a pinned A/B must
never have: two arms' worth of work on one pair makes every timing in it a
measurement of the contention. Both were caught and the duplicate was killed by
PID (never by pattern -- a `pkill -f` here matches the killer's own command
line), and the resumed output was discarded.

So before resuming ANY shard:

    ps -eo pid,cmd | grep -o 'ab-run.sh ab[0-9a-z]*' | sort | uniq -c

which enumerates every shard and cannot be truncated into a false negative, and
confirm the one you mean to resume is absent. "I did not see it" is not "it is
not there" -- and this script rewriting the TSV while a live process holds it
open is exactly the situation where that distinction costs the run.

Usage:  resume_ab.py <ab.NN.tsv> <ab.NN.txt> > remaining.txt
"""

from __future__ import annotations

import sys
from pathlib import Path

COLUMNS = 9
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write(__doc__ or "")
        return 2
    tsv, listing = Path(argv[1]), Path(argv[2])
    lines = tsv.read_text().splitlines()
    header, body = lines[0], lines[1:]
    kept, torn = [], []
    for ln in body:
        if not ln:
            continue
        if len(ln.split("\t")) == COLUMNS:
            kept.append(ln)
        else:
            torn.append(ln)
    tsv.write_text("\n".join([header, *kept]) + "\n")
    done = {ln.split("\t")[0] for ln in kept}
    remaining = []
    for ln in listing.read_text().splitlines():
        if not ln:
            continue
        rel = ln[len(CORPUS) :] if ln.startswith(CORPUS) else ln
        if rel not in done:
            remaining.append(ln)
    for r in remaining:
        print(r)
    sys.stderr.write(
        f"resume_ab: kept {len(kept)} complete rows, DROPPED {len(torn)} torn, "
        f"{len(remaining)} files remain\n"
    )
    for t in torn:
        sys.stderr.write(f"  TORN\t{t[:110]}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
