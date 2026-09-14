#!/usr/bin/env python3
"""Project an A/B TSV's BASE arm into the noise-run schema.

The A/B's base arm IS a base-arm reading of the division, taken on the same
binary, envelope and cores as `noise-run.sh`'s. Projecting it makes it the FIRST
of the three noise readings instead of throwing away a run and paying for a
fourth -- and projecting rather than re-deriving means the noise band is computed
over literally the same columns for all three.

One caveat, stated because it is the reason this is a separate script rather than
a line in the summariser: the A/B's base arm ran INTERLEAVED with a second arm on
the same core, and the two standalone runs did not. If anything, that makes the
A/B's base arm the NOISIER of the three, so a band computed with it included is
not an underestimate.

Usage: project-ab-base.py <ab.tsv> <out.tsv>
"""

import csv
import sys

FIELDS = ["file", "base", "base_ms", "base_rc", "status"]


def main(argv):
    if len(argv) != 3:
        print(__doc__)
        return 2
    rows = list(csv.DictReader(open(argv[1], encoding="utf-8"), delimiter="\t"))
    if not rows:
        print(f"ABORT: {argv[1]} has no rows")
        return 3
    with open(argv[2], "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row[field] for field in FIELDS})
    print(f"PROJECT-OK {len(rows)} rows -> {argv[2]}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
