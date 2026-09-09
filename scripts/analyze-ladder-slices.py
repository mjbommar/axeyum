#!/usr/bin/env python3
"""Which routes spend a ladder's clock without deciding, from the span shards.

Reads the committed span-log shards produced by `scripts/span-log-sweep.sh` and
answers, per division and route: how often it decided, how much wall clock it
spent NOT deciding, what share of the per-file budget that is, and -- the column
that decides whether a budget reservation could buy anything at all -- on how
many of those non-deciding attempts a LATER route decided the file.

A route that never decides is not automatically wrong. It may be cheap
insurance, or it may refute on a population this sample does not contain. The
`recov` column separates "this route is starving one that would have decided"
from "nothing runs after it, and shortening it is pure loss".

Usage:
    scripts/analyze-ladder-slices.py [--spans DIR] [--budget-ms 24000]

The shards default to the gallery's data directory, which is where
`scripts/sync_spans.mjs` in the axeyum.com repository puts them. Any directory
of `<DIVISION>.json` files with the same schema works.

Measurement note: a route attempt's wall clock is a PREFIX SUM -- time is
attributed to the next route that records -- so a route that never returns
leaves its budget on whichever attempt is recorded next, or on no attempt at
all. Read a big `wasted` number as "the budget passed through here", not as
"this function ran that long".
"""

from __future__ import annotations

import argparse
import collections
import glob
import json
import os
import statistics
import sys

DEFAULT_SPANS = os.path.expanduser(
    "~/projects/personal/axeyum.com/public/data/spans"
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spans", default=DEFAULT_SPANS)
    parser.add_argument("--budget-ms", type=int, default=24000)
    parser.add_argument(
        "--min-wasted-ms",
        type=int,
        default=100,
        help="omit routes whose non-deciding time totals less than this",
    )
    args = parser.parse_args()

    budget_ns = args.budget_ms * 1_000_000
    shards = sorted(glob.glob(os.path.join(args.spans, "*.json")))
    if not shards:
        print(f"no span shards under {args.spans}", file=sys.stderr)
        return 2

    rows: dict[tuple[str, str], dict] = collections.defaultdict(
        lambda: {
            "n": 0,
            "decided": 0,
            "nodec_wall": 0,
            "nodec_shares": [],
            "big": 0,
            "recoverable": 0,
            "rec_wall": 0,
            "after": [],
        }
    )
    for shard in shards:
        with open(shard, encoding="utf-8") as handle:
            payload = json.load(handle)
        division = payload["division"]
        for run in payload["runs"]:
            attempts = [
                span
                for span in run["spans"]
                if span["span_kind"] == "route_attempt"
            ]
            for index, span in enumerate(attempts):
                row = rows[(division, span["route"])]
                wall = span["wall_ns"] or 0
                row["n"] += 1
                if span["outcome"] == "decided":
                    row["decided"] += 1
                    continue
                row["nodec_wall"] += wall
                row["nodec_shares"].append(wall / budget_ns)
                if wall / budget_ns > 0.10:
                    row["big"] += 1
                later = [
                    a for a in attempts[index + 1 :] if a["outcome"] == "decided"
                ]
                if later:
                    row["recoverable"] += 1
                    row["rec_wall"] += wall
                    row["after"].append(sum(a["wall_ns"] or 0 for a in later))

    header = (
        f"{'division':8s} {'route':26s} {'n':>3s} {'dec':>4s} {'wasted_s':>9s} "
        f"{'med%bud':>8s} {'max%bud':>8s} {'>10%bud':>7s} {'recov':>6s} "
        f"{'rec_s':>7s} {'after_ms':>9s}"
    )
    print(header)
    print("-" * len(header))
    for (division, route), row in sorted(
        rows.items(), key=lambda kv: -kv[1]["nodec_wall"]
    ):
        if row["nodec_wall"] < args.min_wasted_ms * 1_000_000:
            continue
        shares = sorted(row["nodec_shares"]) or [0.0]
        after = sorted(row["after"])
        after_ms = statistics.median(after) / 1e6 if after else 0.0
        print(
            f"{division:8s} {route:26s} {row['n']:3d} {row['decided']:4d} "
            f"{row['nodec_wall'] / 1e9:9.1f} "
            f"{100 * statistics.median(shares):8.1f} {100 * max(shares):8.1f} "
            f"{row['big']:7d} {row['recoverable']:6d} "
            f"{row['rec_wall'] / 1e9:7.1f} {after_ms:9.1f}"
        )
    print()
    print(
        "recov = non-deciding attempts on files a LATER route decided; "
        "after_ms = how long that later route took, median."
    )
    print(
        "A reservation is worth taking only where recov is nonzero AND rec_s "
        "is large: that is a route starving one that would have decided."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
