#!/usr/bin/env python3
"""UFLIA-TRACE -- merge the census shards and bucket them.

    census-collect.py <out.tsv> <shard.tsv>...

Writes the merged rows to `<out.tsv>` and prints the buckets to stdout.

One repair is applied on the way in, and it is named rather than done quietly.
The first census ran with a `probe-shape.py` that printed `0` for
`joined`/`starved`/`admitted` on a run whose per-universal probe block never
executed, while printing `NA` for `silent` from the same missing rows. Those
four are read out of ONE segment set, so they are missing together; a row with
`silent=NA` therefore has no measurement of the other three either and `0` there
is a strong negative the instrument never made. `silent == NA` rewrites all four
to `NA`. The shipped script now emits `NA` for all four directly, so this repair
is a no-op on anything measured after it.
"""

from __future__ import annotations

import collections
import sys

FIELDS = [
    "file", "verdict", "bound_by", "last", "attempts", "total_ms",
    "giveup_kind", "universals", "triggerless", "rounds", "joined",
    "starved", "admitted", "silent", "giveup_raw",
]


def main() -> None:
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    out_path, shards = sys.argv[1], sys.argv[2:]

    rows: list[dict[str, str]] = []
    for path in shards:
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                parts = line.rstrip("\n").split("\t")
                if not parts or parts[0] == "file":
                    continue
                if len(parts) != len(FIELDS):
                    print(f"SKIPPED malformed row in {path}: {len(parts)} fields",
                          file=sys.stderr)
                    continue
                row = dict(zip(FIELDS, parts))
                if row["silent"] == "NA":
                    for f in ("joined", "starved", "admitted"):
                        row[f] = "NA"
                rows.append(row)

    rows.sort(key=lambda r: r["file"])
    with open(out_path, "w", encoding="utf-8") as handle:
        handle.write("\t".join(FIELDS) + "\n")
        for row in rows:
            handle.write("\t".join(row[f] for f in FIELDS) + "\n")

    print(f"rows {len(rows)}")
    print("\n== verdict ==")
    for k, v in sorted(collections.Counter(r["verdict"] for r in rows).items()):
        print(f"{v:4d}  {k}")
    print("\n== terminal route (bound_by) x giveup kind ==")
    counter = collections.Counter(
        (r["bound_by"], r["giveup_kind"]) for r in rows
    )
    for (bb, gk), v in sorted(counter.items(), key=lambda kv: -kv[1]):
        print(f"{v:4d}  {bb:22s} {gk}")
    print("\n== give-up detail, VERBATIM and unbucketed ==")
    detail = collections.Counter(r["giveup_raw"][:96] for r in rows)
    for k, v in sorted(detail.items(), key=lambda kv: -kv[1]):
        print(f"{v:4d}  {k}")
    print("\n== e-matching shape, rows that printed a per-universal probe ==")
    shaped = [r for r in rows if r["silent"] != "NA"]
    print(f"shaped {len(shaped)} of {len(rows)}; the rest exited before the "
          "probe block and are NOT zeros")
    for r in sorted(shaped, key=lambda r: -int(r["universals"])):
        u = int(r["universals"])
        s = int(r["silent"])
        pct = f"{100 * s / u:.0f}%" if u else "n/a"
        print(f"  {r['file'][:70]:70s} u={u:4d} silent={s:4d} ({pct}) "
              f"tl={r['triggerless']:>4s} rounds={r['rounds']:>4s} "
              f"joined={r['joined']:>8s} admitted={r['admitted']:>6s}")


if __name__ == "__main__":
    main()
