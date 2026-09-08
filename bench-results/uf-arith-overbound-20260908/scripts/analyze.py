#!/usr/bin/env python3
"""Summarize a lane sweep TSV: verdicts, who consumed the budget, and whether
anything ran after the over-bound UF+arithmetic decision point.

Usage: analyze.py <sweep.tsv> [more.tsv ...]
Each argument is summarized on its own, then any two are compared per file.
"""

import collections
import json
import re
import sys

OVERBOUND = "uf-arith-lazy-overbound"


def load(path):
    rows = {}
    meta = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("#"):
                meta.append(line.rstrip("\n"))
                continue
            break  # the column header
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 5:
                continue
            f, wall, verdict, route, trail = parts[0], parts[1], parts[2], parts[3], parts[4]
            bound = re.search(r"bound_by=(\S+)", route)
            decided = re.search(r"decided_by=(\S+)", route)
            bound_ms = re.search(r"bound_ms=(\d+)", route)
            attempts = []
            m = re.match(r"; route-trail (.*)$", trail)
            if m:
                try:
                    attempts = [a["route"] for a in json.loads(m.group(1))["attempts"]]
                except (ValueError, KeyError):
                    attempts = []
            after = None
            if OVERBOUND in attempts:
                i = attempts.index(OVERBOUND)
                # `fd:*` are the FRONT DOOR's own post-dispatch string/bounded
                # routes, recorded on every file after `check_auto` returns. They
                # are not the UF ladder, and counting them makes every file look
                # like the ladder ran. Only a non-`fd:` route after the decision
                # point means dispatch continued.
                after = [r for r in attempts[i + 1:] if not r.startswith("fd:")]
            rows[f] = {
                "wall": int(wall) if wall.isdigit() else -1,
                "verdict": verdict,
                "bound_by": bound.group(1) if bound else "",
                "decided_by": decided.group(1) if decided else "",
                "bound_ms": int(bound_ms.group(1)) if bound_ms else 0,
                "attempts": attempts,
                "after_overbound": after,
            }
    return rows, meta


def summarize(path, rows, meta):
    print(f"\n=== {path}: {len(rows)} files ===")
    for m in meta:
        print(" ", m)
    verdicts = collections.Counter(r["verdict"] for r in rows.values())
    print("verdicts:", dict(verdicts))
    bound = collections.Counter(r["bound_by"] for r in rows.values())
    print("bound_by:")
    for k, v in bound.most_common():
        print(f"  {v:4d}  {k}")
    engaged = [f for f, r in rows.items() if r["after_overbound"] is not None]
    print(f"reached the over-bound decision point: {len(engaged)}")
    swallowed = [f for f in engaged if not rows[f]["after_overbound"]]
    print(f"  ...and NOTHING ran after it: {len(swallowed)}")
    fell = [f for f in engaged if rows[f]["after_overbound"]]
    print(f"  ...and the ladder below ran:    {len(fell)}")
    if fell:
        nxt = collections.Counter(rows[f]["after_overbound"][0] for f in fell)
        print("  first route after it:", dict(nxt))
    ob_bound = [f for f, r in rows.items() if r["bound_by"] == OVERBOUND]
    print(f"budget consumed BY the over-bound CEGAR on: {len(ob_bound)} files")
    if ob_bound:
        share = [
            100.0 * rows[f]["bound_ms"] / rows[f]["wall"] for f in ob_bound if rows[f]["wall"] > 0
        ]
        share.sort()
        print(
            f"  its share of wall clock: min {share[0]:.1f}% "
            f"median {share[len(share) // 2]:.1f}% max {share[-1]:.1f}%"
        )


def compare(pa, ra, pb, rb):
    common = sorted(set(ra) & set(rb))
    print(f"\n=== {pa} -> {pb}: {len(common)} files in common ===")
    gained = [f for f in common if ra[f]["verdict"] == "unknown" and rb[f]["verdict"] != "unknown"]
    lost = [f for f in common if ra[f]["verdict"] != "unknown" and rb[f]["verdict"] == "unknown"]
    flipped = [
        f
        for f in common
        if ra[f]["verdict"] in ("sat", "unsat")
        and rb[f]["verdict"] in ("sat", "unsat")
        and ra[f]["verdict"] != rb[f]["verdict"]
    ]
    print(f"decided in B but not A (GAINED): {len(gained)}")
    for f in gained:
        print(f"  + {rb[f]['verdict']:5s} {rb[f]['decided_by']:28s} {f.split('/')[-1]}")
    print(f"decided in A but not B (LOST):   {len(lost)}")
    for f in lost:
        print(f"  - {ra[f]['verdict']:5s} {ra[f]['decided_by']:28s} {f.split('/')[-1]}")
    print(f"DISAGREEMENTS (sat vs unsat):    {len(flipped)}")
    for f in flipped:
        print(f"  ! {ra[f]['verdict']} -> {rb[f]['verdict']}  {f}")
    return len(flipped)


def main():
    loaded = []
    for p in sys.argv[1:]:
        rows, meta = load(p)
        loaded.append((p, rows, meta))
    digests = {}
    for path, _rows, meta in loaded:
        summarize(path, _rows, meta)
        for m in meta:
            if m.startswith("# binary "):
                digests.setdefault(m.split()[-1], []).append(path)
    if len(loaded) > 1 and len(digests) == 1:
        # Two arms that ran the same binary bytes are only a valid A/B if the
        # policy differed; say so rather than letting a copy-paste pass as a
        # comparison.
        print("\nNOTE: every arm ran the SAME binary digest — check the policy lines.")
    disagreements = 0
    for i in range(len(loaded) - 1):
        disagreements += compare(loaded[i][0], loaded[i][1], loaded[i + 1][0], loaded[i + 1][1])
    # A disagreement voids the comparison, so make the exit status say so.
    return 1 if disagreements else 0


if __name__ == "__main__":
    sys.exit(main())
