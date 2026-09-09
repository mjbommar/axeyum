#!/usr/bin/env python3
"""Join two (or three) `euf-online-atoms-sweep.sh` arms and print the delta.

    exit 0  the arms were compared
    exit 1  a file is DECIDED in the baseline and NOT in the candidate  <- the finding
    exit 2  a VERDICT DISAGREEMENT between arms                         <- soundness
    exit 3  the arms do not cover the same file set

Why the exit status carries the finding rather than a table: a whole-division
A/B whose only output is a count invites reading the count. The population that
matters is the one that MOVED, and a file that stops being decided is the thing
this script exists to refuse to bury.

Usage:
    scripts/euf-online-atoms-compare.py <baseline.tsv> <candidate.tsv> [third.tsv]
"""

from __future__ import annotations

import sys
from pathlib import Path

DECIDED = ("sat", "unsat")


def load(path: Path) -> dict[str, dict[str, str]]:
    rows: dict[str, dict[str, str]] = {}
    with path.open() as handle:
        header = handle.readline().rstrip("\n").split("\t")
        for line in handle:
            if not line.strip():
                continue
            fields = line.rstrip("\n").split("\t")
            fields += [""] * (len(header) - len(fields))
            row = dict(zip(header, fields, strict=False))
            rows[row["file"]] = row
    return rows


def name(path: Path) -> str:
    return path.name.replace(".tsv", "")


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 3
    paths = [Path(p) for p in sys.argv[1:]]
    arms = [(name(p), load(p)) for p in paths]

    base_name, base = arms[0]
    keys = set(base)
    for arm_name, rows in arms[1:]:
        if set(rows) != keys:
            missing = len(keys ^ set(rows))
            print(
                f"COVERAGE: {arm_name} and {base_name} differ on {missing} files; "
                "the arms are not comparable",
                file=sys.stderr,
            )
            return 3

    print(f"files: {len(keys)}")
    for arm_name, rows in arms:
        decided = sum(1 for r in rows.values() if r["verdict"] in DECIDED)
        print(f"  {arm_name:<24} decided {decided}/{len(rows)}")

    # A verdict disagreement between two arms of the same binary is a soundness
    # finding and outranks every count below.
    disagreements = []
    for key in sorted(keys):
        verdicts = {
            rows[key]["verdict"] for _, rows in arms if rows[key]["verdict"] in DECIDED
        }
        if len(verdicts) > 1:
            disagreements.append((key, verdicts))
    if disagreements:
        print("\nVERDICT DISAGREEMENT (soundness):")
        for key, verdicts in disagreements:
            print(f"  {key}\t{sorted(verdicts)}")
        return 2

    status = 0
    for arm_name, rows in arms[1:]:
        gained = sorted(
            k
            for k in keys
            if rows[k]["verdict"] in DECIDED and base[k]["verdict"] not in DECIDED
        )
        lost = sorted(
            k
            for k in keys
            if base[k]["verdict"] in DECIDED and rows[k]["verdict"] not in DECIDED
        )
        print(f"\n{arm_name} vs {base_name}: +{len(gained)} / -{len(lost)}")
        for key in gained:
            row = rows[key]
            print(
                f"  GAINED {Path(key).name}\t{row['verdict']}\t"
                f"decided_by={row['decided_by']}\teuf_online={row['euf_online_outcome']}"
                f"@{row['euf_online_ms']}ms"
            )
        for key in lost:
            base_row = base[key]
            row = rows[key]
            print(
                f"  LOST   {Path(key).name}\twas {base_row['verdict']} "
                f"(decided_by={base_row['decided_by']}) -> {row['verdict']} "
                f"(bound_by={row['bound_by']}, euf_online="
                f"{row['euf_online_outcome']}@{row['euf_online_ms']}ms)"
            )
        if lost:
            status = 1

    # The cost distribution the ceiling is set from: how long `euf-online`
    # actually ran on the queries where it abstracted and DECIDED.
    for arm_name, rows in arms:
        costs = sorted(
            int(r["euf_online_ms"])
            for r in rows.values()
            if r["euf_online_outcome"] == "decided" and r["euf_online_ms"]
        )
        if costs:
            print(
                f"\n{arm_name}: euf-online decided {len(costs)} files; "
                f"its own cost min={costs[0]}ms median={costs[len(costs) // 2]}ms "
                f"max={costs[-1]}ms"
            )
        spends = sorted(
            int(r["euf_online_ms"])
            for r in rows.values()
            if r["euf_online_outcome"] == "declined" and r["euf_online_ms"]
        )
        if spends:
            print(
                f"{arm_name}: euf-online declined {len(spends)} files after "
                f"min={spends[0]}ms median={spends[len(spends) // 2]}ms "
                f"max={spends[-1]}ms"
            )
    return status


if __name__ == "__main__":
    sys.exit(main())
