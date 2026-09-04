#!/usr/bin/env python3
"""Draw 7: every family preregistered before the draw keeps its partition.

R8/R10 tie the effective assignment to the preregistered one inside the
generator. This is the independent outside check, and it carries its own
negative control so a run in which the comparison silently did nothing cannot
report PASS.

    python3 scripts/check-draw7-frozen-families.py [--before <git-ref>]

Exits nonzero if any preregistered family moved partition, and also if the
negative control fails to fire -- a checker that cannot fail is worse than no
checker.

AMENDED 2026-09-03: a move is LICENSED when
`artifacts/autogenesis/mathlib-nursery-split-policy-v1.json` carries an
`amendments` row naming the same family, the same `from`, the same `to`, and
`irreversible: true` -- the ADR-0542 breach repair. That repair is the ONLY
way `check-autogenesis-holdout-isolation.py` lets a spent family out of
held-out, and this gate refused it outright: the first such repair
(natural-bit-decode, 7296730d6, 2026-08-30) reached main only because this
script was then invoked by nothing (wired into the hook 2026-09-02), and the
second (natural-elementary-bounds, 2026-09-03) was refused at push. An
unamended move, a move whose amendment names another direction, and a
family that vanished all still fail; a second negative control proves the
licensing cannot wave a mismatched row through.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = "artifacts/autogenesis/nursery-v2-extension.json"
POLICY = "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json"

# The commit that introduced draw 7. Its parent is the pre-draw tree.
DEFAULT_BEFORE = "HEAD~1"


def partitions(blob: str) -> dict[str, str]:
    data = json.loads(blob)
    out: dict[str, str] = {}
    for entry in data["entries"]:
        family, partition = entry["family"], entry["partition"]
        if out.setdefault(family, partition) != partition:
            raise SystemExit(
                f"family {family!r} carries two partitions in one manifest; "
                "R1 should have refused this")
    return out


def licensed_moves(policy_blob: str) -> set[tuple[str, str, str]]:
    """(family, from, to) triples an irreversible ADR-0542 amendment records."""
    data = json.loads(policy_blob)
    out: set[tuple[str, str, str]] = set()
    for row in data.get("amendments") or []:
        if not isinstance(row, dict) or row.get("irreversible") is not True:
            continue
        family, src, dst = row.get("family"), row.get("from"), row.get("to")
        if family and src and dst:
            out.add((family, src, dst))
    return out


def compare(
    before: dict[str, str],
    after: dict[str, str],
    licensed: set[tuple[str, str, str]] | None = None,
) -> list[str]:
    moved = []
    for family, was in sorted(before.items()):
        now = after.get(family)
        if now is None:
            moved.append(f"{family}: {was} -> ABSENT")
        elif now != was and (family, was, now) not in (licensed or set()):
            moved.append(f"{family}: {was} -> {now}")
    return moved


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--before", default=DEFAULT_BEFORE,
                    help="git ref holding the pre-draw manifest")
    args = ap.parse_args()

    blob = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{args.before}:{MANIFEST}"],
        capture_output=True, text=True, check=True).stdout
    before = partitions(blob)
    after = partitions((ROOT / MANIFEST).read_text())

    licensed = licensed_moves((ROOT / POLICY).read_text())
    moved = compare(before, after, licensed)
    amended = sorted(
        f for f, was in before.items()
        if after.get(f) not in (None, was) and (f, was, after[f]) in licensed)
    fresh = sorted(set(after) - set(before))

    # NEGATIVE CONTROL: move one frozen family and require the comparison to
    # see it. Without this, a bug that empties `before` reports PASS.
    if not before:
        print("CONTROL FAILED: the pre-draw manifest yielded no families")
        return 1
    victim = sorted(before)[0]
    mutated = dict(after)
    mutated[victim] = "train" if before[victim] != "train" else "held-out"
    if not compare(before, mutated):
        print(f"CONTROL FAILED: moving {victim!r} was not detected")
        return 1
    # SECOND CONTROL: an amendment for the same family in the WRONG direction
    # must not license the move -- the row has to match all three fields.
    wrong = {(victim, before[victim], "development" if mutated[victim] != "development" else "train")}
    if not compare(before, mutated, wrong):
        print(f"CONTROL FAILED: a mismatched amendment licensed moving {victim!r}")
        return 1

    print(f"DRAW7_FROZEN|frozen={len(before)}|moved={len(moved)}"
          f"|amended={len(amended)}|new={len(fresh)}|control=FIRES"
          f"|verdict={'PASS' if not moved else 'FAIL'}")
    for line in moved:
        print(f"  MOVED {line}")
    for family in amended:
        print(f"  AMENDED {family}: {before[family]} -> {after[family]} (irreversible, ADR-0542)")
    print(f"  new families: {fresh}")
    return 1 if moved else 0


if __name__ == "__main__":
    sys.exit(main())
