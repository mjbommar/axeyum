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
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = "artifacts/autogenesis/nursery-v2-extension.json"

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


def compare(before: dict[str, str], after: dict[str, str]) -> list[str]:
    moved = []
    for family, was in sorted(before.items()):
        now = after.get(family)
        if now is None:
            moved.append(f"{family}: {was} -> ABSENT")
        elif now != was:
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

    moved = compare(before, after)
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

    print(f"DRAW7_FROZEN|frozen={len(before)}|moved={len(moved)}"
          f"|new={len(fresh)}|control=FIRES"
          f"|verdict={'PASS' if not moved else 'FAIL'}")
    for line in moved:
        print(f"  MOVED {line}")
    print(f"  new families: {fresh}")
    return 1 if moved else 0


if __name__ == "__main__":
    sys.exit(main())
