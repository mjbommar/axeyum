#!/usr/bin/env python3
"""Every drawn row's `(fact_id, partition)` pair, digested, so a spend cannot move one.

Scoring a held-out family is the one deliberate spend the nursery exists for.
The hazard it creates is a *different* one: that while recording the score,
some row quietly changes partition -- moved to `development` because it turned
out hard, or to `held-out` because it turned out easy. Either would make the
next draw's blindness a fiction, and neither shows up in a diff a reviewer
scans, because a manifest of 716 entries is not read line by line.

So this prints one digest over the sorted `(fact_id, partition)` pairs of BOTH
manifests. A baseline is pinned in `BASELINE`; `--check` fails if the digest
has moved, naming the rows that differ against a committed snapshot.

**The negative control is not optional and is run on every invocation.**
`--self-check` (implied by `--check`) recomputes the digest over a copy of the
population with exactly one row's partition flipped and REQUIRES that the
digest change. Without it this gate would print a stable digest whether or not
the digest function looked at `partition` at all -- which is precisely the
"checker that cannot fail" this repository refuses to ship. A digest over
`fact_id` alone is stable too, and would pass every real run forever.

Exit 0 pass, 1 violation, 2 error (unreadable manifest, empty population, or a
failed self-check). FAIL-CLOSED on all three.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFESTS = (
    ROOT / "artifacts/autogenesis/nursery-v1.json",
    ROOT / "artifacts/autogenesis/nursery-v2-extension.json",
)
SNAPSHOT = ROOT / "artifacts/autogenesis/drawn-population-partition-snapshot-v1.json"

# Pinned at 2026-09-01 by lane `score-the-blind-population`, immediately after
# committing its scoring pre-registration and BEFORE inspecting any target.
BASELINE = "d831a202659a6eaa733cc5c34f98495f283521cfb8dc70ee42f81e7509148ad3"


class PopulationError(Exception):
    pass


def load_pairs(manifests=MANIFESTS) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for path in manifests:
        if not path.is_file():
            raise PopulationError(f"manifest is missing: {path}")
        try:
            manifest = json.loads(path.read_text())
        except json.JSONDecodeError as error:
            raise PopulationError(f"manifest is unreadable: {path.name}: {error}") from error
        entries = manifest.get("entries")
        if not isinstance(entries, list) or not entries:
            raise PopulationError(f"{path.name} has no entries; this gate would pass vacuously")
        for entry in entries:
            if not isinstance(entry, dict):
                raise PopulationError(f"{path.name} has a non-object entry")
            fact_id = entry.get("fact_id")
            partition = entry.get("partition")
            if not isinstance(fact_id, str) or not isinstance(partition, str):
                raise PopulationError(f"{path.name} has an entry without fact_id/partition")
            pairs.append((fact_id, partition))
    if not pairs:
        raise PopulationError("the drawn population is empty; this gate would pass vacuously")
    return sorted(pairs)


def digest(pairs: list[tuple[str, str]]) -> str:
    h = hashlib.sha256()
    for fact_id, partition in sorted(pairs):
        h.update(fact_id.encode())
        h.update(b"\x1f")
        h.update(partition.encode())
        h.update(b"\x1e")
    return h.hexdigest()


def self_check(pairs: list[tuple[str, str]]) -> tuple[bool, str, str]:
    """Flip ONE row's partition and require the digest to move.

    Deliberately flips a row that is currently `held-out`, since a digest that
    ignored `partition` -- the realistic way this gate rots -- is exactly what
    scoring work would tempt someone into.
    """
    real = digest(pairs)
    flipped = copy.deepcopy(pairs)
    index = next((i for i, (_, p) in enumerate(flipped) if p == "held-out"), None)
    if index is None:
        raise PopulationError(
            "no held-out row to flip; the self-check cannot discriminate and this "
            "gate must not report a pass it did not earn")
    fact_id, partition = flipped[index]
    flipped[index] = (fact_id, "development" if partition != "development" else "train")
    control = digest(flipped)
    return (control != real), real, control


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="fail if the digest has moved from BASELINE / the snapshot")
    parser.add_argument("--write-baseline", action="store_true",
                        help="print the current digest and rewrite the snapshot")
    args = parser.parse_args()

    try:
        pairs = load_pairs()
        ok, real, control = self_check(pairs)
    except PopulationError as error:
        print(f"DRAWN_POPULATION_ZERO_DIFF|verdict=ERROR|reason={error}")
        return 2

    if not ok:
        print("DRAWN_POPULATION_ZERO_DIFF|verdict=ERROR|reason=self-check did not "
              "discriminate: flipping one row's partition left the digest unchanged")
        return 2

    counts: dict[str, int] = {}
    for _, partition in pairs:
        counts[partition] = counts.get(partition, 0) + 1
    summary = ",".join(f"{k}={counts[k]}" for k in sorted(counts))

    if args.write_baseline:
        SNAPSHOT.write_text(json.dumps(
            {"kind": "axeyum-drawn-population-partition-snapshot",
             "schema_version": 1,
             "digest_sha256": real,
             "rows": len(pairs),
             "partition_counts": counts,
             "pairs": [list(p) for p in pairs]},
            indent=1, sort_keys=True) + "\n")
        print(f"DRAWN_POPULATION_ZERO_DIFF|rows={len(pairs)}|{summary}"
              f"|digest={real}|control={control[:16]}|verdict=BASELINE-WRITTEN")
        return 0

    if args.check:
        violations: list[str] = []
        if BASELINE != "PENDING" and real != BASELINE:
            violations.append(f"digest moved: {real} != pinned {BASELINE}")
        if SNAPSHOT.is_file():
            snap = json.loads(SNAPSHOT.read_text())
            was = {tuple(p) for p in snap.get("pairs", [])}
            now = set(pairs)
            for fact_id, partition in sorted(now - was):
                violations.append(f"row not in snapshot or partition changed: {fact_id} -> {partition}")
            for fact_id, partition in sorted(was - now):
                violations.append(f"row missing from population or partition changed: {fact_id} was {partition}")
        else:
            violations.append(f"snapshot is missing: {SNAPSHOT}")
        if violations:
            for line in violations[:40]:
                print(f"  VIOLATION {line}")
            print(f"DRAWN_POPULATION_ZERO_DIFF|rows={len(pairs)}|{summary}"
                  f"|digest={real}|violations={len(violations)}|verdict=FAIL")
            return 1

    print(f"DRAWN_POPULATION_ZERO_DIFF|rows={len(pairs)}|{summary}"
          f"|digest={real}|control={control[:16]}|self_check=DISCRIMINATES|verdict=PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
