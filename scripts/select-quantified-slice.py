#!/usr/bin/env python3
"""Deterministically select a stratified slice of a staged SMT-LIB logic directory.

Why this exists
---------------
The committed slices under ``corpus/public-curated/`` are drawn from the cvc5
regression suite, which is why they are small enough to vendor. They are *not*
the SMT-LIB library, and the quantified divisions are where that distinction
matters most: axeyum has no honest UF/UFLIA row at all, while SMT-COMP measures
those divisions on families like ``sledgehammer``, ``tokeneer``, ``simplify2``
and ``boogie`` that live only in the staged library.

So this selects from the staged library instead, and the selection is
**deterministic** rather than sampled: no clock, no RNG, no seed to lose. Given
the same library it reproduces byte-for-byte, which is the property a committed
baseline needs.

Method
------
Stratify by family, proportional to family size, then take an **even stride**
through each family's sorted file list. A stride rather than a prefix because
benchmark families are usually named in generated order, so the first N files of
``sledgehammer`` are systematically easier or more similar than a spread. Every
family with at least one file is represented, so a small family cannot be
rounded out of existence.

Usage
-----
    python3 scripts/select-quantified-slice.py \\
        /nas3/.../non-incremental/UFLIA --target 300 --out /tmp/uflia-slice.txt

The output is a newline-terminated list of absolute paths, sorted, suitable for
``--file-list`` style consumption or for staging into a directory.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def families(root: Path) -> dict[str, list[Path]]:
    """Immediate subdirectories of `root`, each mapped to its sorted `.smt2` files."""
    out: dict[str, list[Path]] = {}
    for child in sorted(root.iterdir()):
        if not child.is_dir():
            continue
        files = sorted(p for p in child.rglob("*.smt2") if p.is_file())
        if files:
            out[child.name] = files
    return out


def stride_take(files: list[Path], want: int) -> list[Path]:
    """`want` files spread evenly across `files` by index."""
    if want >= len(files):
        return list(files)
    if want <= 0:
        return []
    # Evenly spaced indices, inclusive of the first element.
    step = len(files) / want
    picked = []
    for i in range(want):
        picked.append(files[min(len(files) - 1, int(i * step))])
    # A stride can collide at the tail on tiny families; keep it exact.
    seen: set[Path] = set()
    unique = [p for p in picked if not (p in seen or seen.add(p))]
    index = 0
    while len(unique) < want and index < len(files):
        if files[index] not in seen:
            unique.append(files[index])
            seen.add(files[index])
        index += 1
    return unique


def select(root: Path, target: int) -> tuple[list[Path], dict[str, int]]:
    groups = families(root)
    if not groups:
        raise SystemExit(f"no families with .smt2 files under {root}")
    total = sum(len(v) for v in groups.values())

    # Proportional quota, but every family gets at least one file.
    quota: dict[str, int] = {}
    for name, files in groups.items():
        share = int(round(target * len(files) / total))
        quota[name] = max(1, min(len(files), share))

    # Reconcile to the target by adjusting the largest families first, so the
    # correction lands where it distorts the proportions least.
    order = sorted(groups, key=lambda n: -len(groups[n]))
    while sum(quota.values()) > target:
        moved = False
        for name in order:
            if sum(quota.values()) <= target:
                break
            if quota[name] > 1:
                quota[name] -= 1
                moved = True
        if not moved:
            break
    while sum(quota.values()) < target:
        moved = False
        for name in order:
            if sum(quota.values()) >= target:
                break
            if quota[name] < len(groups[name]):
                quota[name] += 1
                moved = True
        if not moved:
            break

    chosen: list[Path] = []
    for name in sorted(groups):
        chosen.extend(stride_take(groups[name], quota[name]))
    return sorted(chosen), {n: quota[n] for n in sorted(quota)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="staged logic directory")
    parser.add_argument("--target", type=int, default=300)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    chosen, quota = select(args.root, args.target)
    args.out.write_text("".join(f"{p}\n" for p in chosen), encoding="utf-8")

    total = sum(len(v) for v in families(args.root).values())
    print(f"QUANTIFIED_SLICE|root={args.root}|population={total}|selected={len(chosen)}")
    for name, count in quota.items():
        print(f"  {count:5d}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
