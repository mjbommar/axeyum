"""Benchmark selection — a faithful replica of SMT-COMP 2026 §6.

Given the pool of benchmarks in a logic (each tagged with its *family* — the
bottom-level SMT-LIB submitter directory, §6 "Benchmark demographics"), this
reproduces the selection process that decides which benchmarks a division
actually runs:

  1. (optional) remove easy/inappropriate benchmarks — the "easy" filter needs
     the 2018-2024 historical results (solved-by-all in <1s), which we do not
     have locally, so it is a no-op hook here and logged as skipped;
  2. cap the number of instances by the logic size n (§6, cases 4a-4d):
        n <= 300           -> all
        300 < n <= 600     -> 300
        600 < n <= 1000    -> 50%
        n > 1000           -> 500 + (n - 1000) / 10
  3. guarantee inclusion of *new* families first (one benchmark from each), then
     fill the remainder by uniform random sampling — all randomness driven by a
     single competition seed (§6 "Pseudo-random numbers").

Scrambling (§6 "Benchmark scrambling") is anti-cheating and does not affect
scores, so it is referenced but not reimplemented here (see the upstream
`SMT-COMP/scrambler`, read-only).
"""

from __future__ import annotations

import math
import os
import random
from dataclasses import dataclass
from typing import Callable, Optional


def division_cap(n: int) -> int:
    """§6 case 4: the number of instances to select from a logic of size n."""
    if n <= 300:
        return n
    if n <= 600:
        return 300
    if n <= 1000:
        return n // 2
    return int(500 + (n - 1000) // 10)


def family_of(path: str, corpus_root: str) -> str:
    """The family is the bottom-level submitter directory (§6). We approximate it
    by the immediate parent directory of the benchmark relative to the corpus."""
    rel = os.path.relpath(path, corpus_root)
    parent = os.path.dirname(rel)
    return parent or "(root)"


@dataclass
class SelectionResult:
    selected: list[str]
    n_pool: int
    cap: int
    n_families: int
    new_families_covered: int
    seed: int


def select_division(
    benchmarks: list[str],
    corpus_root: str,
    *,
    seed: int,
    new_families: Optional[set[str]] = None,
    is_easy: Optional[Callable[[str], bool]] = None,
) -> SelectionResult:
    """Reproduce §6 selection for one logic/division.

    `new_families` are families flagged as new this year (§6 guarantees one
    benchmark from each is picked first); default: treat every family as new so
    the diversity guarantee still spreads the pick across submitters.
    `is_easy` optionally removes easy benchmarks (default: keep all).
    """
    pool = list(benchmarks)
    if is_easy is not None:
        pool = [b for b in pool if not is_easy(b)]
    pool.sort()  # determinism before any seeded shuffle

    n = len(pool)
    cap = division_cap(n)
    if cap >= n:
        return SelectionResult(pool, n, cap, _count_families(pool, corpus_root), 0, seed)

    rng = random.Random(seed)
    by_family: dict[str, list[str]] = {}
    for b in pool:
        by_family.setdefault(family_of(b, corpus_root), []).append(b)
    families = sorted(by_family)
    if new_families is None:
        new_families = set(families)

    selected: list[str] = []
    chosen: set[str] = set()

    # (a) one benchmark from each *new* family first (§6 case 4c/4d guarantee).
    new_covered = 0
    for fam in families:
        if fam in new_families and len(selected) < cap:
            pick = rng.choice(by_family[fam])
            selected.append(pick)
            chosen.add(pick)
            new_covered += 1

    # (b) fill the remainder by uniform random over the rest.
    remaining = [b for b in pool if b not in chosen]
    rng.shuffle(remaining)
    for b in remaining:
        if len(selected) >= cap:
            break
        selected.append(b)

    selected.sort()
    return SelectionResult(
        selected=selected,
        n_pool=n,
        cap=cap,
        n_families=len(families),
        new_families_covered=new_covered,
        seed=seed,
    )


def _count_families(pool: list[str], corpus_root: str) -> int:
    return len({family_of(b, corpus_root) for b in pool})
