#!/usr/bin/env python3
"""Draw a HELD-OUT file list per division, seeded and reproducible.

Plan §7's named risk, verbatim:

    "Phase 4 optimises the sample. The 200-file pinned lists are what we
    measure on; the corpus is 60x larger. A derived order is checked on a
    held-out draw before it ships."

The pinned lists ARE the population ADR-2102's ledger rows were measured on
(`/nas3/data/axeyum/harness/route-ownership/ablists/<DIV>.txt`, verified
byte-identical as file SETS to `postmerge-board-dt`'s `T1_<DIV>.txt`), so an
A/B on them is an A/B on the training set. This draws from the rest.

EXCLUDED, and the exclusion is checked rather than assumed:

  * every path in the division's pinned list;
  * every `corpus_path` any committed row in `bench-results/ledger/` carries
    for that division -- the ledger is the table the order was derived from,
    and a file it has a row for is not held out however it got there.

The seed is a constant in this file and the drawn list is committed beside it,
so the draw is reproducible and cannot be re-rolled quietly after a result.

Usage:
    python3 draw-heldout.py --out-dir DIR [--n 200] [--div QF_NIA --div UFNIA]
"""

from __future__ import annotations

import argparse
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
if str(REPO / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO / "scripts"))

import outcome_ledger as ol  # noqa: E402

#: The corpus root the harness runs against.
CORPUS = Path("/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental")

#: The pinned lists the ledger was measured on.
PINNED = Path("/nas3/data/axeyum/harness/route-ownership/ablists")

#: **The seed.** A constant in the source, not a command-line default, so the
#: draw cannot be re-rolled after seeing a result. Changing it is a diff.
SEED = 20260915

DEFAULT_DIVISIONS = ("QF_NIA", "UFNIA")


def pinned_paths(division: str) -> set[str]:
    """Corpus-relative paths in the division's pinned list."""
    path = PINNED / f"{division}.txt"
    if not path.exists():
        raise SystemExit(f"ABORT: pinned list missing: {path}")
    out = set()
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        out.add(line.removeprefix(f"{CORPUS}/"))
    if not out:
        raise SystemExit(f"ABORT: pinned list empty: {path}")
    return out


def ledger_paths(division: str, ledger_dir: Path) -> set[str]:
    """Every `corpus_path` any committed ledger row carries for `division`.

    Read through `outcome_ledger.read_ledger`, not by globbing the TSVs by
    hand, so a schema change refuses instead of being guessed at.
    """
    out: set[str] = set()
    for tsv in sorted(ledger_dir.glob("*.tsv")):
        if tsv.name == ol.INDEX_NAME:
            continue
        for row in ol.read_ledger(tsv):
            if row.corpus_path.startswith(f"{division}/"):
                out.add(row.corpus_path)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--n", type=int, default=200)
    ap.add_argument("--div", action="append", default=None)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    args = ap.parse_args()

    divisions = args.div or list(DEFAULT_DIVISIONS)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    ledger_dir = Path(args.ledger_dir)

    short = []
    for division in divisions:
        root = CORPUS / division
        if not root.is_dir():
            raise SystemExit(f"ABORT: corpus division missing: {root}")
        # Sorted, so the population the seed indexes into is deterministic.
        every = sorted(
            str(p.relative_to(CORPUS)) for p in root.rglob("*.smt2") if p.is_file()
        )
        excluded = pinned_paths(division) | ledger_paths(division, ledger_dir)
        pool = [p for p in every if p not in excluded]

        # The exclusion is CHECKED, not assumed: a pinned path that survived
        # into the pool means the prefix stripping is wrong and the "held-out"
        # draw is not held out.
        leaked = excluded & set(pool)
        if leaked:
            raise SystemExit(f"ABORT: {len(leaked)} excluded paths leaked into the pool")

        rng = random.Random(f"{SEED}:{division}")
        take = min(args.n, len(pool))
        drawn = sorted(rng.sample(pool, take))

        out = out_dir / f"{division}.txt"
        out.write_text("".join(f"{CORPUS}/{p}\n" for p in drawn), encoding="utf-8")
        print(
            f"{division}: corpus {len(every)}, excluded {len(excluded)} "
            f"(pinned {len(pinned_paths(division))} + ledger), pool {len(pool)}, "
            f"drew {take} -> {out}"
        )
        if take < args.n:
            short.append(f"{division} ({take} of {args.n})")

    # Exit status depends on the finding: a short draw is a real limitation on
    # what the held-out arm can show, and must not pass silently.
    if short:
        print(f"SHORT DRAW: {', '.join(short)}")
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
