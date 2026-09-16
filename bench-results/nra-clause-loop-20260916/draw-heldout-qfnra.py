#!/usr/bin/env python3
"""Draw a HELD-OUT `QF_NRA` file list, seeded and reproducible (ADR-2126).

ADR-2106's pattern, adapted for one division that pattern could not serve as
written. `draw-heldout.py` reads the division's pinned list from
`/nas3/data/axeyum/harness/route-ownership/ablists/<DIV>.txt`, and **there is no
`QF_NRA.txt` there** — the route-ownership harness pins `QF_LIA`, `QF_LRA`,
`QF_NIA` and the `AUF*` divisions only. Pointing the original script at
`QF_NRA` aborts. So this one takes the training set explicitly.

EXCLUDED, and the exclusion is CHECKED rather than assumed:

  * every path in the A/B list this lane measured on (`--pinned`), which is
    ADR-2121's `qfnra-200.txt` — an A/B on it is an A/B on the training set;
  * every `corpus_path` any committed row in `bench-results/ledger/` carries for
    `QF_NRA`, read through `outcome_ledger.read_ledger` rather than by globbing,
    so a schema change refuses instead of being guessed at.

The seed is a constant in this file, **not** a command-line default, so the draw
cannot be quietly re-rolled after a result; changing it is a diff. The drawn list
is committed beside it.

One thing this draw is and one thing it is not. It IS a population neither this
lane nor the ledger has looked at, which is what makes a second A/B on it worth
more than a longer one on the first. It is NOT a fresh population for any FUTURE
lane: the seed is fixed, so a later lane running this script gets the same 200
files, and citing them again would be citing a set that has been scored. A later
lane wanting a blind draw must change the seed and say so.

Usage:
    python3 draw-heldout-qfnra.py --out FILE --pinned FILE [--n 200]
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

#: **The seed.** A constant in the source. See the module docstring.
SEED = 20260916

DIVISION = "QF_NRA"


def pinned_paths(path: Path) -> set[str]:
    """Corpus-relative paths in the training list."""
    if not path.exists():
        raise SystemExit(f"ABORT: training list missing: {path}")
    out = {
        line.strip().removeprefix(f"{CORPUS}/")
        for line in path.read_text().splitlines()
        if line.strip()
    }
    if not out:
        raise SystemExit(f"ABORT: training list empty: {path}")
    return out


def ledger_paths(ledger_dir: Path) -> set[str]:
    """Every `corpus_path` any committed ledger row carries for the division."""
    out: set[str] = set()
    for tsv in sorted(ledger_dir.glob("*.tsv")):
        if tsv.name == ol.INDEX_NAME:
            continue
        for row in ol.read_ledger(tsv):
            if row.corpus_path.startswith(f"{DIVISION}/"):
                out.add(row.corpus_path)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True)
    ap.add_argument("--pinned", required=True, help="the list the A/B measured on")
    ap.add_argument("--n", type=int, default=200)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    args = ap.parse_args()

    root = CORPUS / DIVISION
    if not root.is_dir():
        raise SystemExit(f"ABORT: corpus division missing: {root}")
    # Sorted, so the population the seed indexes into is deterministic.
    every = sorted(str(p.relative_to(CORPUS)) for p in root.rglob("*.smt2") if p.is_file())

    pinned = pinned_paths(Path(args.pinned))
    ledger = ledger_paths(Path(args.ledger_dir))
    excluded = pinned | ledger
    pool = [p for p in every if p not in excluded]

    # CHECKED, not assumed: an excluded path surviving into the pool means the
    # prefix stripping is wrong and the "held-out" draw is not held out. This is
    # the guard ADR-2106 wrote and the reason to reuse its shape.
    leaked = excluded & set(pool)
    if leaked:
        raise SystemExit(f"ABORT: {len(leaked)} excluded paths leaked into the pool")
    # And the training list must actually have been FOUND in the corpus: an
    # exclusion set that intersects the corpus in nothing excludes nothing, and
    # would print a clean "held-out" draw over the training set itself.
    hit = pinned & set(every)
    if len(hit) != len(pinned):
        raise SystemExit(
            f"ABORT: only {len(hit)} of {len(pinned)} training paths are in the corpus; "
            "the exclusion would be a no-op"
        )

    rng = random.Random(f"{SEED}:{DIVISION}")
    take = min(args.n, len(pool))
    drawn = sorted(rng.sample(pool, take))

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("".join(f"{p}\n" for p in drawn), encoding="utf-8")
    print(
        f"{DIVISION}: corpus {len(every)}, excluded {len(excluded)} "
        f"(training {len(pinned)} + ledger {len(ledger)}), pool {len(pool)}, "
        f"drew {take} -> {out}"
    )

    # Exit status depends on the finding: a short draw is a real limitation on
    # what the held-out arm can show and must not pass silently.
    if take < args.n:
        print(f"SHORT DRAW: {take} of {args.n}")
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
