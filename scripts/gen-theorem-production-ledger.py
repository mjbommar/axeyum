#!/usr/bin/env python3
"""Count this project's theorems across every prelude, and pin the number.

`docs/formalized-math-2026-08/05-throughput.md` concluded on 2026-08-19:

    nobody can currently measure this project's theorem-production rate, because
    no tool counts theorems across preludes, and the one that counts them in
    `nat_prelude` has been superseded by where the work went.

That was exactly right, and it stayed true for three more days. `nat_theorem_
inventory` counts `nat` and `int_theorem_inventory` counts `Int.*`; `rat`,
`creal`, `complex`, `logic` and `string` had no theorem counter at all. So the
headline counter could not rise when production moved to ℚ and the constructed
ℝ, and a fall would not have meant a regression either -- unfalsifiable in both
directions, which is the same defect class as a checker that cannot fail.

This is the theorem-side twin of `gen-lean-axiom-ledger.py`. It runs the kernel,
not a source scan: theorem declarations go through a `.theorem(name, ...)` helper
taking an interned `NameId`, so grepping `.theorem("...")` returns ZERO matches
and three separate counts of this repository's theorems were wrong before anyone
built the environment to look.

**Direction is the opposite of the axiom ledger's.** There, a rise is a
regression. Here, a rise is production and a FALL is the regression -- theorems
do not un-prove themselves, so a drop means a prelude stopped building, a
declaration was removed, or the instrument broke. `--check` reports which way a
number moved and says which of the two it is.

Two numbers, and they are different claims:

* `theorems` per prelude is CUMULATIVE. Preludes nest -- `build_rat_prelude`
  builds ℤ, which builds Nat, which builds logic -- so `rat`'s count includes
  everything underneath it. **Summing this column multiply-counts most of the
  library** and is not a production figure.
* `originated` attributes each theorem to the prelude where it was proved, by
  taking the minimal element of the inclusion order. This column DOES sum, to
  the distinct total.

Usage:  python3 scripts/gen-theorem-production-ledger.py [--check]
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEDGER = ROOT / "docs/plan/generated/theorem-production-ledger.md"
EXAMPLE = "prelude_theorem_inventory"
COMMAND = (
    "cargo run --quiet --release -p axeyum-lean-kernel "
    f"--example {EXAMPLE} -- --include-constructed"
)

# Dropping a prelude from the example would otherwise make this ledger quietly
# narrower rather than red. A prelude that exists must be listed here.
#
# `characterization` (the Peano/initiality package -- `Nat.Peano.*`,
# `Int.Characterization.*`) added 2026-08-27: `prelude_theorem_inventory`'s
# `build_groups` never built it before, so its 32 axiom-free theorems were
# silently absent from `distinct` with no error -- see
# `docs/research/11-design-review/2026-08-27-rat-reindexing-and-the-denominator-gap.md`.
#
# `ipc` (the intuitionistic-propositional-calculus soundness package,
# `ipc_*` flat names) added to `prelude_theorem_inventory` on 2026-08-31 and
# never added here -- this ledger's `--check` caught the gap on 2026-09-01
# (measured: this generator raised `coverage changed` rather than silently
# publishing a narrower distinct count, which is the fail-closed behaviour
# this comment block exists to keep true for the NEXT prelude too).
#
# `list` (`List.{u}` -- the nine pure-`List`/bridge theorems from
# `list-carrier-1`, `List.count_toMultiset` and `List.Perm`'s four theorems
# from `list-carrier-2`) added to `prelude_theorem_inventory` 2026-09-03 and
# added here in the SAME commit, per the `ipc` precedent above -- this
# ledger's `--check` was verified to raise `coverage changed` first, before
# this line was added, confirming the gap it exists to catch.
EXPECTED_PRELUDES: tuple[str, ...] = (
    "axreal",
    "characterization",
    "complex",
    "cpoint",
    "creal",
    "integer",
    "ipc",
    "list",
    "logic",
    "nat",
    "rat",
    "string",
)

GROUP_RE = re.compile(
    r"^(?P<prelude>[a-z]+): theorems=(?P<theorems>\d+) axiom_free=(?P<free>\d+) "
    r"axiom_bearing=(?P<bearing>\d+) originated=(?P<origin>\d+)$"
)
DISTINCT_RE = re.compile(
    r"^distinct: theorems=(?P<theorems>\d+) axiom_free=(?P<free>\d+) "
    r"axiom_bearing=(?P<bearing>\d+) preludes=(?P<preludes>\S+)$"
)


class LedgerError(Exception):
    pass


def measure() -> tuple[dict[str, dict[str, int]], dict[str, int], int]:
    completed = subprocess.run(
        COMMAND, shell=True, cwd=ROOT, capture_output=True, text=True, check=False
    )
    if completed.returncode != 0:
        raise LedgerError(f"{EXAMPLE} failed: {completed.stderr.strip()[-400:]}")

    groups: dict[str, dict[str, int]] = {}
    distinct: dict[str, int] | None = None
    ties: int | None = None
    for line in completed.stderr.splitlines():
        line = line.strip()
        if match := GROUP_RE.match(line):
            groups[match["prelude"]] = {
                "theorems": int(match["theorems"]),
                "axiom_free": int(match["free"]),
                "axiom_bearing": int(match["bearing"]),
                "originated": int(match["origin"]),
            }
        elif match := DISTINCT_RE.match(line):
            distinct = {
                "theorems": int(match["theorems"]),
                "axiom_free": int(match["free"]),
                "axiom_bearing": int(match["bearing"]),
            }
            covered = tuple(sorted(match["preludes"].split(",")))
            if covered != EXPECTED_PRELUDES:
                raise LedgerError(
                    f"coverage changed: measured {covered}, expected {EXPECTED_PRELUDES}"
                )
        elif line.startswith("origin_ties:"):
            ties = int(line.split(":", 1)[1])

    if distinct is None or ties is None:
        raise LedgerError("the example did not report a distinct total or tie count")
    missing = set(EXPECTED_PRELUDES) - set(groups)
    if missing:
        raise LedgerError(f"preludes absent from the measurement: {sorted(missing)}")

    # `originated` is an exact partition of the distinct set. If it does not sum,
    # the attribution is wrong and every per-prelude production number below it
    # is wrong too -- fail rather than publish a table that does not add up.
    total = sum(group["originated"] for group in groups.values())
    if total != distinct["theorems"]:
        raise LedgerError(
            f"originated columns sum to {total}, distinct total is {distinct['theorems']}"
        )
    return groups, distinct, ties


def render(
    groups: dict[str, dict[str, int]], distinct: dict[str, int], ties: int
) -> str:
    lines = [
        "# Generated theorem production ledger",
        "",
        "> Generated by `scripts/gen-theorem-production-ledger.py`. Do not hand-edit.",
        f"> Authority: `{COMMAND}` — read from the kernel, never from source text.",
        "",
        "| Prelude | Theorems (cumulative) | Originated here | Axiom-free | Axiom-bearing |",
        "|---|---:|---:|---:|---:|",
    ]
    for prelude in EXPECTED_PRELUDES:
        group = groups[prelude]
        lines.append(
            f"| `{prelude}` | {group['theorems']} | {group['originated']} | "
            f"{group['axiom_free']} | {group['axiom_bearing']} |"
        )
    lines += [
        f"| **distinct** | **{distinct['theorems']}** | "
        f"**{sum(g['originated'] for g in groups.values())}** | "
        f"**{distinct['axiom_free']}** | **{distinct['axiom_bearing']}** |",
        "",
        f"- **{distinct['theorems']} distinct theorems**, of which "
        f"**{distinct['axiom_free']} rest on no assumption at all** "
        f"({distinct['axiom_bearing']} are axiom-bearing).",
        "",
        "**Do not sum the second column.** Preludes nest, so `rat` contains every",
        "Nat and Int theorem beneath it. The *Originated here* column is the one",
        "that partitions the library, and it sums to the distinct total by",
        "construction — the generator fails if it does not.",
        "",
        f"Origin ties: {ties}. A tie is two preludes with identical theorem sets",
        "(`axreal` builds `logic` and adds no theorems of its own); the earlier",
        "prelude in dependency order takes the credit.",
        "",
        "## Reading a change",
        "",
        "The direction here is the **opposite** of the",
        "[axiom ledger](lean-axiom-ledger.md). Theorems do not un-prove themselves:",
        "",
        "- a **rise** is production, and is the result this programme exists to make;",
        "- a **fall** is a regression — a prelude stopped building, a declaration was",
        "  removed, or the instrument broke — and is never something to re-pin quietly.",
        "",
        "`axiom_bearing` rising is a regression in either direction of reading: it",
        "means a theorem was admitted resting on an assumption.",
        "",
        "## What this does not say",
        "",
        "It counts theorems, not **autonomous** theorems. Nothing here distinguishes",
        "a theorem the system produced with nobody writing the proof from one a lane",
        "hand-constructed, and that distinction — not the total — is the programme's",
        "headline metric",
        "([`docs/autogenesis/04-metrics-and-evaluation.md`](../../autogenesis/04-metrics-and-evaluation.md)).",
        "Provenance classification is the next increment of P1 in",
        "[`docs/autogenesis/226-production-measurement-and-general-producer-plan.md`](../../autogenesis/226-production-measurement-and-general-producer-plan.md).",
        "",
    ]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        groups, distinct, ties = measure()
        rendered = render(groups, distinct, ties)
        if args.check:
            if not LEDGER.exists():
                raise LedgerError(f"{LEDGER.relative_to(ROOT)} does not exist")
            committed = LEDGER.read_text()
            if committed != rendered:
                raise LedgerError(_direction(committed, rendered))
        else:
            LEDGER.write_text(rendered)
        print(
            f"THEOREM_PRODUCTION|distinct={distinct['theorems']}|"
            f"axiom_free={distinct['axiom_free']}|"
            f"axiom_bearing={distinct['axiom_bearing']}|"
            f"preludes={len(EXPECTED_PRELUDES)}|ties={ties}"
        )
    except LedgerError as error:
        print(f"THEOREM_PRODUCTION_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


def _direction(committed: str, rendered: str) -> str:
    """Say which way each number moved, and which of the two that is."""

    def total(text: str) -> int | None:
        match = re.search(r"- \*\*(\d+) distinct theorems\*\*", text)
        return int(match[1]) if match else None

    was, now = total(committed), total(rendered)
    if was is None or now is None:
        return "ledger is stale; regenerate without --check"
    if now > was:
        return (
            f"ledger is stale: distinct theorems ROSE {was} -> {now}. That is "
            "production — regenerate and say so in the commit message."
        )
    if now < was:
        return (
            f"ledger is stale: distinct theorems FELL {was} -> {now}. Theorems do "
            "not un-prove themselves: a prelude stopped building, a declaration "
            "was removed, or this instrument broke. Do not re-pin without an "
            "explanation."
        )
    return "ledger is stale: the total is unchanged but a per-prelude row moved"


if __name__ == "__main__":
    raise SystemExit(main())
