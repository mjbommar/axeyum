#!/usr/bin/env python3
"""Detect held-out nursery propositions the kernel ALREADY proves.

`docs/autogenesis/263-holdout-contamination-by-ordinary-development.md` found
that ordinary hand development -- nothing to do with autogenesis -- had already
proved at least 5 of the 57 (now 20 of the pre-repair 57) held-out Mathlib
propositions in `artifacts/autogenesis/nursery-v1.json`, entirely undetected by
`scripts/check-autogenesis-holdout-isolation.py`. That gate reads one field
(`epistemic_status`) and scans files for textual REFERENCES to a held-out fact
id; a lane proving `Nat.choose_self` in `nat_prelude/choose.rs` because it
needed it for something else never touches either signal, because the fact's
`epistemic_status` correctly stays `open` (nobody credited it) and no artifact
ever names the fact id. The guard was sound about what it measured and blind to
what mattered.

This script is the guard one level up: it asks whether the KERNEL -- not the
ledger -- already contains a proof of each held-out proposition, by comparing
the fact's `formal.statement` against a fresh, freshly-built rendered kernel
type. It is deliberately narrower than a full semantic Lean-statement
equivalence checker, because that does not exist and a fuzzy one would be
worse than no checker: in the audit behind doc 263, **14 of 16** name-level
candidates were REFUTED once the actual statements were compared (one matched
three unrelated Mathlib propositions). So:

  * `KNOWN_CONTAMINATION` is a REVIEWED table -- each row was compared by hand,
    once, against a `--release` `nat_theorem_inventory` / `int_theorem_inventory`
    dump, and the exact rendered type line is pinned. Every run RE-DERIVES the
    match against the LIVE kernel build; nothing here is a cache of the
    finding. If a future refactor changes or removes the theorem, this table
    stops confirming it -- which is correct, not a regression in the checker.
  * A CANDIDATE SWEEP flags held-out facts NOT in that table whose fact-id slug
    shares every word with some kernel theorem name, for human review. This is
    the part that "would have caught it": run today, against a kernel that has
    not yet grown a sixth contaminating theorem, it prints nothing new; the day
    a lane adds one, the next run surfaces the name as `needs-review` before
    anyone builds an ADR-0542 amendment for it. It is advisory, not a verdict
    -- statement comparison is still a human step, exactly because a name match
    is usually wrong.

FAIL-CLOSED only on the detector's own infrastructure: a missing/unreadable
nursery manifest, an empty held-out population, or a cargo build that cannot
run at all. A CONFIRMED CONTAMINATION IS NOT A FAILURE -- see the reasoning in
the doc above: failing the build would pressure a lane into not proving a
theorem it needs, which is precisely the wrong incentive. The exit status
depends only on whether the detector itself could run; the finding is reported,
not gated.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from typing import Any, Callable

ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
# The 2026-08-29 refill preregisters its held-out rows HERE, not in v1, and this
# detector read v1 alone until 2026-08-30. Measured that day against the
# pre-amendment population: 136 held-out rows, **16 in v1 and 120 in the
# extension**, so the detector was aimed at 12% of the population it names. Of
# the 9 rows its own matching rule would have surfaced, 6 were extension rows it
# never read -- including `F:ml430-nat-odd-of-mul-left-2c6c2553`, which matches
# the admitted `Int.odd_of_mul_left` by the EXISTING equality rule. The
# `natural-parity` contamination was reachable by this gate as already written;
# it was pointed at the wrong file. Same fail-closed treatment as
# `check-autogenesis-holdout-isolation.py`: BOTH manifests are required and each
# must contribute rows, because a detector reading one of two populations
# reports the same "clean" as a detector that works.
EXTENSION = ROOT / "artifacts/autogenesis/nursery-v2-extension.json"

EXAMPLE_BY_PRELUDE = {
    "nat": "nat_theorem_inventory",
    "int": "int_theorem_inventory",
}

# Reviewed 2026-08-25 against a `--release` build (docs/autogenesis/
# 263-holdout-contamination-by-ordinary-development.md). Each `expected_line`
# is the EXACT `name<TAB>arity<TAB>type` row `nat_theorem_inventory` /
# `int_theorem_inventory` prints for that theorem; it was copied from a real
# run, not transcribed by hand, so a rendering drift breaks the match instead
# of silently mismatching.
KNOWN_CONTAMINATION: list[dict[str, str]] = [
    {
        "fact_id": "F:ml430-nat-choose-zero-right-1ed2802a",
        "prelude": "nat",
        "kernel_name": "Nat.choose_zero_right",
        "expected_line": (
            "Nat.choose_zero_right\t1\t((x0 : AxNat) -> Eq.{1} AxNat "
            "(AxNat.choose x0 AxNat.zero) (AxNat.succ AxNat.zero))"
        ),
    },
    {
        "fact_id": "F:ml430-nat-choose-self-25bb9fb8",
        "prelude": "nat",
        "kernel_name": "Nat.choose_self",
        "expected_line": (
            "Nat.choose_self\t1\t((x0 : AxNat) -> Eq.{1} AxNat "
            "(AxNat.choose x0 x0) (AxNat.succ AxNat.zero))"
        ),
    },
    {
        "fact_id": "F:ml430-nat-choose-succ-succ-671856b6",
        "prelude": "nat",
        "kernel_name": "Nat.choose_succ_succ",
        "expected_line": (
            "Nat.choose_succ_succ\t2\t((x0 : AxNat) -> ((x1 : AxNat) -> "
            "Eq.{1} AxNat (AxNat.choose (AxNat.succ x0) (AxNat.succ x1)) "
            "(AxNat.add (AxNat.choose x0 x1) (AxNat.choose x0 (AxNat.succ x1)))))"
        ),
    },
    {
        "fact_id": "F:ml430-nat-choose-zero-succ-62c6520b",
        "prelude": "nat",
        "kernel_name": "Nat.zero_choose_succ",
        "expected_line": (
            "Nat.zero_choose_succ\t1\t((x0 : AxNat) -> Eq.{1} AxNat "
            "(AxNat.choose AxNat.zero (AxNat.succ x0)) AxNat.zero)"
        ),
    },
    {
        # Not in the doc-263 table (which pinned a lower bound of 4): this is
        # the 5th, found while building this detector's reviewed table by
        # re-checking every `choose`-family candidate `nat_theorem_inventory`
        # surfaced, not just the four already reported.
        "fact_id": "F:ml430-nat-choose-succ-self-e396f6c2",
        "prelude": "nat",
        "kernel_name": "Nat.choose_succ_self_eq_zero",
        "expected_line": (
            "Nat.choose_succ_self_eq_zero\t1\t((x0 : AxNat) -> Eq.{1} AxNat "
            "(AxNat.choose x0 (AxNat.succ x0)) AxNat.zero)"
        ),
    },
]


class ContaminationDetectorError(Exception):
    """The detector's own infrastructure failed; no finding was possible."""


RunFn = Callable[[str, str], "subprocess.CompletedProcess[str]"]


def run_inventory(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
    example = EXAMPLE_BY_PRELUDE[prelude]
    try:
        return subprocess.run(
            [
                "cargo", "run", "-q", "--release",
                "-p", "axeyum-lean-kernel", "--example", example,
                "--", name_filter,
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=1800,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ContaminationDetectorError(f"cargo invocation failed: {error}") from error


def held_out_entries(nursery: dict[str, Any]) -> list[dict[str, Any]]:
    entries = nursery.get("entries")
    if not isinstance(entries, list):
        raise ContaminationDetectorError("nursery manifest has no entries")
    held = [e for e in entries if isinstance(e, dict) and e.get("partition") == "held-out"]
    if not held:
        raise ContaminationDetectorError(
            "the held-out population is empty; this detector would report vacuously"
        )
    return held


def held_out_everywhere() -> list[dict[str, Any]]:
    """Every held-out row, from BOTH manifests, each required to contribute.

    Deliberately not a loop over "whatever manifests exist": a third manifest
    landing without this function being updated should be a visible omission,
    and a manifest that has stopped carrying held-out rows is an error rather
    than a quiet halving of the population.
    """
    rows: list[dict[str, Any]] = []
    for path in (NURSERY, EXTENSION):
        rows += held_out_entries(load_nursery(path))
    return rows


def load_nursery(path: pathlib.Path) -> dict[str, Any]:
    if not path.is_file():
        raise ContaminationDetectorError(f"nursery manifest is missing: {path}")
    try:
        manifest = json.loads(path.read_text())
    except json.JSONDecodeError as error:
        raise ContaminationDetectorError(f"nursery manifest is unreadable: {error}") from error
    if not isinstance(manifest, dict):
        raise ContaminationDetectorError("nursery manifest is not an object")
    return manifest


def check_known(
    held_out_ids: set[str], run: RunFn | None = None
) -> tuple[list[dict[str, str]], list[str]]:
    """Re-derive each reviewed row against a fresh kernel build.

    Returns (contaminated_rows, skipped_ids) -- a row is skipped, not checked,
    if it names a fact id that is no longer in the held-out population (e.g.
    already amended out), so this table does not itself fabricate a held-out
    reference once a row graduates.

    `run` defaults to `None` rather than to `run_inventory` directly: a
    default *argument value* is bound once, at function-definition time, so a
    caller (or a test) that monkeypatches the module-level `run_inventory`
    name afterwards would silently keep calling the ORIGINAL function. Looking
    it up inside the body instead resolves the module global at CALL time.
    """
    if run is None:
        run = run_inventory
    contaminated: list[dict[str, str]] = []
    skipped: list[str] = []
    for row in KNOWN_CONTAMINATION:
        if row["fact_id"] not in held_out_ids:
            skipped.append(row["fact_id"])
            continue
        result = run(row["prelude"], row["kernel_name"])
        lines = result.stdout.splitlines()
        if row["expected_line"] in lines:
            contaminated.append(row)
    return contaminated, skipped


def word_set(text: str) -> frozenset[str]:
    return frozenset(w for w in text.replace("-", "_").split("_") if w)


def candidate_sweep(
    held_out: list[dict[str, Any]],
    reviewed_ids: set[str],
    run: RunFn | None = None,
) -> list[tuple[str, str]]:
    """Advisory name-level candidates for held-out facts not already reviewed.

    A held-out fact_id like `F:ml430-nat-choose-le-add-9c463139` is sliced to
    its slug (`choose-le-add`) and compared, as a WORD SET (order-independent,
    which is what catches `choose-zero-succ` vs kernel `zero_choose_succ`),
    against every declared theorem name. It is a candidate generator, not a
    verdict: per the doc-263 audit, most candidates it would surface are
    refuted by statement comparison, which a human still has to do.

    **SUBSET, not equality, since 2026-08-30.** The rule was
    `word_set(short) == slug_words`, which requires the kernel theorem to be
    named with EXACTLY the ledger slug's words -- so a proof of the same
    proposition under a longer, more specific name is invisible. That is the
    `natural-parity` contamination precisely: `F:ml430-nat-even-iff-024826e9`
    has slug words `{even, iff}` and the admitted theorem is
    `Nat.even_iff_mod_two_eq_zero`, `{even, iff, mod, two, eq, zero}`. Not
    equal, so not flagged; a strict superset, so flagged now.

    The cost was measured before changing it, over the 136-row pre-amendment
    population against the committed 2,383-name environment snapshot:

        equality  ->   9 rows flagged,  9 (row, name) pairs
        subset    ->  15 rows flagged, 34 (row, name) pairs

    Six extra rows and 25 extra pairs of ADVISORY `needs-review` output, for a
    detector whose own docstring says most candidates are refuted by hand. That
    is the right side of the trade for a population of 116. It would not be at
    ten times the size, and the number to re-measure is the pair count, not the
    row count.

    The direction matters and the other one is wrong: `slug_words <=
    name_words` means "the kernel name says at least what the ledger row says".
    The reverse (`name_words <= slug_words`) would flag every kernel theorem
    whose name is a fragment of the row's -- `Nat.even` for `even-add-one` --
    which is noise with no mechanism behind it.

    Still blind, by construction, to a proposition proved under a name sharing
    NO word with the slug, and to an inline step that has no declaration name
    at all. And blind to a `Definition` in either rule, because it reads a
    THEOREM inventory: see `check-holdout-closed-evaluation.py` for the shape
    this cannot reach.

    `run` defaults to `None`, not `run_inventory`, for the same late-binding
    reason `check_known` does -- see its docstring.
    """
    if run is None:
        run = run_inventory
    prelude_dumps: dict[str, list[str]] = {}
    for prelude in EXAMPLE_BY_PRELUDE:
        result = run(prelude, "")
        prelude_dumps[prelude] = [
            line.split("\t", 1)[0] for line in result.stdout.splitlines() if "\t" in line
        ]

    candidates: list[tuple[str, str]] = []
    for entry in held_out:
        fact_id = entry.get("fact_id", "")
        if fact_id in reviewed_ids:
            continue
        # F:ml430-nat-choose-le-add-9c463139 -> choose-le-add
        parts = fact_id.split("-")
        if len(parts) < 2:
            continue
        slug = "-".join(parts[2:-1]) if parts[0].startswith("F:ml430") else "-".join(parts[1:])
        slug_words = word_set(slug)
        if not slug_words:
            continue
        for prelude, names in prelude_dumps.items():
            for name in names:
                short = name.rsplit(".", 1)[-1]
                if slug_words <= word_set(short):
                    candidates.append((fact_id, f"{prelude}:{name}"))
    return candidates


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--no-candidates",
        action="store_true",
        help="skip the advisory name-level candidate sweep (reviewed-table check only)",
    )
    args = parser.parse_args(argv)

    try:
        held = held_out_everywhere()
        held_ids = {e["fact_id"] for e in held}
        contaminated, skipped = check_known(held_ids)
        candidates: list[tuple[str, str]] = []
        if not args.no_candidates:
            reviewed_ids = {row["fact_id"] for row in KNOWN_CONTAMINATION}
            candidates = candidate_sweep(held, reviewed_ids)
    except ContaminationDetectorError as error:
        print(f"AUTOGENESIS_HOLDOUT_CONTAMINATION_ERROR|{error}", file=sys.stderr)
        return 1

    verdict = "CONTAMINATED" if contaminated else "CLEAN"
    print(
        "AUTOGENESIS_HOLDOUT_CONTAMINATION|"
        f"held_out={len(held)}|reviewed={len(KNOWN_CONTAMINATION)}|"
        f"contaminated={len(contaminated)}|skipped={len(skipped)}|"
        f"candidates={len(candidates)}|verdict={verdict}"
    )
    for row in contaminated:
        print(f"  contaminated|{row['fact_id']}|{row['kernel_name']}")
    for fact_id in skipped:
        print(f"  skipped-not-held-out|{fact_id}", file=sys.stderr)
    for fact_id, name in candidates:
        print(f"  needs-review|{fact_id}|{name}", file=sys.stderr)
    if contaminated:
        print(
            "contamination found is NOT a build failure -- see docs/autogenesis/"
            "263-holdout-contamination-by-ordinary-development.md. Confirm the "
            "affected family is already amended in "
            "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json (ADR-0542); "
            "if not, that is the next step, not this gate.",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
