#!/usr/bin/env python3
"""Count landmark facts beside the raw total (W1-4, roadmap C6/12.3).

WHY THIS EXISTS. `python3 scripts/validate-facts.py` reports "2,487 proved" as
a single number, and the chair's review (`docs/math-department/12-the-chair.md`)
names the objection directly: a generated congruence lemma and quadratic
reciprocity are one row each in that total, and the first hostile reviewer will
say so. This script reports a SECOND, stricter number beside the first one,
derived from a stated, checkable rule rather than asserted in prose.

THE RULE. A fact is a **landmark** iff:

    epistemic_status == "proved"
      AND  title does not start with "[generated]"
      AND  proof_route is not one this project did not author alone

The third clause is ADR-1664 rule 5 and was added on 2026-09-05, when it was
measured that ALL SEVEN `imported-kernel-lean` facts had been counted as
landmarks -- Mathlib's Intermediate Value Theorem and Extreme Value Theorem
among them. Seven of 1,523 does not move a headline, but they are exactly the
rows ADR-0601 calls "labeled scaffolding, never headline", and a landmark count
that includes a theorem Mathlib proved is not measuring what the paragraph above
says it measures. `kernel-lean-over-import` (an originated proof term resting on
an import) is excluded for the weaker reason that it belongs to ADR-1664's
separately reported composed tier. The measured effect of the clause is
`landmark` 1,523 -> 1,516 and a new `imported=7` field in the summary line.

`[generated]` is not a label this script invents: it is the literal prefix an
existing production pass writes into `title` for a fact whose `statement` is,
verbatim, "MECHANICALLY GENERATED, UNREVIEWED PROSE -- this sentence
deliberately makes NO mathematical characterisation of the theorem" (see any
file matching that string under `artifacts/facts/`). A generated fact's title
is a template ("[generated] kernel theorem <Name> (<prelude>, axiom-free, prose
not curated)"); a landmark's title was written by whoever proved it, and says
what the fact IS rather than merely which kernel declaration backs it.

WHAT THIS EXCLUDES, DELIBERATELY.

  * `computed` and `conjectured` facts never count, however striking the
    computation: the chair's review names exactly this
    ("Treating `computed` as `proved`") as a claim that must not be made. Only
    `proved` is eligible.
  * `open` and `refuted` facts never count: a landmark is something this
    project ESTABLISHED, not a statement in the ledger.
  * A CURATED but genuinely routine fact (e.g. one instance of `X_comm` on one
    of several carriers) still counts as a landmark under this rule. Curated
    prose is a necessary condition for "somebody characterised this," not a
    sufficient one for "this is important," and this script does not attempt
    the harder, less checkable judgment of importance or novelty. State the
    rule, report the numbers, let a reader disagree with the DEFINITION rather
    than an unstated one.
  * This rule does not deduplicate the same abstract law proved once per
    carrier (Nat/Int/Rat/CReal/Complex `_comm`, `_assoc`, ...). A landmark
    count that collapsed those would need a second, harder-to-verify axis
    (grouping by underlying law); left as future work rather than attempted
    here under the checker-that-cannot-fail discipline this repository holds
    every gate to.

USAGE.

    python3 scripts/count-landmark-facts.py                  # print the summary
    python3 scripts/count-landmark-facts.py --json            # summary as JSON
    python3 scripts/count-landmark-facts.py --check            # compare to the
                                                                 # committed baseline
    python3 scripts/count-landmark-facts.py --facts-dir DIR --baseline PATH

EXIT STATUS. Depends on the finding, not merely on completion:

  * 2 -- the ledger is malformed (a fact file is not valid JSON, or is missing
    a field this script depends on: `epistemic_status` or `title`). This is a
    DIFFERENT failure from a landmark-count mismatch, and is reported with its
    own tag so the two are never confused.
  * 1 -- (`--check` only) the measured counts disagree with the committed
    baseline. The mismatched fields are named explicitly.
  * 0 -- otherwise.

A run with no `--check` NEVER exits nonzero on a mere count (there is nothing
to compare it to); it can still exit 2 on a malformed ledger. That is
deliberate: "prints a plausible number and exits 0" is exactly the
checker-that-cannot-fail shape this repository's contributor guide warns
against, so the parse/schema guard applies unconditionally and the drift guard
applies only under `--check`.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

DEFAULT_FACTS_DIR = "artifacts/facts"
DEFAULT_BASELINE = "scripts/landmark-facts-baseline.json"
GENERATED_PREFIX = "[generated]"
LANDMARK_STATUS = "proved"

# Routes whose proof term this project did not construct, or did not construct
# alone. ADR-1664 rule 5.
#
# WHY THIS IS HERE. This script read only `epistemic_status` and `title` until
# 2026-09-05, and the omission was not free: measured that day, ALL SEVEN
# `imported-kernel-lean` facts were counted as landmarks, Mathlib's Intermediate
# Value Theorem and Extreme Value Theorem among them. Seven of 1,523 is 0.46 %
# and would not move a headline, but they are exactly the rows ADR-0601 calls
# "labeled scaffolding, never headline", and a landmark count that includes a
# theorem Mathlib proved is not measuring what its own docstring says it
# measures.
#
# `kernel-lean-over-import` is excluded for a weaker but sufficient reason: that
# proof term IS ours, but the result rests on an import, so it belongs to the
# separately reported composed tier rather than to the count a hostile reviewer
# will read as "results this project established".
#
# Read with `.get`, deliberately NOT added to REQUIRED_FIELDS: `proof_route` is
# absent on open facts by design, and making this script fail-closed on that
# would reject a well-formed ledger.
IMPORT_DEPENDENT_ROUTES = frozenset(
    {"imported-kernel-lean", "kernel-lean-over-import"}
)

REQUIRED_FIELDS = ("epistemic_status", "title")


class MalformedLedgerError(Exception):
    """Raised when a fact file cannot be read as the ledger this script needs."""

    def __init__(self, path: Path, reason: str) -> None:
        super().__init__(f"{path}: {reason}")
        self.path = path
        self.reason = reason


def load_facts(facts_dir: Path) -> list[dict]:
    """Load every `*.json` fact under `facts_dir`.

    Raises `MalformedLedgerError` naming the first offending file, on invalid
    JSON or on a fact missing a field this script's counting rule depends on.
    Deliberately fail-closed: a ledger this script cannot fully read is not a
    ledger it will silently under-count.
    """
    paths = sorted(facts_dir.glob("*.json"))
    if not paths:
        raise MalformedLedgerError(facts_dir, "no *.json fact files found")
    facts: list[dict] = []
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise MalformedLedgerError(path, f"could not read file: {exc}") from exc
        try:
            fact = json.loads(text)
        except json.JSONDecodeError as exc:
            raise MalformedLedgerError(path, f"invalid JSON: {exc}") from exc
        if not isinstance(fact, dict):
            raise MalformedLedgerError(path, "top-level JSON value is not an object")
        for field in REQUIRED_FIELDS:
            if field not in fact:
                raise MalformedLedgerError(path, f"missing required field {field!r}")
        facts.append(fact)
    return facts


def is_generated(fact: dict) -> bool:
    """Whether `fact`'s title carries the mechanical-generation marker."""
    title = fact["title"]
    if not isinstance(title, str):
        return False
    return title.startswith(GENERATED_PREFIX)


def rests_on_an_import(fact: dict) -> bool:
    """Whether `fact`'s proof term was authored elsewhere, wholly or in part."""
    return fact.get("proof_route") in IMPORT_DEPENDENT_ROUTES


def is_landmark(fact: dict) -> bool:
    """The landmark rule: proved, not mechanically generated, and ours.

    The third clause is ADR-1664 rule 5, added 2026-09-05. Before it, the rule
    counted a theorem checked here but authored in Mathlib exactly as it counted
    one this project proved.
    """
    return (
        fact["epistemic_status"] == LANDMARK_STATUS
        and not is_generated(fact)
        and not rests_on_an_import(fact)
    )


def count(facts: list[dict]) -> dict:
    """Reduce a fact list to the counters this script reports and gates on."""
    total = len(facts)
    proved = sum(1 for f in facts if f["epistemic_status"] == LANDMARK_STATUS)
    generated = sum(1 for f in facts if is_generated(f))
    imported = sum(1 for f in facts if rests_on_an_import(f))
    landmark = sum(1 for f in facts if is_landmark(f))
    return {
        "total": total,
        "proved": proved,
        "generated": generated,
        "imported": imported,
        "landmark": landmark,
    }


def format_summary(counts: dict) -> str:
    ratio = (counts["landmark"] / counts["proved"]) if counts["proved"] else 0.0
    return (
        "LANDMARK_FACTS"
        f"|total={counts['total']}"
        f"|proved={counts['proved']}"
        f"|generated={counts['generated']}"
        f"|imported={counts['imported']}"
        f"|landmark={counts['landmark']}"
        f"|landmark_of_proved={ratio:.4f}"
    )


def run_check(counts: dict, baseline_path: Path) -> int:
    """`--check`: compare `counts` to the committed baseline. Returns exit status."""
    if not baseline_path.exists():
        print(
            f"LANDMARK_FACTS_CHECK|verdict=FAIL|reason=BASELINE_MISSING|path={baseline_path}",
            file=sys.stderr,
        )
        return 1
    try:
        baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(
            f"LANDMARK_FACTS_CHECK|verdict=FAIL|reason=BASELINE_UNPARSEABLE|path={baseline_path}|detail={exc}",
            file=sys.stderr,
        )
        return 1

    mismatches = []
    for key in ("total", "proved", "generated", "imported", "landmark"):
        want = baseline.get(key)
        got = counts.get(key)
        if want != got:
            mismatches.append(f"{key}: baseline={want} measured={got}")

    if mismatches:
        print(
            "LANDMARK_FACTS_CHECK|verdict=FAIL|reason=DRIFT|"
            + ";".join(mismatches),
            file=sys.stderr,
        )
        return 1

    print(f"LANDMARK_FACTS_CHECK|verdict=OK|baseline={baseline_path}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--facts-dir", default=DEFAULT_FACTS_DIR, help="directory of fact JSON files")
    parser.add_argument("--baseline", default=DEFAULT_BASELINE, help="committed baseline JSON for --check")
    parser.add_argument("--check", action="store_true", help="compare the measured counts to the baseline")
    parser.add_argument("--json", action="store_true", help="print the summary as JSON instead of the pipe line")
    args = parser.parse_args(argv)

    facts_dir = Path(args.facts_dir)
    try:
        facts = load_facts(facts_dir)
    except MalformedLedgerError as exc:
        print(f"LANDMARK_FACTS|verdict=FAIL|reason=MALFORMED_LEDGER|detail={exc}", file=sys.stderr)
        return 2

    counts = count(facts)

    if args.json:
        print(json.dumps(counts, indent=2, sort_keys=True))
    else:
        print(format_summary(counts))

    if args.check:
        return run_check(counts, Path(args.baseline))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
