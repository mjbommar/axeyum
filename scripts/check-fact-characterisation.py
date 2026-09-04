#!/usr/bin/env python3
"""Report and ratchet how much of the fact ledger CHARACTERISES itself (ADR-1605).

WHY THIS EXISTS. Twelve persona reviews of the library
(`docs/math-department/`) were written on 2026-09-04 by reading the fact
ledger. `docs/math-department/AUDIT-2026-09-04.md` re-checked every claim of
absence in them against the kernel and found **11 false** -- eleven things the
reviews say are missing that are proved, seven of them landed in a single day
one week before the reviews. The cause is not carelessness. It is that the
ledger cannot distinguish *"no prose has been written"* from *"there is nothing
here."*

The generator's refusal to characterise is CORRECT and is why the ledger is
trustworthy: `gen-kernel-facts.py` writes, verbatim, "MECHANICALLY GENERATED,
UNREVIEWED PROSE -- this sentence deliberately makes NO mathematical
characterisation of the theorem" rather than guessing at meaning. The defect is
that nothing marks the difference at the point where somebody reads it.

WHAT THIS ADDS OVER `count-landmark-facts.py`. That script splits the ledger
two ways -- `[generated]` or not -- and counts the second half as landmarks.
This one splits it THREE ways, and the third class is load-bearing:

  * `curated`     -- a title written by whoever proved it, saying what the fact IS.
  * `generated`   -- the generator's `[generated]` prefix. Says which declaration
                     backs it and deliberately nothing more.
  * `transcribed` -- "Mathlib v4.30 source proposition <Name>". Characterises by
                     REFERENCE to an external name and adds nothing of its own.

The landmark rule counts a `transcribed` title as characterised. Measured
2026-09-04, that is 499 proved facts, and it is exactly where one of the
audit's false absences hid: `07-combinatorics.md` reports "no Stirling
numbers" while `Nat.stirlingFirst` and `Nat.stirlingSecond` carry TEN proved
facts -- every one of them titled "Mathlib v4.30 source proposition
Nat.stirlingFirst_...". A reader scanning titles for "Stirling numbers" sees
nothing; a reader who already knows the Mathlib name does not need the ledger.

So the headline this script reports and the landmark script cannot:
**1,554 of 2,493 proved facts (62.3%) carry no mathematical characterisation of
their own.**

WHY A RATCHET AND NOT A PIN. `count-landmark-facts.py --check` pins four
counts to exact equality. Measured on `main` at `182d0dd7d`, it was RED --
`baseline=2758 measured=2764` -- because six facts landed and nobody bumped a
generated file. An exact pin goes red on every legitimate addition, which
trains lanes to re-baseline reflexively and is how a pin stops being read. The
guard here is directional instead: the count of CURATED proved facts, per
fragment, may never FALL. Characterisation is monotone; adding uncharacterised
facts is allowed (the autogenesis producer must be able to run), removing
characterisation is not.

USAGE.

    python3 scripts/check-fact-characterisation.py            # the report
    python3 scripts/check-fact-characterisation.py --report   # same, explicit
    python3 scripts/check-fact-characterisation.py --json     # report as JSON
    python3 scripts/check-fact-characterisation.py --check    # guards + ratchet
    python3 scripts/check-fact-characterisation.py --write-baseline
    python3 scripts/check-fact-characterisation.py --facts-dir DIR --baseline PATH

EXIT STATUS. Depends on the finding, never merely on completing:

  * 2 -- MALFORMED. A fact file is not valid JSON, or is missing a field this
    script reads (`title`, `statement`, `epistemic_status`). Applies to EVERY
    mode including a bare report, because a report over a ledger this script
    could not fully read is not a measurement.
  * 1 -- PROSE_DISAGREEMENT. A fact's title and statement disagree about
    whether its prose is generated: a `[generated]` title whose statement does
    not carry the generator's marker, or the marker in a statement under a
    title that does not say so. Either way a reader is told one thing by the
    title and another by the body. This guard found exactly one violation on
    its first honest run -- `F-int-euler-totient-theorem.json`, whose statement
    is a full curated characterisation of Euler's totient theorem sitting under
    a "prose not curated" title, so both this script and the landmark count
    scored a characterised fact as uncharacterised. Applies in every mode.
  * 1 -- CHARACTERISATION_REGRESSION (`--check` only). Some fragment's curated
    proved count fell below the committed baseline.
  * 0 -- otherwise.

A bare report can therefore still exit nonzero; it is not a mode in which
nothing can fail.

NOT GATED HERE, AND SIZED IN ADR-1605. The second and larger axis is that 430
kernel THEOREMS and 762 of 789 kernel DEFINITIONS have no ledger fact at all --
including `AlgS.Hom.firstIso`, the headline result of `04-algebra.md`. That
measurement needs the kernel declaration index, which is a ~2.5-minute
`--release` build, so it is not a per-commit gate and is not attempted here.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

DEFAULT_FACTS_DIR = "artifacts/facts"
DEFAULT_BASELINE = "scripts/fact-characterisation-baseline.json"

GENERATED_PREFIX = "[generated]"
TRANSCRIBED_PREFIX = "Mathlib v4.30 source proposition"
# The generator's own disclaimer, verbatim. Not a label this script invents:
# grep it under artifacts/facts/ to see it.
GENERATED_MARKER = "MECHANICALLY GENERATED, UNREVIEWED PROSE"

PROVED = "proved"
CLASSES = ("curated", "generated", "transcribed")

# Only fragments at or above this many curated proved facts get their own floor
# in the baseline. The ledger carries ~45 one-fact CAS/solver fragments; giving
# each a floor would make the baseline a 60-line file that every lane touching
# a CAS fact has to edit -- the shared-append-point shape this repository has
# lost content to four times. The total floor still covers them collectively.
MIN_FRAGMENT_FLOOR = 10

REQUIRED_FIELDS = ("title", "statement", "epistemic_status")


class LedgerMalformed(Exception):
    """A fact file could not be read as this script's measurement requires."""

    def __init__(self, path: Path, reason: str) -> None:
        super().__init__(f"{path}: {reason}")
        self.path = path
        self.reason = reason


def load_facts(facts_dir: Path) -> list[tuple[Path, dict]]:
    """Read every fact. Raises LedgerMalformed rather than skipping a bad file.

    Skipping would make a shrinking ledger indistinguishable from a healthy
    one, which is the failure this whole script exists to name.
    """
    out: list[tuple[Path, dict]] = []
    for path in sorted(facts_dir.glob("*.json")):
        try:
            fact = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise LedgerMalformed(path, f"unreadable JSON ({exc})") from exc
        if not isinstance(fact, dict):
            raise LedgerMalformed(path, "top level is not an object")
        for field in REQUIRED_FIELDS:
            if not isinstance(fact.get(field), str):
                raise LedgerMalformed(path, f"missing or non-string {field!r}")
        out.append((path, fact))
    return out


def classify(fact: dict) -> str:
    """Three-way characterisation class of a fact's TITLE."""
    title = fact["title"].strip()
    if title.startswith(GENERATED_PREFIX):
        return "generated"
    if title.startswith(TRANSCRIBED_PREFIX):
        return "transcribed"
    return "curated"


def prose_disagreements(facts: list[tuple[Path, dict]]) -> list[str]:
    """Facts whose title and statement disagree about generated-ness."""
    bad: list[str] = []
    for path, fact in facts:
        title_says = fact["title"].strip().startswith(GENERATED_PREFIX)
        body_says = GENERATED_MARKER in fact["statement"]
        if title_says and not body_says:
            bad.append(f"{path.name}: [generated] title, no generator marker in statement")
        elif body_says and not title_says:
            bad.append(f"{path.name}: generator marker in statement, title does not say so")
    return bad


def fragment_of(fact: dict) -> str:
    formal = fact.get("formal")
    if isinstance(formal, dict):
        frag = formal.get("fragment")
        if isinstance(frag, str) and frag:
            return frag
    return "(none)"


def measure(facts: list[tuple[Path, dict]]) -> dict:
    overall = Counter()
    proved = Counter()
    curated_by_fragment = Counter()
    for _path, fact in facts:
        cls = classify(fact)
        overall[cls] += 1
        if fact["epistemic_status"] == PROVED:
            proved[cls] += 1
            if cls == "curated":
                curated_by_fragment[fragment_of(fact)] += 1
    total = sum(overall.values())
    proved_total = sum(proved.values())
    uncharacterised = proved["generated"] + proved["transcribed"]
    return {
        "total": total,
        "proved": proved_total,
        "all": {c: overall[c] for c in CLASSES},
        "proved_by_class": {c: proved[c] for c in CLASSES},
        "uncharacterised_proved": uncharacterised,
        "uncharacterised_share": (uncharacterised / proved_total) if proved_total else 0.0,
        "curated_proved_by_fragment": dict(sorted(curated_by_fragment.items())),
    }


def format_report(m: dict) -> str:
    lines = [
        "FACT_CHARACTERISATION"
        f"|total={m['total']}"
        f"|proved={m['proved']}"
        f"|curated={m['proved_by_class']['curated']}"
        f"|generated={m['proved_by_class']['generated']}"
        f"|transcribed={m['proved_by_class']['transcribed']}"
        f"|uncharacterised_proved={m['uncharacterised_proved']}"
        f"|uncharacterised_share={m['uncharacterised_share']:.4f}",
    ]
    lines.append("curated proved facts, by fragment:")
    for frag, n in sorted(m["curated_proved_by_fragment"].items(), key=lambda kv: (-kv[1], kv[0])):
        lines.append(f"  {frag:<16} {n}")
    return "\n".join(lines)


def run_check(m: dict, baseline_path: Path) -> int:
    """`--check`: the curated-per-fragment ratchet. Returns exit status."""
    if not baseline_path.exists():
        print(
            f"FACT_CHARACTERISATION_CHECK|verdict=FAIL|reason=BASELINE_MISSING|path={baseline_path}",
            file=sys.stderr,
        )
        return 1
    try:
        baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(
            f"FACT_CHARACTERISATION_CHECK|verdict=FAIL|reason=BASELINE_UNPARSEABLE"
            f"|path={baseline_path}|detail={exc}",
            file=sys.stderr,
        )
        return 1

    want = baseline.get("curated_proved_by_fragment")
    if not isinstance(want, dict):
        print(
            f"FACT_CHARACTERISATION_CHECK|verdict=FAIL|reason=BASELINE_UNPARSEABLE"
            f"|path={baseline_path}|detail=curated_proved_by_fragment missing",
            file=sys.stderr,
        )
        return 1

    got = m["curated_proved_by_fragment"]
    regressions = []
    for frag, floor in sorted(want.items()):
        have = got.get(frag, 0)
        if have < floor:
            regressions.append(f"{frag}: baseline>={floor} measured={have}")

    total_floor = baseline.get("curated_proved_total")
    if isinstance(total_floor, int):
        total_have = sum(got.values())
        if total_have < total_floor:
            regressions.append(f"(total): baseline>={total_floor} measured={total_have}")

    if regressions:
        print(
            "FACT_CHARACTERISATION_CHECK|verdict=FAIL|reason=CHARACTERISATION_REGRESSION|"
            + ";".join(regressions),
            file=sys.stderr,
        )
        return 1
    print(f"FACT_CHARACTERISATION_CHECK|verdict=OK|baseline={baseline_path}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--facts-dir", default=DEFAULT_FACTS_DIR)
    parser.add_argument("--baseline", default=DEFAULT_BASELINE)
    parser.add_argument("--report", action="store_true", help="print the report (default)")
    parser.add_argument("--json", action="store_true", help="print the measurement as JSON")
    parser.add_argument("--check", action="store_true", help="run the curated-count ratchet")
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="rewrite the baseline from the current measurement",
    )
    args = parser.parse_args(argv)

    try:
        facts = load_facts(Path(args.facts_dir))
    except LedgerMalformed as exc:
        print(
            f"FACT_CHARACTERISATION|verdict=FAIL|reason=MALFORMED|path={exc.path}|detail={exc.reason}",
            file=sys.stderr,
        )
        return 2

    disagreements = prose_disagreements(facts)
    m = measure(facts)

    if args.json:
        print(json.dumps(m, indent=2, sort_keys=True))
    elif not args.write_baseline:
        print(format_report(m))

    if disagreements:
        print(
            "FACT_CHARACTERISATION|verdict=FAIL|reason=PROSE_DISAGREEMENT|"
            f"count={len(disagreements)}|" + ";".join(disagreements[:10]),
            file=sys.stderr,
        )
        return 1

    if args.write_baseline:
        floors = {
            frag: n
            for frag, n in m["curated_proved_by_fragment"].items()
            if n >= MIN_FRAGMENT_FLOOR
        }
        payload = {
            "curated_proved_by_fragment": floors,
            "curated_proved_total": sum(m["curated_proved_by_fragment"].values()),
            "observed_proved": m["proved"],
            "observed_uncharacterised_proved": m["uncharacterised_proved"],
        }
        Path(args.baseline).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(f"FACT_CHARACTERISATION|wrote={args.baseline}")
        return 0

    if args.check:
        return run_check(m, Path(args.baseline))
    return 0


if __name__ == "__main__":
    sys.exit(main())
