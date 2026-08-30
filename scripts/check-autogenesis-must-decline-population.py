#!/usr/bin/env python3
"""Void a producer census that admits a statement which must be declined.

This repository's signature discipline is that a checker whose exit status
does not depend on its finding is worse than no checker (see CLAUDE.md, "40 of
162 checker runs ... exit 0 on completion alone"). That discipline has never
been applied to PRODUCERS: every producer census run over this nursery has
been evaluated only on statements that are TRUE, so a producer that admitted
*anything at all* would have looked successful. There was no statement in the
evaluation population marked "this MUST be declined".

`artifacts/autogenesis/nursery-v1.json` contains 12 rows with
`provenance_class: generated-mutation` -- deliberately corrupted variants of
real, proved Mathlib propositions. Ten of them sit in the train/development
partitions (the other two are held-out and are never referenced here or
anywhere else outside the two files that define that population -- see
`scripts/check-autogenesis-holdout-isolation.py`). Every one of those ten is
FALSE, each by a concrete, hand-checkable counterexample:
`artifacts/autogenesis/must-decline-mutations-v1.json` records the witness and
this script independently RECOMPUTES it -- the JSON is not trusted on its own.

This gate has two jobs, and both must depend on what they find:

1.  The ground-truth artifact must exactly name the must-decline population
    (derived fresh from the nursery, not hand-copied) and every recorded
    counterexample must actually refute its statement when recomputed by a
    small bounded evaluator below. A wrong or stale ground-truth artifact is a
    hard failure, not a warning.
2.  A producer census (default: the existing
    `mathlib-reflexivity-coverage-v1.json`, the actual census this repository
    runs today) must not list any must-decline fact id among its admissible /
    admitted proofs. If it does, the whole census is VOID: a producer that
    admits a false statement is a soundness failure, not a low conversion
    rate, and nothing else the census reports can be trusted.

FAIL-CLOSED throughout: a missing or unreadable nursery, ground-truth artifact,
or census file is an error, never a silent pass; an empty must-decline
population is an error (a gate with an empty subject cannot fail, which is the
exact defect this gate exists to avoid reproducing one arrow downstream).
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
GROUND_TRUTH = ROOT / "artifacts/autogenesis/must-decline-mutations-v1.json"
FACTS = ROOT / "artifacts/facts"
CENSUS = ROOT / "artifacts/autogenesis/mathlib-reflexivity-coverage-v1.json"


class MustDeclineError(Exception):
    """The must-decline population, its ground truth, or a census is invalid."""


# ---------------------------------------------------------------------------
# Bounded ground-truth evaluator. Every function is a direct, elementary
# Nat/Int computation on concrete numerals -- deliberately not clever, so the
# counterexamples it certifies are checkable by hand (0! = 1, fib(1) = 1,
# gcd(0, 0) = 0, 1 % 2 != 0 % 2, ...).
# ---------------------------------------------------------------------------


def nat_fib(n: int) -> int:
    if n < 0:
        raise MustDeclineError("nat_fib: negative argument")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def nat_factorial(n: int) -> int:
    if n < 0:
        raise MustDeclineError("nat_factorial: negative argument")
    result = 1
    for k in range(2, n + 1):
        result *= k
    return result


def nat_choose(n: int, k: int) -> int:
    if n < 0 or k < 0:
        raise MustDeclineError("nat_choose: negative argument")
    if k > n:
        return 0
    k = min(k, n - k)
    result = 1
    for i in range(1, k + 1):
        result = result * (n - k + i) // i
    return result


def nat_gcd(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def nat_log(b: int, n: int) -> int:
    """Mathlib `Nat.log b n`: the greatest `k` with `b^k <= n`.

    Zero when `b <= 1` or `n < b` -- including `Nat.log b 0 = 0` for every `b`,
    which is the whole counterexample for the strengthened-conclusion mutation.
    """
    if b < 0 or n < 0:
        raise MustDeclineError("nat_log: negative argument")
    if b <= 1 or n < b:
        return 0
    k, value = 0, 1
    while value * b <= n:
        value *= b
        k += 1
    return k


def nat_pred(n: int) -> int:
    return n - 1 if n > 0 else 0


def is_prime(p: int) -> bool:
    if p < 2:
        return False
    k = 2
    while k * k <= p:
        if p % k == 0:
            return False
        k += 1
    return True


CHECKS = {
    "fib_widened": lambda w: nat_fib(w["n"]) != 0 and w["n"] in (0, 1),
    "gcd_conclusion_strengthened": lambda w: (
        nat_gcd(w["x"], w["y"]) != 0 and not (w["x"] != 0 and w["y"] != 0)
    ),
    "prime_pred_bound_strengthened": lambda w: (
        is_prime(w["p"]) and not (nat_pred(w["p"]) > 1)
    ),
    "factorial_polarity_reversed": lambda w: nat_factorial(w["n"]) != 0,
    "choose_self_polarity_reversed": lambda w: nat_choose(w["n"], w["n"]) != 0,
    "bitwise_operator_substituted": lambda w: (w["n"] | w["m"]) != (w["n"] & w["m"]),
    "modeq_premise_removed": lambda w: (w["a"] % w["n"]) != (w["b"] % w["n"]),
    "coprime_polarity_reversed": lambda w: nat_gcd(w["a"], w["b"]) != 1,
    # `Nat.log b n <= n` strengthened to `<`. Refuted wherever `n = 0`:
    # `Nat.log b 0 = 0` for every `b`, and `0 < 0` is false.
    "log_conclusion_strengthened": lambda w: not (nat_log(w["b"], w["x"]) < w["x"]),
}


# ---------------------------------------------------------------------------
# Loading and validation
# ---------------------------------------------------------------------------


def load_json(path: pathlib.Path, label: str) -> dict[str, Any]:
    if not path.is_file():
        raise MustDeclineError(f"{label} is missing: {path}")
    try:
        value = json.loads(path.read_text())
    except json.JSONDecodeError as error:
        raise MustDeclineError(f"{label} is unreadable: {error}") from error
    if not isinstance(value, dict):
        raise MustDeclineError(f"{label} is not a JSON object: {path}")
    return value


def compute_must_decline(nursery: dict[str, Any]) -> set[str]:
    entries = nursery.get("entries")
    if not isinstance(entries, list):
        raise MustDeclineError("nursery manifest has no entries")
    must_decline = {
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict)
        and entry.get("provenance_class") == "generated-mutation"
        and entry.get("partition") != "held-out"
        and isinstance(entry.get("fact_id"), str)
    }
    if not must_decline:
        raise MustDeclineError(
            "the must-decline population is empty; this gate would pass "
            "vacuously -- a producer census with nothing it MUST decline "
            "cannot be shown to have earned a success"
        )
    return must_decline


def validate_ground_truth_population(
    ground_truth: dict[str, Any], must_decline: set[str]
) -> list[dict[str, Any]]:
    entries = ground_truth.get("entries")
    if not isinstance(entries, list) or not entries:
        raise MustDeclineError("ground-truth artifact has no entries")
    recorded = {
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict) and isinstance(entry.get("fact_id"), str)
    }
    extra = sorted(recorded - must_decline)
    if extra:
        raise MustDeclineError(
            "ground-truth artifact names fact id(s) outside the current "
            f"must-decline population (stale or held-out leakage): {extra}"
        )
    missing = sorted(must_decline - recorded)
    if missing:
        raise MustDeclineError(
            "ground-truth artifact is missing fact id(s) from the current "
            f"must-decline population: {missing}"
        )
    return entries


def verify_counterexamples(entries: list[dict[str, Any]]) -> None:
    for entry in entries:
        fact_id = entry.get("fact_id", "<unknown>")
        check_kind = entry.get("check_kind")
        fn = CHECKS.get(check_kind)
        if fn is None:
            raise MustDeclineError(
                f"{fact_id}: unrecognized check_kind {check_kind!r}"
            )
        witness = entry.get("witness")
        if not isinstance(witness, dict):
            raise MustDeclineError(f"{fact_id}: witness is not an object")
        try:
            refuted = bool(fn(witness))
        except (KeyError, MustDeclineError) as error:
            raise MustDeclineError(
                f"{fact_id}: witness {witness} could not be evaluated: {error}"
            ) from error
        if not refuted:
            raise MustDeclineError(
                f"{fact_id}: witness {witness} does NOT refute the statement "
                "under independent recomputation -- the ground-truth entry is wrong"
            )


def load_census(path: pathlib.Path) -> list[Any]:
    census = load_json(path, "census")
    admissible = census.get("admissible_proofs")
    if not isinstance(admissible, list):
        raise MustDeclineError(
            f"census at {path} has no 'admissible_proofs' list; its schema is "
            "not recognized by this gate, and an unrecognized census cannot be "
            "shown clean"
        )
    return admissible


SETTLED = {"proved", "computed"}


def scan_ledger(must_decline: set[str], facts_dir: pathlib.Path) -> list[str]:
    """A must-decline fact must never be SETTLED in the ledger.

    `scan_census` guards the census; nothing guarded the ledger, and the two are
    different doors into the same room. Measured 2026-08-22 by mutation: marking
    the known-false `n! = 0` as `proved` with a forged-but-well-formed evidence
    row passed `validate-facts.py`, this gate, the held-out isolation gate and the
    nursery gate -- four green checks over a statement refuted by `0! = 1`.

    A false theorem admitted to the ledger is the worst outcome this project has,
    strictly worse than a wrong `sat`: it is durable, it is cited by dependents,
    and every downstream axiom-freedom claim inherits it.
    """
    violations = []
    for fact_id in sorted(must_decline):
        path = facts_dir / (fact_id.replace("F:", "F-") + ".json")
        if not path.is_file():
            continue
        status = json.loads(path.read_text()).get("epistemic_status")
        if status in SETTLED:
            violations.append(f"{fact_id} is {status} in the ledger")
    return violations


def scan_census(admissible: list[Any], must_decline: set[str]) -> list[str]:
    violations = []
    for row in admissible:
        if isinstance(row, dict) and row.get("fact_id") in must_decline:
            violations.append(row["fact_id"])
    return violations


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nursery", type=pathlib.Path, default=NURSERY)
    parser.add_argument("--ground-truth", type=pathlib.Path, default=GROUND_TRUTH)
    parser.add_argument("--census", type=pathlib.Path, default=CENSUS)
    parser.add_argument("--facts-dir", type=pathlib.Path, default=FACTS)
    args = parser.parse_args(argv)

    try:
        nursery = load_json(args.nursery, "nursery manifest")
        must_decline = compute_must_decline(nursery)
        ground_truth = load_json(args.ground_truth, "ground-truth artifact")
        entries = validate_ground_truth_population(ground_truth, must_decline)
        verify_counterexamples(entries)
        admissible = load_census(args.census)
        violations = scan_census(admissible, must_decline)
        ledger_violations = scan_ledger(must_decline, args.facts_dir)
    except MustDeclineError as error:
        print(f"AUTOGENESIS_MUST_DECLINE_CENSUS_ERROR|{error}", file=sys.stderr)
        return 1

    verdict = "FAIL" if violations or ledger_violations else "PASS"
    print(
        f"AUTOGENESIS_MUST_DECLINE_CENSUS|must_decline={len(must_decline)}|"
        f"ground_truth_verified={len(entries)}|census={args.census.name}|"
        f"admissible_total={len(admissible)}|violations={len(violations)}|"
        f"ledger_violations={len(ledger_violations)}|"
        f"verdict={verdict}"
    )
    for item in ledger_violations:
        print(
            f"  must-decline-fact-settled|{item} -- a statement refuted by a "
            "recorded counterexample is marked settled in the ledger. A false "
            "theorem admitted here is durable, is inherited by every dependent, "
            "and is strictly worse than a wrong `sat`.",
            file=sys.stderr,
        )
    for fact_id in violations:
        print(
            f"  must-decline-fact-admitted|{fact_id} appears in "
            f"{args.census.name}'s admissible_proofs -- a false statement was "
            "admitted, so this census is VOID",
            file=sys.stderr,
        )
    return 1 if violations or ledger_violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
