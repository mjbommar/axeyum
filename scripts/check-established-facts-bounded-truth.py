#!/usr/bin/env python3
"""Bounded-truth net over the facts we have ESTABLISHED.

This repository has a gate that stops a known-false statement from being
admitted (`check-autogenesis-must-decline-population.py`). It has had nothing
pointing the other way: nothing checks that a statement we marked `proved` is
actually TRUE.

Those are different directions and neither implies the other. The must-decline
gate can only see the nine statements someone thought to refute in advance. This
one evaluates what we CLAIM, independently of the kernel that accepted it.

It is deliberately a NET, not a proof. A bounded search finds no counterexample
for a true statement and for a statement that is false only beyond the bound, so
a clean run is weak evidence. What makes it worth running is the failure case:
if the kernel ever accepts a false theorem -- a kernel defect, an import defect,
a mis-transcribed statement -- a counterexample at n < 64 is a loud, cheap,
independent alarm that no amount of kernel self-consistency would raise.

FAIL-CLOSED, in the way this file can actually fail closed:
* a counterexample against an established fact is an ERROR, not a warning;
* zero evaluable facts is an ERROR, because the net would pass vacuously;
* a statement it cannot parse is reported as SKIPPED and counted, never assumed
  true -- the skip count is the coverage number and is printed every run.

Usage:  python3 scripts/check-established-facts-bounded-truth.py [--bound N]
"""

from __future__ import annotations

import argparse
import json
import math
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
SETTLED = {"proved", "computed"}


class TruthError(Exception):
    pass


def factorial(n: int) -> int:
    return math.factorial(n)


def desc_factorial(n: int, k: int) -> int:
    out = 1
    for i in range(k):
        out *= max(n - i, 0)  # Nat subtraction TRUNCATES; using n-i would lie
    return out


def asc_factorial(n: int, k: int) -> int:
    out = 1
    for i in range(k):
        out *= n + i
    return out


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


# Statement shapes this net understands. Deliberately narrow and explicit: a
# regex that matched loosely would evaluate the wrong proposition and could
# manufacture a counterexample against a true theorem, which is the single worst
# outcome here -- far worse than low coverage.
PATTERNS: list[tuple[str, str]] = [
    (r"^∀ \(n : ℕ\), n\.descFactorial 1 = n$", "desc_factorial(n,1) == n"),
    (r"^∀ \(n : ℕ\), n\.descFactorial 0 = 1$", "desc_factorial(n,0) == 1"),
    (r"^∀ \(n : ℕ\), n\.ascFactorial 0 = 1$", "asc_factorial(n,0) == 1"),
    (r"^∀ \(k : ℕ\), Nat\.ascFactorial 0 k\.succ = 0$", "asc_factorial(0,n+1) == 0"),
    (r"^∀ \(k : ℕ\), Nat\.ascFactorial 1 k = k\.factorial$", "asc_factorial(1,n) == factorial(n)"),
    (r"^∀ \(n : ℕ\), n\.factorial = 0$", "factorial(n) == 0"),
]

ENV = {
    "factorial": factorial,
    "desc_factorial": desc_factorial,
    "asc_factorial": asc_factorial,
    "fib": fib,
}


def evaluate(statement: str, bound: int) -> tuple[str, int | None]:
    """(verdict, counterexample) where verdict is holds / counterexample / skipped."""
    for pattern, expr in PATTERNS:
        if re.match(pattern, statement.strip()):
            code = compile(expr, "<stmt>", "eval")
            for n in range(bound):
                if not eval(code, {"__builtins__": {}}, dict(ENV, n=n)):  # noqa: S307
                    return "counterexample", n
            return "holds", None
    return "skipped", None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bound", type=int, default=64)
    args = parser.parse_args()
    try:
        settled = []
        for path in sorted(FACTS.glob("*.json")):
            fact = json.loads(path.read_text())
            if fact["epistemic_status"] in SETTLED:
                settled.append(fact)
        if not settled:
            raise TruthError("no settled facts; this net would pass vacuously")

        holds = skipped = 0
        failures: list[str] = []
        for fact in settled:
            statement = (fact.get("formal") or {}).get("statement") or ""
            verdict, witness = evaluate(statement, args.bound)
            if verdict == "holds":
                holds += 1
            elif verdict == "skipped":
                skipped += 1
            else:
                failures.append(f"{fact['id']} is {fact['epistemic_status']} but FAILS at n={witness}: {statement}")

        if holds == 0:
            raise TruthError(
                f"evaluated 0 of {len(settled)} settled facts; the net is pointed at "
                "nothing and a clean run would mean nothing"
            )

        verdict = "FAIL" if failures else "PASS"
        print(
            f"ESTABLISHED_FACT_TRUTH|settled={len(settled)}|evaluated={holds}|"
            f"skipped={skipped}|counterexamples={len(failures)}|bound={args.bound}|"
            f"verdict={verdict}"
        )
        for failure in failures:
            print(
                f"  ESTABLISHED-FACT-IS-FALSE|{failure}\n"
                "    A statement we marked settled has a counterexample. This is a "
                "kernel, import, or transcription defect and it invalidates every "
                "dependent. Do not re-pin; investigate.",
                file=sys.stderr,
            )
        return 1 if failures else 0
    except (OSError, json.JSONDecodeError, TruthError) as error:
        print(f"ESTABLISHED_FACT_TRUTH_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
