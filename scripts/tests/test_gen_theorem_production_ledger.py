#!/usr/bin/env python3
"""Mutation controls for the cross-prelude theorem production ledger.

The measurement itself costs a release build of eight preludes, so these tests
stub the subprocess and exercise the VALIDATION, which is where this generator
can lie. Every guard below exists because its absence would let the ledger
publish a number that looks fine:

* a prelude silently dropped from the example makes the ledger narrower, not red
  — the failure that let a coverage claim be drawn from a tool that never
  covered its subject;
* an `originated` column that does not sum to the distinct total means the
  attribution is wrong, and every per-prelude production number under it is
  wrong with it;
* a `--check` that says "stale" without a DIRECTION invites re-pinning a fall,
  and a fall is the one thing that cannot happen honestly.
"""

from __future__ import annotations

import importlib.util
import pathlib
import subprocess
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-theorem-production-ledger.py"
SPEC = importlib.util.spec_from_file_location("gen_theorem_production_ledger", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
ledger = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ledger)

GROUPS = {
    "logic": 2,
    "nat": 139,
    "axreal": 2,
    "integer": 201,
    "rat": 320,
    "string": 6,
    "creal": 390,
    "complex": 414,
}
ORIGIN = {
    "logic": 2,
    "nat": 137,
    "axreal": 0,
    "integer": 62,
    "rat": 119,
    "string": 4,
    "creal": 70,
    "complex": 24,
}


def stderr(groups=None, origin=None, preludes=None, distinct=418, ties=2) -> str:
    groups = GROUPS if groups is None else groups
    origin = ORIGIN if origin is None else origin
    names = sorted(groups) if preludes is None else preludes
    lines = [
        f"{p}: theorems={groups[p]} axiom_free={groups[p]} axiom_bearing=0 "
        f"originated={origin[p]}"
        for p in groups
    ]
    lines.append(f"origin_ties: {ties}")
    lines.append(
        f"distinct: theorems={distinct} axiom_free={distinct} axiom_bearing=0 "
        f"preludes={','.join(names)}"
    )
    return "\n".join(lines)


def run_with(text: str, code: int = 0):
    completed = subprocess.CompletedProcess(args="", returncode=code, stdout="", stderr=text)
    with mock.patch.object(subprocess, "run", return_value=completed):
        return ledger.measure()


class TheoremProductionLedgerTests(unittest.TestCase):
    def test_a_well_formed_measurement_parses(self) -> None:
        groups, distinct, ties = run_with(stderr())
        self.assertEqual(distinct["theorems"], 418)
        self.assertEqual(ties, 2)
        self.assertEqual(groups["rat"]["originated"], 119)

    def test_a_dropped_prelude_is_an_error_not_a_narrower_ledger(self) -> None:
        groups = {k: v for k, v in GROUPS.items() if k != "complex"}
        origin = {k: v for k, v in ORIGIN.items() if k != "complex"}
        with self.assertRaisesRegex(ledger.LedgerError, "coverage changed"):
            run_with(stderr(groups, origin, distinct=394))

    def test_a_prelude_missing_from_the_rows_is_an_error(self) -> None:
        """The distinct line can claim coverage the group rows do not have."""
        groups = {k: v for k, v in GROUPS.items() if k != "complex"}
        origin = {k: v for k, v in ORIGIN.items() if k != "complex"}
        with self.assertRaisesRegex(ledger.LedgerError, "absent from the measurement"):
            run_with(stderr(groups, origin, preludes=sorted(GROUPS), distinct=394))

    def test_originated_columns_must_sum_to_the_distinct_total(self) -> None:
        origin = dict(ORIGIN, rat=118)
        with self.assertRaisesRegex(ledger.LedgerError, "sum to 417"):
            run_with(stderr(origin=origin))

    def test_a_missing_distinct_line_is_an_error(self) -> None:
        text = "\n".join(
            line for line in stderr().splitlines() if not line.startswith("distinct:")
        )
        with self.assertRaisesRegex(ledger.LedgerError, "did not report"):
            run_with(text)

    def test_a_missing_tie_count_is_an_error(self) -> None:
        text = "\n".join(
            line for line in stderr().splitlines() if not line.startswith("origin_ties:")
        )
        with self.assertRaisesRegex(ledger.LedgerError, "did not report"):
            run_with(text)

    def test_a_failed_example_is_an_error(self) -> None:
        with self.assertRaisesRegex(ledger.LedgerError, "failed"):
            run_with(stderr(), code=1)

    # --- direction, which is the whole point of the --check message ----------
    def test_a_rise_is_reported_as_production(self) -> None:
        message = ledger._direction(
            "- **400 distinct theorems**", "- **418 distinct theorems**"
        )
        self.assertIn("ROSE 400 -> 418", message)
        self.assertIn("production", message)

    def test_a_fall_is_reported_as_a_regression_not_a_re_pin(self) -> None:
        message = ledger._direction(
            "- **500 distinct theorems**", "- **418 distinct theorems**"
        )
        self.assertIn("FELL 500 -> 418", message)
        self.assertIn("Do not re-pin", message)

    # --- the committed ledger ------------------------------------------------
    def test_the_committed_ledger_warns_against_summing_the_cumulative_column(self) -> None:
        """`rat` alone is 320 of a 418-theorem library; a reader who sums the
        column gets 1474 and believes it."""
        text = ledger.LEDGER.read_text()
        self.assertIn("Do not sum the second column", text)
        self.assertIn("Originated here", text)

    def test_the_committed_ledger_says_it_does_not_measure_autonomy(self) -> None:
        self.assertIn("not **autonomous** theorems", ledger.LEDGER.read_text())


if __name__ == "__main__":
    unittest.main()
