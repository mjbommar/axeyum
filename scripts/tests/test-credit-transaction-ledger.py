#!/usr/bin/env python3
"""Test suite for scripts/credit-transaction-ledger.py and its gate,
scripts/check-credit-transaction-ledger.py -- the wiring of ADR-0785's
two-phase-commit engine into the REAL fact ledger write set (ADR-0810).

Run directly: `python3 scripts/tests/test-credit-transaction-ledger.py -v`
(the filename has a hyphen, so it cannot be imported as a module).

Every test below drives functions that operate ONLY on scratch copies built
by `build_scratch_base` (a `shutil.copytree` of `scripts/`,
`artifacts/facts/`, `artifacts/ontology/`, `artifacts/safety-matrix/` into a
`tempfile.mkdtemp()` directory) -- nothing here ever writes to the real
ledger. See scripts/check-credit-transaction-ledger.py's module docstring.

Covers:
  1. crash-boundary sweep over the REAL write ops converges to OLD or NEW
  2. four DISTINCT staleness rejections against the real dimensions
  3. idempotent replay + the guard's measured (not assumed) value
  4. content rejection via validate-facts.py's own validate_one
  5. the gate fails closed on an empty fixture/boundary set
  6. individual guards are mutation-verified separately by
     scripts/tests/test-credit-transaction-ledger-mutations.sh
"""
from __future__ import annotations

import importlib.util
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_SCRIPTS = _HERE.parent


def _load(name: str, relpath: str):
    spec = importlib.util.spec_from_file_location(name, _SCRIPTS / relpath)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


gate = _load("check_credit_transaction_ledger", "check-credit-transaction-ledger.py")


class CrashBoundarySweepTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.results, cls.total_ops, cls.old_snap, cls.new_snap = gate.run_crash_sweep()

    def test_at_least_one_boundary_found(self):
        self.assertGreater(self.total_ops, 0, "the sweep found zero write ops -- nothing was tested")
        self.assertEqual(len(self.results), self.total_ops)

    def test_every_boundary_resolves_to_old_or_new(self):
        bad = [(k, o) for (k, o) in self.results if o not in ("OLD", "NEW")]
        self.assertEqual(bad, [], f"these op indices resolved to neither OLD nor NEW: {bad}")

    def test_both_old_and_new_outcomes_occur(self):
        outcomes = {o for (_, o) in self.results}
        self.assertIn("OLD", outcomes, "no interruption point rolled back to OLD")
        self.assertIn("NEW", outcomes, "no interruption point rolled forward to NEW")

    def test_old_and_new_snapshots_actually_differ(self):
        self.assertNotEqual(self.old_snap, self.new_snap)

    def test_evaluate_crash_sweep_passes_on_the_real_results(self):
        ok, reason = gate.evaluate_crash_sweep(self.results, self.total_ops)
        self.assertTrue(ok, reason)

    def test_op_count_is_reported(self):
        # Documents the measured real boundary count; also fails loudly if a
        # refactor ever collapses the transaction into one giant write.
        self.assertGreaterEqual(self.total_ops, 10, f"only {self.total_ops} ops -- suspiciously few boundaries")

    def test_gate_fails_closed_on_empty_boundaries(self):
        ok, reason = gate.evaluate_crash_sweep([], 0)
        self.assertFalse(ok)
        self.assertIn("NO BOUNDARIES ENUMERATED", reason)


class StalenessFixtureTests(unittest.TestCase):
    def test_all_four_fixtures_reject_distinctly(self):
        ok, reason, rows = gate.run_staleness_suite()
        self.assertTrue(ok, f"{reason}: {rows}")
        self.assertEqual(len(rows), 4)

    def test_fresh_pass_control_does_not_reject(self):
        # Without this, "every fixture rejects" could be true because
        # commit() rejects EVERYTHING.
        self.assertTrue(gate.run_fresh_pass_control())

    def test_gate_fails_closed_on_empty_fixtures(self):
        ok, reason, rows = gate.run_staleness_suite(fixtures=[])
        self.assertFalse(ok)
        self.assertIn("NO STALENESS FIXTURES REGISTERED", reason)
        self.assertEqual(rows, [])

    def test_stale_receipt_raises_only_stale_receipt_error(self):
        root, mod, txn_dir = gate._fixture_stale_receipt(gate.TEST_FACT_ID)
        try:
            with self.assertRaises(mod.ct.StaleReceiptError):
                mod.commit(txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_source_raises_only_stale_source_error(self):
        root, mod, txn_dir = gate._fixture_stale_source(gate.TEST_FACT_ID)
        try:
            with self.assertRaises(mod.ct.StaleSourceError):
                mod.commit(txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_graph_raises_only_stale_graph_error(self):
        root, mod, txn_dir = gate._fixture_stale_graph(gate.TEST_FACT_ID)
        try:
            with self.assertRaises(mod.ct.StaleGraphError):
                mod.commit(txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_checker_raises_only_stale_checker_error(self):
        root, mod, txn_dir = gate._fixture_stale_checker(gate.TEST_FACT_ID)
        try:
            with self.assertRaises(mod.ct.StaleCheckerError):
                mod.commit(txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)


class IdempotenceTests(unittest.TestCase):
    def test_replay_is_idempotent(self):
        ok, detail = gate.run_idempotence_check()
        self.assertTrue(ok, detail)

    def test_guard_skips_recomputation_on_replay(self):
        # Also documents the MEASURED finding (not the fixture's assumption):
        # the real rebuilt targets are idempotent by construction even
        # without the guard (a keyed full rebuild, not an append log), so the
        # guard's load-bearing property here is skipping wasted work, not
        # preventing corruption. See docs/plan/status/s6-wire-real-ledger.md.
        ok, detail = gate.run_guard_skips_recomputation_on_replay()
        self.assertTrue(ok, detail)
        self.assertEqual(detail["pin_rows_for_fact"], 1)
        self.assertEqual(detail["txns_created_without_guard"], 2)


class ContentRejectionTests(unittest.TestCase):
    def test_invalid_depends_on_is_rejected_by_validate_one(self):
        ok, detail = gate.run_invalid_content_is_rejected()
        self.assertTrue(ok, detail)


class GuardBehaviorTests(unittest.TestCase):
    """Individual guards this wrapper OWNS (as opposed to guards reused
    as-is from credit-transaction.py, already mutation-verified by
    scripts/tests/test-credit-transaction-mutations.sh), each isolated by
    its own fixture. Mutation table:
    scripts/tests/test-credit-transaction-ledger-mutations.sh."""

    def test_commit_rejects_a_non_prepared_transaction(self):
        root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-guard-commit-"))
        try:
            gate.build_scratch_base(root)
            mod = gate._load_ledger_engine_from(root)
            new_fact = gate._new_fact(gate.TEST_FACT_ID)
            _, txn_dir = mod.propose(gate.TEST_FACT_ID, new_fact)
            mod.commit(txn_dir)  # now status == "committed"
            with self.assertRaises(mod.ct.TransactionStateError):
                mod.commit(txn_dir)  # committing again must be refused
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_rejects_an_uncommitted_transaction(self):
        root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-guard-apply-"))
        try:
            gate.build_scratch_base(root)
            mod = gate._load_ledger_engine_from(root)
            new_fact = gate._new_fact(gate.TEST_FACT_ID)
            _, txn_dir = mod.propose(gate.TEST_FACT_ID, new_fact)
            with self.assertRaises(mod.ct.TransactionStateError):
                mod.apply(txn_dir)  # never committed
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_refuses_corrupted_staged_content(self):
        root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-guard-corrupt-"))
        try:
            gate.build_scratch_base(root)
            mod = gate._load_ledger_engine_from(root)
            new_fact = gate._new_fact(gate.TEST_FACT_ID)
            _, txn_dir = mod.propose(gate.TEST_FACT_ID, new_fact)
            mod.commit(txn_dir)
            staged = sorted((txn_dir / "staged").iterdir())
            staged[0].write_bytes(b"TORN-WRITE-GARBAGE")
            with self.assertRaises(mod.ct.CorruptStagingError):
                mod.apply(txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_invalid_fact_content_is_rejected_before_any_txn_dir_exists(self):
        # compute_cascade() (called from propose()) must reject BEFORE any
        # durable write happens -- confirms the validate_one guard runs
        # ahead of staging, not merely somewhere in the pipeline.
        root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-guard-content-"))
        try:
            gate.build_scratch_base(root)
            mod = gate._load_ledger_engine_from(root)
            bad_fact = gate._new_fact(gate.TEST_FACT_ID)
            bad_fact["depends_on"] = ["F:this-fact-id-does-not-exist-anywhere"]
            with self.assertRaises(mod.LedgerCascadeError):
                mod.propose(gate.TEST_FACT_ID, bad_fact)
            txn_root = mod.TXN_ROOT / "_txn"
            self.assertFalse(txn_root.exists() and any(txn_root.iterdir()))
        finally:
            shutil.rmtree(root, ignore_errors=True)


class RealWriteSetTests(unittest.TestCase):
    """Confirms the ACTUAL relpaths touched match what ADR-0810 documents --
    fails loudly if a future edit silently widens or narrows the write set."""

    def test_applied_transaction_touches_exactly_the_documented_targets(self):
        root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-writeset-"))
        try:
            gate.build_scratch_base(root)
            mod = gate._load_ledger_engine_from(root)
            new_fact = gate._new_fact(gate.TEST_FACT_ID)
            _, txn_dir = mod.propose(gate.TEST_FACT_ID, new_fact)
            journal = mod.ct._load_journal_fresh(txn_dir)
            relpaths = {w.relpath for w in journal.writes}
            expected = {
                f"artifacts/facts/{gate.TEST_FACT_ID.replace('F:', 'F-')}.json",
                "artifacts/ontology/settled-fact-statement-pins.json",
                "artifacts/safety-matrix/safety-matrix.tsv",
                "artifacts/safety-matrix/safety-matrix-summary.md",
                f"artifacts/.credit-txn/receipts/latest/{gate.TEST_FACT_ID.replace('F:', 'F-')}.sha256",
            }
            self.assertEqual(relpaths, expected)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
