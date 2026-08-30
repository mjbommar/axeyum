#!/usr/bin/env python3
"""Test suite for the L0 phase S6 credit-transaction engine and its gate.

Run directly: `python3 scripts/tests/test-credit-transaction.py -v`
(the filename has a hyphen, so it cannot be imported as a module -- it is a
script, not `python3 -m unittest ...`).

Covers the six S6 obligations from
docs/plan/trusted-library-safety-roadmap-2026-08-30.md:

  1. crash-boundary sweep converges to OLD or NEW at every op
  2. fresh-read: commit() acts on the disk journal, not a cached object
  3. four DISTINCT staleness rejections
  4. idempotent replay (no double-append)
  5. the gate fails closed on an empty fixture/boundary set
  6. individual guards (state preconditions, corrupt-staging refusal) --
     mutation-verified separately by
     scripts/tests/test-credit-transaction-mutations.sh
"""
from __future__ import annotations

import importlib.util
import json
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


# Load `check-credit-transaction.py` FIRST and take `ct` from IT, rather than
# loading `credit-transaction.py` independently here too. Two separate
# `importlib` loads of the same file under the same module name produce TWO
# DISTINCT module objects with their own separate copies of any module-level
# state (in particular `_LAST_STAGED_JOURNAL`, the cache the fresh-read guard
# exists to bypass). Fixtures built via `gate._fixture_*` populate the cache
# inside `gate`'s module instance; calling `ct.commit(...)` against a
# DIFFERENT instance would see an empty cache and raise a spurious KeyError
# that has nothing to do with any guard being tested -- confirmed by
# deliberately reproducing it while building this suite.
gate = _load("check_credit_transaction", "check-credit-transaction.py")
ct = gate.ct


def _tmp(prefix: str) -> Path:
    return Path(tempfile.mkdtemp(prefix=prefix))


class CrashBoundarySweepTests(unittest.TestCase):
    """Requirement 1: the crash test IS the deliverable."""

    @classmethod
    def setUpClass(cls):
        cls.results, cls.total_ops, cls.old_snap, cls.new_snap = gate.run_crash_sweep()

    def test_at_least_one_boundary_found(self):
        self.assertGreater(
            self.total_ops, 0, "the sweep found zero write ops -- nothing was tested"
        )
        self.assertEqual(len(self.results), self.total_ops)

    def test_every_boundary_resolves_to_old_or_new(self):
        bad = [(k, o) for (k, o) in self.results if o not in ("OLD", "NEW")]
        self.assertEqual(
            bad, [], f"these op indices resolved to neither OLD nor NEW: {bad}"
        )

    def test_both_old_and_new_outcomes_occur(self):
        outcomes = {o for (_, o) in self.results}
        self.assertIn("OLD", outcomes, "no interruption point rolled back to OLD")
        self.assertIn("NEW", outcomes, "no interruption point rolled forward to NEW")

    def test_old_and_new_snapshots_actually_differ(self):
        # If they didn't, "resolves to OLD or NEW" would be checking nothing.
        self.assertNotEqual(self.old_snap, self.new_snap)

    def test_evaluate_crash_sweep_passes_on_the_real_results(self):
        ok, reason = gate.evaluate_crash_sweep(self.results, self.total_ops)
        self.assertTrue(ok, reason)

    def test_op_count_is_reported(self):
        # Documents the measured boundary count for the report; also fails
        # loudly if the engine's op count ever collapses to something tiny
        # (e.g. a refactor that accidentally batches every write into one).
        self.assertGreaterEqual(
            self.total_ops, 10, f"only {self.total_ops} ops -- suspiciously few boundaries"
        )


class FreshReadTests(unittest.TestCase):
    """Requirement 2: construct disagreement, show the checker uses disk."""

    def test_commit_uses_fresh_disk_journal_not_cached_object(self):
        ok, detail = gate.run_fresh_read_check()
        self.assertTrue(ok, detail)

    def test_cached_and_disk_journal_genuinely_diverge_in_this_scenario(self):
        # Re-derive the divergence directly (not via the gate helper) so this
        # test fails loudly if the scenario stops being a real divergence.
        root = _tmp("credit-txn-test-freshread-")
        try:
            fact_id, receipt = "F:t-fresh", b"R"
            ct.init_ledger(root, fact_id)
            nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
            _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
            cached = ct._LAST_STAGED_JOURNAL[str(txn_dir)]
            data = json.loads((txn_dir / "journal.json").read_text())
            data["inputs"]["checker_version"] = "SOMETHING-ELSE"
            (txn_dir / "journal.json").write_text(json.dumps(data))
            self.assertNotEqual(cached.inputs.checker_version, "SOMETHING-ELSE")
            fresh = ct._load_journal_fresh(txn_dir)
            self.assertEqual(fresh.inputs.checker_version, "SOMETHING-ELSE")
        finally:
            shutil.rmtree(root, ignore_errors=True)


class StalenessFixtureTests(unittest.TestCase):
    """Requirement 3: four fixtures, four distinct named rejections."""

    def test_all_four_fixtures_reject_distinctly(self):
        ok, reason, rows = gate.run_staleness_suite()
        self.assertTrue(ok, f"{reason}: {rows}")
        self.assertEqual(len(rows), 4)

    def test_fresh_pass_control_does_not_reject(self):
        # Without this, "every fixture rejects" could be true because
        # commit() rejects EVERYTHING, which would make the suite above
        # vacuous.
        self.assertTrue(gate.run_fresh_pass_control())

    def test_stale_receipt_raises_only_stale_receipt_error(self):
        root, txn_dir = gate._fixture_stale_receipt()
        try:
            with self.assertRaises(ct.StaleReceiptError):
                ct.commit(root, txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_source_raises_only_stale_source_error(self):
        root, txn_dir = gate._fixture_stale_source()
        try:
            with self.assertRaises(ct.StaleSourceError):
                ct.commit(root, txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_graph_raises_only_stale_graph_error(self):
        root, txn_dir = gate._fixture_stale_graph()
        try:
            with self.assertRaises(ct.StaleGraphError):
                ct.commit(root, txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_checker_raises_only_stale_checker_error(self):
        root, txn_dir = gate._fixture_stale_checker()
        try:
            with self.assertRaises(ct.StaleCheckerError):
                ct.commit(root, txn_dir)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_four_exception_classes_are_pairwise_distinct(self):
        classes = {
            ct.StaleReceiptError,
            ct.StaleSourceError,
            ct.StaleGraphError,
            ct.StaleCheckerError,
        }
        self.assertEqual(len(classes), 4)
        for a in classes:
            for b in classes:
                if a is not b:
                    self.assertFalse(issubclass(a, b))


class IdempotenceTests(unittest.TestCase):
    """Requirement 4: replay is idempotent, no double-count."""

    def test_replay_is_idempotent(self):
        ok, detail = gate.run_idempotence_check()
        self.assertTrue(ok, detail)

    def test_replay_without_the_registry_guard_would_double_append(self):
        # Demonstrates the FAILURE the guard prevents, by recomputing the
        # cascade twice manually (bypassing run_transaction's short-circuit)
        # exactly as a caller without the guard would.
        root = _tmp("credit-txn-test-idem-noguard-")
        try:
            fact_id, receipt = "F:t-idem-noguard", b"R"
            ct.init_ledger(root, fact_id)
            for _ in range(2):
                nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
                _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
                ct.commit(root, txn_dir)
                ct.apply(root, txn_dir)
            dash = (root / "dashboards" / "settled.md").read_text()
            self.assertEqual(
                dash.count(fact_id),
                2,
                "sanity check: calling propose/commit/apply directly, twice, "
                "WITHOUT the run_transaction() short-circuit really does "
                "double-append -- confirming the guard is load-bearing",
            )
        finally:
            shutil.rmtree(root, ignore_errors=True)


class GuardBehaviorTests(unittest.TestCase):
    """Individual guards, each with a fixture that isolates it. Mutation
    table lives in scripts/tests/test-credit-transaction-mutations.sh."""

    def test_commit_rejects_a_non_prepared_transaction(self):
        root = _tmp("credit-txn-test-guard-commit-status-")
        try:
            fact_id, receipt = "F:t-guard1", b"R"
            ct.init_ledger(root, fact_id)
            nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
            _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
            ct.commit(root, txn_dir)  # now status == "committed"
            with self.assertRaises(ct.TransactionStateError):
                ct.commit(root, txn_dir)  # committing again must be refused
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_rejects_an_uncommitted_transaction(self):
        root = _tmp("credit-txn-test-guard-apply-status-")
        try:
            fact_id, receipt = "F:t-guard2", b"R"
            ct.init_ledger(root, fact_id)
            nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
            _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
            with self.assertRaises(ct.TransactionStateError):
                ct.apply(root, txn_dir)  # never committed
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_refuses_corrupted_staged_content(self):
        root = _tmp("credit-txn-test-guard-corrupt-")
        try:
            fact_id, receipt = "F:t-guard3", b"R"
            ct.init_ledger(root, fact_id)
            nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
            _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
            ct.commit(root, txn_dir)
            staged = sorted((txn_dir / "staged").iterdir())
            staged[0].write_bytes(b"TORN-WRITE-GARBAGE")
            with self.assertRaises(ct.CorruptStagingError):
                ct.apply(root, txn_dir)
            # And nothing was installed: every target is still the OLD value.
            fact = json.loads((root / "facts" / f"{fact_id}.json").read_text())
            self.assertEqual(fact["epistemic_status"], "open")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_recover_rolls_back_a_never_committed_transaction(self):
        root = _tmp("credit-txn-test-guard-rollback-")
        try:
            fact_id, receipt = "F:t-guard4", b"R"
            ct.init_ledger(root, fact_id)
            old_snap = gate.full_tree_snapshot(root)
            nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
            ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
            # Never committed.
            actions = ct.recover(root)
            self.assertTrue(any("never committed" in a for a in actions), actions)
            self.assertEqual(gate.full_tree_snapshot(root), old_snap)
            self.assertFalse((root / "_txn").exists() and any((root / "_txn").iterdir()))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_recover_rolls_forward_a_committed_transaction(self):
        root = _tmp("credit-txn-test-guard-rollforward-")
        try:
            fact_id, receipt = "F:t-guard5", b"R"
            ct.init_ledger(root, fact_id)
            nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
            _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
            ct.commit(root, txn_dir)  # committed but never applied
            actions = ct.recover(root)
            self.assertTrue(any("roll-forward" in a for a in actions), actions)
            fact = json.loads((root / "facts" / f"{fact_id}.json").read_text())
            self.assertEqual(fact["epistemic_status"], "proved")
        finally:
            shutil.rmtree(root, ignore_errors=True)


class GateAbsenceTests(unittest.TestCase):
    """Requirement 5: the gate must fail on absence, with a named reason."""

    def test_empty_staleness_fixtures_fails_with_named_reason(self):
        ok, reason, rows = gate.run_staleness_suite(fixtures=[])
        self.assertFalse(ok)
        self.assertIn("NO STALENESS FIXTURES REGISTERED", reason)
        self.assertEqual(rows, [])

    def test_zero_boundaries_fails_with_named_reason(self):
        ok, reason = gate.evaluate_crash_sweep([], 0)
        self.assertFalse(ok)
        self.assertIn("NO BOUNDARIES ENUMERATED", reason)

    def test_cli_exits_nonzero_and_names_the_reason_for_empty_fixtures(self):
        import subprocess

        proc = subprocess.run(
            [sys.executable, str(_SCRIPTS / "check-credit-transaction.py"), "--empty-fixtures"],
            capture_output=True,
            text=True,
            timeout=60,
        )
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("NO STALENESS FIXTURES REGISTERED", proc.stdout)

    def test_cli_exits_nonzero_and_names_the_reason_for_empty_boundaries(self):
        import subprocess

        proc = subprocess.run(
            [sys.executable, str(_SCRIPTS / "check-credit-transaction.py"), "--empty-boundaries"],
            capture_output=True,
            text=True,
            timeout=60,
        )
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("NO BOUNDARIES ENUMERATED", proc.stdout)

    def test_cli_exits_zero_on_the_real_run(self):
        import subprocess

        proc = subprocess.run(
            [sys.executable, str(_SCRIPTS / "check-credit-transaction.py")],
            capture_output=True,
            text=True,
            timeout=60,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("CREDIT_TXN|summary|ok=True", proc.stdout)


if __name__ == "__main__":
    unittest.main()
