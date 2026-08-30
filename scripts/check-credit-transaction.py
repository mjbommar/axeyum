#!/usr/bin/env python3
"""Gate for the L0 phase S6 credit-transaction engine.

docs/plan/trusted-library-safety-roadmap-2026-08-30.md, S6 exit:

    interruption at every write boundary leaves either old state or a
    complete new state; replay is idempotent; stale receipt, source, graph,
    or checker versions reject.

This is not a "does it import" smoke test. It:

  1. Runs `scripts/credit-transaction.py`'s crash-boundary sweep: one full
     transaction is executed to count every low-level write op, then the
     transaction is re-run once per op with a fault injected at that exact
     op, and the resulting (post-`recover()`) ledger state is compared
     byte-for-byte against the pre-transaction snapshot (OLD) and the
     post-transaction snapshot (NEW). Every op index must resolve to
     exactly one of the two -- never neither, never "did not crash".
  2. Runs the four staleness fixtures (receipt, source, graph, checker),
     each of which must reject with its OWN named exception, plus a
     fresh-pass control that must NOT reject.
  3. Runs the fresh-read demonstration: an in-process cached journal object
     and the on-disk journal are made to disagree, and `commit()` is shown
     to act on the disk value.
  4. Runs the idempotent-replay check: the same (fact_id, receipt) applied
     twice must not double-append the cascade/dashboard.

Per CLAUDE.md's standing rule, EVERY one of these is fail-closed on absence:
zero boundaries, zero fixtures, or a crash sweep that never actually crashed
is a FAILURE, not a vacuous pass. `--empty-fixtures` and `--empty-boundaries`
exist ONLY so `scripts/tests/test-credit-transaction.py` can demonstrate that
exit code and reason from the outside; do not use them for anything else.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import shutil
import sys
import tempfile
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_ENGINE_PATH = _HERE / "credit-transaction.py"


def load_engine():
    spec = importlib.util.spec_from_file_location("credit_transaction", _ENGINE_PATH)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["credit_transaction"] = mod
    spec.loader.exec_module(mod)
    return mod


ct = load_engine()


# ---------------------------------------------------------------------------
# Snapshots
# ---------------------------------------------------------------------------
def full_tree_snapshot(root: Path) -> dict:
    """Hash of every file under `root` EXCEPT `_txn/` (transaction scratch
    space is not part of the observable ledger state)."""
    snap = {}
    if not root.exists():
        return snap
    for p in sorted(root.rglob("*")):
        if p.is_dir():
            continue
        rel = p.relative_to(root)
        if rel.parts[0] == "_txn":
            continue
        snap[str(rel)] = ct.hash_bytes(p.read_bytes())
    return snap


# ---------------------------------------------------------------------------
# 1. Crash-boundary sweep
# ---------------------------------------------------------------------------
def run_crash_sweep(fact_id: str = "F:demo", receipt: bytes = b"RECEIPT-1"):
    """Returns (results, total_ops) where results is a list of
    (op_index, outcome) and outcome is one of "OLD", "NEW", "NEITHER",
    "NO-CRASH-RAISED"."""
    base = Path(tempfile.mkdtemp(prefix="credit-txn-crash-base-"))
    try:
        ct.init_ledger(base, fact_id)
        old_snapshot = full_tree_snapshot(base)

        total_root = Path(tempfile.mkdtemp(prefix="credit-txn-crash-total-"))
        try:
            shutil.copytree(base, total_root, dirs_exist_ok=True)
            ct.clear_crash_budget()
            ct.run_transaction(total_root, fact_id, receipt)
            total_ops = ct.ops_performed()
            new_snapshot = full_tree_snapshot(total_root)
        finally:
            shutil.rmtree(total_root, ignore_errors=True)

        if total_ops == 0:
            return [], 0, old_snapshot, new_snapshot

        results = []
        for k in range(0, total_ops):
            scratch = Path(tempfile.mkdtemp(prefix="credit-txn-crash-scratch-"))
            try:
                shutil.copytree(base, scratch, dirs_exist_ok=True)
                ct.set_crash_budget(k)
                crashed = False
                try:
                    ct.run_transaction(scratch, fact_id, receipt)
                except ct.SimulatedCrash:
                    crashed = True
                finally:
                    ct.clear_crash_budget()
                if not crashed:
                    results.append((k, "NO-CRASH-RAISED"))
                    continue
                ct.recover(scratch)
                snap = full_tree_snapshot(scratch)
                if snap == old_snapshot:
                    results.append((k, "OLD"))
                elif snap == new_snapshot:
                    results.append((k, "NEW"))
                else:
                    results.append((k, "NEITHER"))
            finally:
                shutil.rmtree(scratch, ignore_errors=True)
        return results, total_ops, old_snapshot, new_snapshot
    finally:
        shutil.rmtree(base, ignore_errors=True)


def evaluate_crash_sweep(results: list, total_ops: int):
    """Fail-closed evaluation. Returns (ok: bool, reason: str)."""
    if total_ops == 0 or not results:
        return False, "NO BOUNDARIES ENUMERATED: the crash sweep found zero write ops"
    bad = [(k, o) for (k, o) in results if o not in ("OLD", "NEW")]
    if bad:
        return False, (
            f"CRASH SWEEP FAILED at {len(bad)} boundary(ies): "
            + ", ".join(f"op#{k}={o}" for k, o in bad[:10])
        )
    outcomes = {o for (_, o) in results}
    if "OLD" not in outcomes:
        return False, "CRASH SWEEP DEGENERATE: no interruption resolved to OLD state"
    if "NEW" not in outcomes:
        return False, "CRASH SWEEP DEGENERATE: no interruption resolved to NEW state"
    return True, f"{len(results)} boundaries, all resolve to OLD or NEW"


# ---------------------------------------------------------------------------
# 2. Staleness fixtures
# ---------------------------------------------------------------------------
def _propose_fresh(root, fact_id, receipt):
    # Deliberately does NOT pre-write the receipt pointer: `propose_transaction`
    # snapshots whatever is currently on disk (nothing, for a fact's first
    # transaction), and that snapshot matching a later fresh re-read is what
    # "not stale" means. Pre-writing it here would also make the pointer
    # write LOOK already-applied to `apply()`'s idempotence check before the
    # transaction ever ran, which defeats a corrupt-staging test on that file.
    nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
    return ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)


def _fixture_fresh_pass():
    root = Path(tempfile.mkdtemp(prefix="credit-txn-fx-fresh-"))
    fact_id, receipt = "F:fx-fresh", b"R-FRESH"
    ct.init_ledger(root, fact_id)
    _, txn_dir = _propose_fresh(root, fact_id, receipt)
    return root, txn_dir


def _fixture_stale_receipt():
    root = Path(tempfile.mkdtemp(prefix="credit-txn-fx-receipt-"))
    fact_id, receipt = "F:fx-receipt", b"R-ORIGINAL"
    ct.init_ledger(root, fact_id)
    nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
    _, txn_dir = ct.propose_transaction(root, fact_id, receipt, nf, ng, npi, nd)
    # A concurrent lane records a DIFFERENT receipt as authoritative for the
    # same fact_id, entirely outside this transaction.
    ct.record_latest_receipt(root, fact_id, b"R-FROM-ANOTHER-LANE")
    return root, txn_dir


def _fixture_stale_source():
    root = Path(tempfile.mkdtemp(prefix="credit-txn-fx-source-"))
    fact_id, receipt = "F:fx-source", b"R-SOURCE"
    ct.init_ledger(root, fact_id)
    _, txn_dir = _propose_fresh(root, fact_id, receipt)
    # The fact's own source file changes on disk after staging.
    (root / "facts" / f"{fact_id}.json").write_text(
        json.dumps({"fact_id": fact_id, "epistemic_status": "open", "note": "edited"})
    )
    return root, txn_dir


def _fixture_stale_graph():
    root = Path(tempfile.mkdtemp(prefix="credit-txn-fx-graph-"))
    fact_id, receipt = "F:fx-graph", b"R-GRAPH"
    ct.init_ledger(root, fact_id)
    _, txn_dir = _propose_fresh(root, fact_id, receipt)
    (root / "graph" / "graph.json").write_text(json.dumps({"settled": ["F:other"]}))
    return root, txn_dir


def _fixture_stale_checker():
    root = Path(tempfile.mkdtemp(prefix="credit-txn-fx-checker-"))
    fact_id, receipt = "F:fx-checker", b"R-CHECKER"
    ct.init_ledger(root, fact_id)
    nf, ng, npi, nd = ct.cascade_append_settled(root, fact_id, receipt)
    _, txn_dir = ct.propose_transaction(
        root, fact_id, receipt, nf, ng, npi, nd, checker_version="OLD-CHECKER-VERSION"
    )
    return root, txn_dir


STALENESS_FIXTURES = [
    ("stale-receipt", ct.StaleReceiptError, _fixture_stale_receipt),
    ("stale-source", ct.StaleSourceError, _fixture_stale_source),
    ("stale-graph", ct.StaleGraphError, _fixture_stale_graph),
    ("stale-checker", ct.StaleCheckerError, _fixture_stale_checker),
]


def run_staleness_suite(fixtures=None):
    """Fail-closed: an empty fixture list is a failure, named as such."""
    if fixtures is None:
        fixtures = STALENESS_FIXTURES
    if not fixtures:
        return False, "NO STALENESS FIXTURES REGISTERED", []

    rows = []
    for name, exc_cls, builder in fixtures:
        root, txn_dir = builder()
        try:
            try:
                ct.commit(root, txn_dir)
                rows.append((name, exc_cls.__name__, "NOT-REJECTED"))
            except exc_cls:
                rows.append((name, exc_cls.__name__, "OK"))
            except Exception as e:  # wrong exception type -- also a failure
                rows.append((name, exc_cls.__name__, f"WRONG-EXCEPTION:{type(e).__name__}"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    # Distinctness: every named exception class must be different, or a
    # single shared check could be posing as four.
    exc_names = {r[1] for r in rows}
    if len(exc_names) != len(rows):
        return False, "STALENESS FIXTURES SHARE AN EXCEPTION CLASS (not distinct)", rows

    ok = all(r[2] == "OK" for r in rows)
    reason = "all reject with distinct named reasons" if ok else "one or more did not reject as expected"
    return ok, reason, rows


def run_fresh_pass_control():
    """A transaction proposed against genuinely fresh inputs must COMMIT,
    not reject -- otherwise the four staleness checks could be vacuously
    "always reject" and still pass the suite above."""
    root, txn_dir = _fixture_fresh_pass()
    try:
        ct.commit(root, txn_dir)
        return True
    except Exception:
        return False
    finally:
        shutil.rmtree(root, ignore_errors=True)


# ---------------------------------------------------------------------------
# 3. Fresh-read demonstration
# ---------------------------------------------------------------------------
def run_fresh_read_check():
    """Construct a case where the in-process cached journal object and the
    on-disk journal DISAGREE, and confirm `commit()` acts on the disk value.
    Returns (ok: bool, detail: str)."""
    root = Path(tempfile.mkdtemp(prefix="credit-txn-fresh-read-"))
    try:
        fact_id, receipt = "F:fresh-read", b"R-FRESH-READ"
        ct.init_ledger(root, fact_id)
        _, txn_dir = _propose_fresh(root, fact_id, receipt)

        cached = ct._LAST_STAGED_JOURNAL[str(txn_dir)]
        if cached.inputs.checker_version != ct.CURRENT_CHECKER_VERSION:
            return False, "setup failed: cached journal was not fresh at staging time"

        journal_path = txn_dir / "journal.json"
        data = json.loads(journal_path.read_text())
        data["inputs"]["checker_version"] = "DIVERGED-ON-DISK"
        journal_path.write_text(json.dumps(data))

        disagree = cached.inputs.checker_version != "DIVERGED-ON-DISK"
        if not disagree:
            return False, "setup failed: cached and disk values do not actually diverge"

        try:
            ct.commit(root, txn_dir)
            return False, "commit() succeeded despite a diverged on-disk journal -- it used the cache"
        except ct.StaleCheckerError:
            return True, (
                f"cached in-memory checker_version={cached.inputs.checker_version!r} "
                f"disagreed with on-disk 'DIVERGED-ON-DISK', and commit() rejected "
                f"based on the DISK value"
            )
    finally:
        shutil.rmtree(root, ignore_errors=True)


# ---------------------------------------------------------------------------
# 4. Idempotent replay
# ---------------------------------------------------------------------------
def run_idempotence_check():
    root = Path(tempfile.mkdtemp(prefix="credit-txn-idem-"))
    try:
        fact_id, receipt = "F:idem", b"R-IDEM"
        ct.init_ledger(root, fact_id)
        r1 = ct.run_transaction(root, fact_id, receipt)
        snap1 = full_tree_snapshot(root)
        r2 = ct.run_transaction(root, fact_id, receipt)
        snap2 = full_tree_snapshot(root)
        dash = (root / "dashboards" / "settled.md").read_text()
        graph = json.loads((root / "graph" / "graph.json").read_text())
        ok = (
            r1 == "applied"
            and r2 == "noop-already-applied"
            and snap1 == snap2
            and dash.count(fact_id) == 1
            and graph["settled"].count(fact_id) == 1
        )
        return ok, f"first={r1} second={r2} dashboard_entries={dash.count(fact_id)} graph_entries={graph['settled'].count(fact_id)}"
    finally:
        shutil.rmtree(root, ignore_errors=True)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def main(argv: list) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--empty-fixtures",
        action="store_true",
        help="self-test only: run with zero staleness fixtures to demonstrate fail-on-absence",
    )
    p.add_argument(
        "--empty-boundaries",
        action="store_true",
        help="self-test only: skip the crash sweep to demonstrate fail-on-absence",
    )
    args = p.parse_args(argv)

    ok = True
    lines = []

    if args.empty_boundaries:
        boundary_ok, boundary_reason = False, "NO BOUNDARIES ENUMERATED: --empty-boundaries requested"
    else:
        results, total_ops, _old, _new = run_crash_sweep()
        boundary_ok, boundary_reason = evaluate_crash_sweep(results, total_ops)
    ok = ok and boundary_ok
    lines.append(f"CREDIT_TXN|crash-sweep|ok={boundary_ok}|{boundary_reason}")

    fixtures = [] if args.empty_fixtures else STALENESS_FIXTURES
    stale_ok, stale_reason, stale_rows = run_staleness_suite(fixtures)
    ok = ok and stale_ok
    for name, exc, outcome in stale_rows:
        lines.append(f"CREDIT_TXN|staleness|{name}|expect={exc}|outcome={outcome}")
    lines.append(f"CREDIT_TXN|staleness-suite|ok={stale_ok}|{stale_reason}")

    fresh_pass_ok = run_fresh_pass_control()
    ok = ok and fresh_pass_ok
    lines.append(f"CREDIT_TXN|fresh-pass-control|ok={fresh_pass_ok}")

    fresh_read_ok, fresh_read_detail = run_fresh_read_check()
    ok = ok and fresh_read_ok
    lines.append(f"CREDIT_TXN|fresh-read|ok={fresh_read_ok}|{fresh_read_detail}")

    idem_ok, idem_detail = run_idempotence_check()
    ok = ok and idem_ok
    lines.append(f"CREDIT_TXN|idempotence|ok={idem_ok}|{idem_detail}")

    for line in lines:
        print(line)
    print(f"CREDIT_TXN|summary|ok={ok}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
