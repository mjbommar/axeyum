#!/usr/bin/env python3
"""Gate for `scripts/credit-transaction-ledger.py` -- the wiring of ADR-0785's
two-phase-commit engine into the REAL fact ledger (ADR-0810).

This is NOT a smoke test against the fixture ledger (that suite already
exists and is untouched: `scripts/check-credit-transaction.py`). This gate
runs the SAME six obligations against a SCRATCH COPY of the actual write set
-- `artifacts/facts/`, `artifacts/ontology/settled-fact-statement-pins.json`,
`artifacts/safety-matrix/*` -- never the live ledger:

  1. crash-boundary sweep over the REAL write ops converges to OLD or NEW
  2. four DISTINCT staleness rejections against the real dimensions (receipt
     pointer, fact source file, settled-id-set + pins snapshot, checker
     source hash)
  3. idempotent replay (no double-counted pin/matrix row)
  4. content rejection: an invalid proposal is refused by validate-facts.py's
     own validate_one, not silently accepted
  5. the gate fails closed on an empty fixture/boundary set
  6. individual guards (state preconditions, corrupt-staging refusal) are
     mutation-verified separately by
     scripts/tests/test-credit-transaction-ledger-mutations.sh

Every scratch tree is built from a COPY of the real `scripts/` +
`artifacts/facts/` + `artifacts/ontology/` + `artifacts/safety-matrix/`
subtrees, never the live directories -- see `build_scratch_base`.
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
REAL_ROOT = _HERE.parent
_SUBTREES = ("scripts", "artifacts/facts", "artifacts/ontology", "artifacts/safety-matrix")

TEST_FACT_ID = "F:ml430-mutation-c86940b52af8159ca9b381d6"


def _load_ledger_engine_from(root: Path):
    """Load a FRESH instance of credit-transaction-ledger.py rooted at `root`.
    Its ROOT/FACTS/TXN_ROOT globals (and the ct/vf/csfs/gsm it loads in turn)
    are computed from `__file__` at import time, so each scratch tree needs
    its own import -- reusing one module instance across scratch trees would
    silently operate on whichever tree it was first loaded from."""
    tag = str(root).replace("/", "_")
    spec = importlib.util.spec_from_file_location(
        f"credit_transaction_ledger_{tag}", root / "scripts" / "credit-transaction-ledger.py"
    )
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def build_scratch_base(dest: Path) -> None:
    for rel in _SUBTREES:
        shutil.copytree(REAL_ROOT / rel, dest / rel)


def _new_fact(fact_id: str, marker: str = "") -> dict:
    old = json.loads((REAL_ROOT / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json")).read_text())
    formal_statement = old["formal"]["statement"]
    return {
        "schema_version": 1,
        "id": fact_id,
        "title": old["title"],
        "statement": old["statement"],
        "formal": {"language": "lean4-surface", "statement": formal_statement, "fragment": old["formal"]["fragment"]},
        "epistemic_status": "proved",
        "external_status": "unknown",
        "depends_on": [],
        "axiom_footprint": [],
        "proof_route": "kernel-lean",
        "evidence": [
            {
                "artifact": "sha256:" + ("0" * 64),
                "check_status": "checked",
                "checkers": ["s6-wire-real-ledger/scratch-gate"],
                "id": "s6-scratch-gate-evidence" + marker,
                "kernel_declaration": "Nat.ModEq.symm",
                "kind": "kernel-term",
                "notes": "SCRATCH-ONLY gate fixture, never applied to the real ledger.",
                "supports": formal_statement,
            }
        ],
        "provenance": old["provenance"],
        "notes": "SCRATCH GATE FIXTURE ONLY (scripts/check-credit-transaction-ledger.py).",
    }


def full_tree_snapshot(root: Path) -> dict:
    """Hash of every file under the covered subtrees EXCEPT `artifacts/.credit-txn`
    (transaction scratch space, not observable ledger state)."""
    snap = {}
    for rel in ("artifacts/facts", "artifacts/ontology", "artifacts/safety-matrix"):
        base = root / rel
        if not base.exists():
            continue
        for p in sorted(base.rglob("*")):
            if p.is_dir():
                continue
            snap[str(p.relative_to(root))] = ctl_hash(p)
    return snap


def ctl_hash(p: Path) -> str:
    import hashlib
    return hashlib.sha256(p.read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# 1. Crash-boundary sweep
# ---------------------------------------------------------------------------
def run_crash_sweep(fact_id: str = TEST_FACT_ID):
    base = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-crash-base-"))
    try:
        build_scratch_base(base)
        old_snapshot = full_tree_snapshot(base)
        new_fact = _new_fact(fact_id)

        total_root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-crash-total-"))
        try:
            shutil.copytree(base, total_root, dirs_exist_ok=True)
            mod = _load_ledger_engine_from(total_root)
            mod.ct.clear_crash_budget()
            mod.run_ledger_transaction(fact_id, new_fact)
            total_ops = mod.ct.ops_performed()
            new_snapshot = full_tree_snapshot(total_root)
        finally:
            shutil.rmtree(total_root, ignore_errors=True)

        if total_ops == 0:
            return [], 0, old_snapshot, new_snapshot

        results = []
        for k in range(0, total_ops):
            scratch = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-crash-scratch-"))
            try:
                shutil.copytree(base, scratch, dirs_exist_ok=True)
                mod = _load_ledger_engine_from(scratch)
                mod.ct.set_crash_budget(k)
                crashed = False
                try:
                    mod.run_ledger_transaction(fact_id, new_fact)
                except mod.ct.SimulatedCrash:
                    crashed = True
                finally:
                    mod.ct.clear_crash_budget()
                if not crashed:
                    results.append((k, "NO-CRASH-RAISED"))
                    continue
                mod.recover()
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
# 2. Staleness fixtures, against the REAL dimensions
# ---------------------------------------------------------------------------
def _fixture_base(fact_id: str):
    root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-fx-"))
    build_scratch_base(root)
    mod = _load_ledger_engine_from(root)
    new_fact = _new_fact(fact_id)
    _, txn_dir = mod.propose(fact_id, new_fact)
    return root, mod, txn_dir


def _fixture_fresh_pass(fact_id: str):
    return _fixture_base(fact_id)


def _fixture_stale_receipt(fact_id: str):
    root, mod, txn_dir = _fixture_base(fact_id)
    # A concurrent lane records a DIFFERENT receipt as authoritative for this
    # fact_id, entirely outside this transaction -- exactly the scenario
    # `_read_receipt_pointer`/`StaleReceiptError` exists to catch.
    ptr = mod._receipt_pointer_path(fact_id)
    mod.ct.io_write_new_file(ptr, mod.ct.hash_bytes(b"receipt-from-another-lane").encode(), label="receipt-pointer")
    return root, mod, txn_dir


def _fixture_stale_source(fact_id: str):
    root, mod, txn_dir = _fixture_base(fact_id)
    fp = mod._fact_path(fact_id)
    data = json.loads(fp.read_text())
    data["notes"] = (data.get("notes") or "") + " -- edited by a concurrent lane"
    fp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    return root, mod, txn_dir


def _fixture_stale_graph(fact_id: str):
    root, mod, txn_dir = _fixture_base(fact_id)
    # A concurrent lane's pins rewrite lands directly (bypassing any
    # transaction) while this one is staged -- the graph fingerprint hashes
    # the pins manifest bytes precisely to catch this. (An earlier version of
    # this fixture only edited an unrelated fact's `notes` field, which
    # changes neither the settled-id-set nor pins.json -- a vacuous control
    # that passed `commit()` for the wrong reason; caught by this gate's own
    # first run, see docs/plan/status/s6-wire-real-ledger.md.)
    pins_path = mod.csfs.PINS
    data = json.loads(pins_path.read_text())
    data["_concurrent_lane_probe"] = "gate fixture: pins rewritten while this transaction was staged"
    pins_path.write_text(json.dumps(data, indent=2) + "\n")
    return root, mod, txn_dir


def _fixture_stale_checker(fact_id: str):
    root, mod, txn_dir = _fixture_base(fact_id)
    # The checker source itself changes between propose() and commit() -- a
    # sibling lane edits gen-safety-matrix.py in the shared tree.
    p = root / "scripts" / "gen-safety-matrix.py"
    p.write_text(p.read_text() + "\n# edited by a concurrent lane (gate fixture)\n")
    return root, mod, txn_dir


STALENESS_FIXTURES = [
    ("stale-receipt", "StaleReceiptError", _fixture_stale_receipt),
    ("stale-source", "StaleSourceError", _fixture_stale_source),
    ("stale-graph", "StaleGraphError", _fixture_stale_graph),
    ("stale-checker", "StaleCheckerError", _fixture_stale_checker),
]


def run_staleness_suite(fixtures=None, fact_id: str = TEST_FACT_ID):
    if fixtures is None:
        fixtures = STALENESS_FIXTURES
    if not fixtures:
        return False, "NO STALENESS FIXTURES REGISTERED", []

    rows = []
    for name, exc_name, builder in fixtures:
        root, mod, txn_dir = builder(fact_id)
        exc_cls = getattr(mod.ct, exc_name)
        try:
            try:
                mod.commit(txn_dir)
                rows.append((name, exc_name, "NOT-REJECTED"))
            except exc_cls:
                rows.append((name, exc_name, "OK"))
            except Exception as e:
                rows.append((name, exc_name, f"WRONG-EXCEPTION:{type(e).__name__}"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    exc_names = {r[1] for r in rows}
    if len(exc_names) != len(rows):
        return False, "STALENESS FIXTURES SHARE AN EXCEPTION CLASS (not distinct)", rows

    ok = all(r[2] == "OK" for r in rows)
    reason = "all reject with distinct named reasons" if ok else "one or more did not reject as expected"
    return ok, reason, rows


def run_fresh_pass_control(fact_id: str = TEST_FACT_ID) -> bool:
    root, mod, txn_dir = _fixture_fresh_pass(fact_id)
    try:
        mod.commit(txn_dir)
        return True
    except Exception:
        return False
    finally:
        shutil.rmtree(root, ignore_errors=True)


# ---------------------------------------------------------------------------
# 3. Idempotent replay: the guard, AND a demonstration that skipping it (by
#    calling propose/commit/apply directly, twice) produces a REAL duplicate.
# ---------------------------------------------------------------------------
def run_idempotence_check(fact_id: str = TEST_FACT_ID):
    root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-idem-"))
    try:
        build_scratch_base(root)
        mod = _load_ledger_engine_from(root)
        new_fact = _new_fact(fact_id)
        r1 = mod.run_ledger_transaction(fact_id, new_fact)
        r2 = mod.run_ledger_transaction(fact_id, new_fact)
        pins = json.loads(mod.csfs.PINS.read_text())
        count = sum(1 for row in pins["pins"] if row["fact_id"] == fact_id)
        return r1 == "applied" and r2 == "noop-already-applied" and count == 1, (r1, r2, count)
    finally:
        shutil.rmtree(root, ignore_errors=True)


def run_guard_skips_recomputation_on_replay(fact_id: str = TEST_FACT_ID):
    """MEASURED, not assumed (docs/plan/status/s6-wire-real-ledger.md): unlike
    the FIXTURE's `dashboards/settled.md` (append-only text), every real
    target this transaction rebuilds -- pins.json, the safety-matrix TSV/MD --
    is a FULL REBUILD KEYED BY fact_id (a dict/list built fresh from current
    ledger state each time), so calling propose()/commit()/apply() directly
    TWICE without run_ledger_transaction's guard does NOT corrupt content --
    confirmed first by finding it does not, see below -- it just does
    real, wasted work. Two of these are measured here:

      1. content stays correct without the guard (count stays 1, not >1) --
         this WOULD be a false claim as "the guard is load-bearing against
         duplication" for these specific targets, so it is reported as what
         it is instead: a property of full-rebuild dashboards, not evidence
         the guard is decorative. A future APPEND-style dashboard (like the
         fixture's) would NOT have this property, which is exactly why the
         guard stays in run_ledger_transaction rather than being removed.
      2. the guard's real, measurable value here: it skips a whole txn
         (cascade recompute + stage + commit + apply) on replay. Without it,
         a second identical call still creates a second `_txn/<id>/` entry
         and re-runs validate_one/rewrite/run_controls for nothing.
    """
    root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-idem-nog-"))
    try:
        build_scratch_base(root)
        mod = _load_ledger_engine_from(root)
        new_fact = _new_fact(fact_id)
        txn_dirs = []
        for _ in range(2):
            _, txn_dir = mod.propose(fact_id, new_fact)
            mod.commit(txn_dir)
            mod.apply(txn_dir)
            txn_dirs.append(txn_dir)
        pins = json.loads(mod.csfs.PINS.read_text())
        count = sum(1 for row in pins["pins"] if row["fact_id"] == fact_id)
        content_idempotent = count == 1
        two_txns_created = len(set(txn_dirs)) == 2
        return content_idempotent and two_txns_created, {
            "pin_rows_for_fact": count,
            "txns_created_without_guard": len(set(txn_dirs)),
        }
    finally:
        shutil.rmtree(root, ignore_errors=True)


# ---------------------------------------------------------------------------
# 4. Content rejection: validate_one, rewrite() drift-refusal, run_controls
# ---------------------------------------------------------------------------
def run_invalid_content_is_rejected(fact_id: str = TEST_FACT_ID) -> tuple[bool, str]:
    root = Path(tempfile.mkdtemp(prefix="credit-txn-ledger-invalid-"))
    try:
        build_scratch_base(root)
        mod = _load_ledger_engine_from(root)
        bad_fact = _new_fact(fact_id)
        bad_fact["depends_on"] = ["F:this-fact-id-does-not-exist-anywhere"]
        try:
            mod.compute_cascade(fact_id, bad_fact)
            return False, "compute_cascade ACCEPTED a fact with a dangling depends_on edge"
        except mod.LedgerCascadeError as e:
            return True, str(e)
    finally:
        shutil.rmtree(root, ignore_errors=True)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--empty-fixtures", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--empty-boundaries", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args(argv)

    if args.empty_fixtures:
        ok, reason, _rows = run_staleness_suite(fixtures=[])
        print(f"CREDIT_TXN_LEDGER_GATE|{reason}", file=sys.stderr)
        return 1 if not ok else 0
    if args.empty_boundaries:
        ok, reason = evaluate_crash_sweep([], 0)
        print(f"CREDIT_TXN_LEDGER_GATE|{reason}", file=sys.stderr)
        return 1 if not ok else 0

    failures = []

    results, total_ops, old_snap, new_snap = run_crash_sweep()
    crash_ok, crash_reason = evaluate_crash_sweep(results, total_ops)
    print(f"CREDIT_TXN_LEDGER_GATE|crash-sweep|ops={total_ops}|{crash_reason}")
    if not crash_ok:
        failures.append(f"crash-sweep: {crash_reason}")
    if old_snap == new_snap:
        failures.append("crash-sweep: OLD and NEW snapshots are identical -- the sweep tests nothing")

    stale_ok, stale_reason, stale_rows = run_staleness_suite()
    print(f"CREDIT_TXN_LEDGER_GATE|staleness|{stale_reason}|{stale_rows}")
    if not stale_ok:
        failures.append(f"staleness: {stale_reason}")

    fresh_ok = run_fresh_pass_control()
    print(f"CREDIT_TXN_LEDGER_GATE|fresh-pass-control|ok={fresh_ok}")
    if not fresh_ok:
        failures.append("fresh-pass-control: a genuinely fresh transaction was rejected")

    idem_ok, idem_detail = run_idempotence_check()
    print(f"CREDIT_TXN_LEDGER_GATE|idempotence|ok={idem_ok}|{idem_detail}")
    if not idem_ok:
        failures.append(f"idempotence: {idem_detail}")

    dup_ok, dup_detail = run_guard_skips_recomputation_on_replay()
    print(f"CREDIT_TXN_LEDGER_GATE|idempotence-guard-skips-recomputation|ok={dup_ok}|{dup_detail}")
    if not dup_ok:
        failures.append(f"idempotence-guard-skips-recomputation: {dup_detail}")

    inv_ok, inv_detail = run_invalid_content_is_rejected()
    print(f"CREDIT_TXN_LEDGER_GATE|content-rejection|ok={inv_ok}")
    if not inv_ok:
        failures.append(f"content-rejection: {inv_detail}")

    if failures:
        for f in failures:
            print(f"CREDIT_TXN_LEDGER_GATE|FAIL|{f}", file=sys.stderr)
        return 1
    print("CREDIT_TXN_LEDGER_GATE|PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
