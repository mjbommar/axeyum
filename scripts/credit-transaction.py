#!/usr/bin/env python3
"""Crash-safe credit transaction engine — L0 phase S6.

docs/plan/trusted-library-safety-roadmap-2026-08-30.md, section S6:

    The checked receipt, fact transition, dependency-derived cascade, and
    generated dashboards commit through one crash-safe transaction. Checkers
    operate on a fresh read of the proposed state, not mutable in-process
    assumptions.

    Exit: interruption at every write boundary leaves either old state or a
    complete new state; replay is idempotent; stale receipt, source, graph,
    or checker versions reject.

This module is a STANDALONE, self-contained transaction engine over a small
fixture "ledger" directory shape (facts/, receipts/, pins/, graph/,
dashboards/) that mirrors the real one's write fan-out without touching it —
see docs/plan/status/l0-s6-credit-transaction.md for why, and for how a later
lane would wire this into the real `artifacts/facts/` flip.

Design (two-phase commit over a plain filesystem, since POSIX gives us no
multi-file atomic rename):

  propose()  -- compute the desired end state, write it to a scratch
                `_txn/<id>/staged/` directory. Nothing under the ledger's
                real paths is touched. Every durable write goes through
                `io_write_new_file`/`io_replace`/`io_remove`, the three
                fault-injectable primitives the crash sweep interrupts.
  commit()   -- re-read the transaction's journal FRESH from disk (never the
                in-process object `propose()` returned), re-check the four
                staleness dimensions against fresh disk reads, then flip the
                journal's `status` field from "prepared" to "committed" with
                one atomic file replace. That flip is the single point of no
                return.
  apply()    -- re-read the journal fresh, verify every staged blob's hash
                still matches what commit() approved (torn/corrupted staging
                is refused before ANY target is touched), then replace each
                target file with its staged counterpart. Each target is
                skipped if it already matches the staged hash, which is what
                makes replay of an already-applied transaction a no-op.
  recover()  -- scan `_txn/` and reconcile every transaction found: a
                "prepared" one (crashed before the commit flip) is rolled
                back by deleting its scratch directory, since no target was
                ever touched; a "committed" or "applied" one is rolled
                forward by calling `apply()` again, which is idempotent.

`run_transaction()` is the end-to-end entry point a caller uses: it also
holds the higher-level idempotence guard (a fact_id+receipt pair already
recorded as applied short-circuits before any cascade recomputation, so a
replayed call cannot double-append a cascade/dashboard entry).
"""
from __future__ import annotations

import dataclasses
import hashlib
import json
import os
import shutil
import sys
import time
from pathlib import Path
from typing import Optional

CURRENT_CHECKER_VERSION = "credit-transaction/1"


# ---------------------------------------------------------------------------
# Exceptions. Four DISTINCT staleness exceptions on purpose -- see the S6
# brief and CLAUDE.md's "six of seven guards ... rejected through one shared
# check": a checker that cannot tell WHICH thing went stale is one guard
# wearing four names, and a mutation deleting any one of the four checks must
# be caught by exactly the test that names it.
# ---------------------------------------------------------------------------
class SimulatedCrash(Exception):
    """Raised by the fault-injection IO layer when the op budget runs out."""


class TransactionStateError(Exception):
    pass


class StaleReceiptError(Exception):
    pass


class StaleSourceError(Exception):
    pass


class StaleGraphError(Exception):
    pass


class StaleCheckerError(Exception):
    pass


class CorruptStagingError(Exception):
    pass


# ---------------------------------------------------------------------------
# Fault-injectable low-level IO. Every durable write in this module goes
# through exactly one of these three functions, so the crash-boundary sweep
# in scripts/tests/test-credit-transaction.py can interrupt at ANY one of
# them -- and only them -- and nowhere else in the process.
# ---------------------------------------------------------------------------
class _OpBudget:
    def __init__(self) -> None:
        self.remaining: Optional[int] = None
        self.count = 0
        self.log: list[str] = []

    def tick(self, label: str) -> None:
        self.count += 1
        self.log.append(label)
        if self.remaining is not None:
            if self.remaining <= 0:
                raise SimulatedCrash(
                    f"simulated crash before op #{self.count} ({label})"
                )
            self.remaining -= 1


_budget = _OpBudget()


def set_crash_budget(n: int) -> None:
    _budget.remaining = n
    _budget.count = 0
    _budget.log = []


def clear_crash_budget() -> None:
    _budget.remaining = None
    _budget.count = 0
    _budget.log = []


def ops_performed() -> int:
    return _budget.count


def ops_log() -> list[str]:
    return list(_budget.log)


def io_write_new_file(path: Path, data: bytes, label: str = "write") -> None:
    """Write `data` to `path` durably: write-to-temp, fsync, atomic rename.

    Two fault-injection ticks: the crash sweep can land between the fsync'd
    temp write and the rename (leaving `path` untouched -- OLD), or after the
    rename (leaving `path` fully replaced -- NEW). There is no tick that can
    land "mid-file": `path` is never opened for in-place writing.
    """
    _budget.tick(f"write-temp:{label}:{path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f"{path.name}.tmp-{os.getpid()}-{time.time_ns()}")
    with open(tmp, "wb") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    _budget.tick(f"rename:{label}:{path}")
    os.replace(tmp, path)


def io_replace(src: Path, dst: Path, label: str = "replace") -> None:
    """Atomically install `src` as `dst` (one fault-injection tick)."""
    _budget.tick(f"install:{label}:{dst}")
    dst.parent.mkdir(parents=True, exist_ok=True)
    os.replace(src, dst)


def io_remove(path: Path, label: str = "remove") -> None:
    if path.exists():
        _budget.tick(f"remove:{label}:{path}")
        os.remove(path)


# ---------------------------------------------------------------------------
# Hashing helpers
# ---------------------------------------------------------------------------
def hash_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_file(path: Path) -> str:
    if not path.exists():
        return hash_bytes(b"")
    return hash_bytes(path.read_bytes())


# ---------------------------------------------------------------------------
# Journal
# ---------------------------------------------------------------------------
@dataclasses.dataclass
class Inputs:
    receipt_sha256: str
    receipt_pointer_sha256: str
    source_sha256: str
    graph_sha256: str
    checker_version: str

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)

    @staticmethod
    def from_dict(d: dict) -> "Inputs":
        return Inputs(**d)


@dataclasses.dataclass
class WriteOp:
    relpath: str
    staged_name: str
    sha256: str

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)

    @staticmethod
    def from_dict(d: dict) -> "WriteOp":
        return WriteOp(**d)


@dataclasses.dataclass
class Journal:
    txn_id: str
    fact_id: str
    status: str  # "prepared" | "committed" | "applied"
    inputs: Inputs
    writes: list

    def to_dict(self) -> dict:
        return {
            "txn_id": self.txn_id,
            "fact_id": self.fact_id,
            "status": self.status,
            "inputs": self.inputs.to_dict(),
            "writes": [w.to_dict() for w in self.writes],
        }

    @staticmethod
    def from_dict(d: dict) -> "Journal":
        return Journal(
            txn_id=d["txn_id"],
            fact_id=d["fact_id"],
            status=d["status"],
            inputs=Inputs.from_dict(d["inputs"]),
            writes=[WriteOp.from_dict(w) for w in d["writes"]],
        )


def _journal_path(txn_dir: Path) -> Path:
    return txn_dir / "journal.json"


# `_LAST_STAGED_JOURNAL` exists ONLY so the fresh-read guard is testable: it
# is the in-process object a careless implementation would be tempted to
# reuse at commit time instead of re-reading the journal from disk. Nothing
# in this module's own commit()/apply() logic ever reads from it.
_LAST_STAGED_JOURNAL: dict = {}


def _load_journal_fresh(txn_dir: Path) -> Journal:
    return Journal.from_dict(json.loads(_journal_path(txn_dir).read_text()))


def _write_journal(txn_dir: Path, journal: Journal, label: str) -> None:
    io_write_new_file(
        _journal_path(txn_dir),
        json.dumps(journal.to_dict(), indent=2, sort_keys=True).encode(),
        label=label,
    )


# ---------------------------------------------------------------------------
# Applied-transaction registry (higher-level idempotence: fact_id -> the
# receipt sha256 already folded in)
# ---------------------------------------------------------------------------
def _applied_registry_path(root: Path) -> Path:
    return root / "_txn" / "applied.json"


def load_applied_registry(root: Path) -> dict:
    p = _applied_registry_path(root)
    if not p.exists():
        return {}
    return json.loads(p.read_text())


def _write_applied_registry(root: Path, registry: dict) -> None:
    io_write_new_file(
        _applied_registry_path(root),
        json.dumps(registry, sort_keys=True, indent=2).encode(),
        label="applied-registry",
    )


# ---------------------------------------------------------------------------
# Receipt pointer: "the currently-authoritative receipt for this fact_id",
# recorded by a checker BEFORE a transaction opens. This is what "stale
# receipt" checks against -- distinct from "stale source" (the fact/kernel
# content itself changed) and "stale graph" (the cascade snapshot changed).
# ---------------------------------------------------------------------------
def _receipt_pointer_path(root: Path, fact_id: str) -> Path:
    return root / "receipts" / "latest" / f"{fact_id}.sha256"


def record_latest_receipt(root: Path, fact_id: str, receipt_bytes: bytes) -> None:
    io_write_new_file(
        _receipt_pointer_path(root, fact_id),
        hash_bytes(receipt_bytes).encode(),
        label="receipt-pointer",
    )


def _read_receipt_pointer(root: Path, fact_id: str) -> str:
    p = _receipt_pointer_path(root, fact_id)
    if not p.exists():
        return hash_bytes(b"")
    return p.read_text().strip()


# ---------------------------------------------------------------------------
# Ledger fixture helpers (the "facts/pins/graph/dashboards" fan-out)
# ---------------------------------------------------------------------------
def _fact_path(root: Path, fact_id: str) -> Path:
    return root / "facts" / f"{fact_id}.json"


def init_ledger(root: Path, fact_id: str) -> None:
    """Create a minimal fixture ledger with one OPEN fact, ready to be
    transitioned to `proved` by `run_transaction`."""
    (root / "facts").mkdir(parents=True, exist_ok=True)
    (root / "pins").mkdir(parents=True, exist_ok=True)
    (root / "graph").mkdir(parents=True, exist_ok=True)
    (root / "dashboards").mkdir(parents=True, exist_ok=True)
    (root / "receipts").mkdir(parents=True, exist_ok=True)
    _fact_path(root, fact_id).write_text(
        json.dumps({"fact_id": fact_id, "epistemic_status": "open"}, indent=2)
    )
    (root / "pins" / "pins.json").write_text(json.dumps({}, indent=2))
    (root / "graph" / "graph.json").write_text(
        json.dumps({"settled": []}, indent=2)
    )
    (root / "dashboards" / "settled.md").write_text("# Settled facts\n")


def cascade_append_settled(root: Path, fact_id: str, receipt_bytes: bytes):
    """Compute the desired new bytes for every write target, reading CURRENT
    on-disk content. This is what makes a missing idempotence guard produce a
    real, double-counted bug on replay: called twice without a short-circuit,
    it appends `fact_id` to the cascade/dashboard a second time."""
    fact = json.loads(_fact_path(root, fact_id).read_text())
    fact["epistemic_status"] = "proved"
    fact["receipt_sha256"] = hash_bytes(receipt_bytes)
    new_fact = json.dumps(fact, indent=2, sort_keys=True).encode()

    graph = json.loads((root / "graph" / "graph.json").read_text())
    graph.setdefault("settled", [])
    graph["settled"].append(fact_id)
    new_graph = json.dumps(graph, indent=2, sort_keys=True).encode()

    pins = json.loads((root / "pins" / "pins.json").read_text())
    pins[fact_id] = {"statement_sha256": hash_bytes(fact_id.encode())}
    new_pins = json.dumps(pins, indent=2, sort_keys=True).encode()

    dash = (root / "dashboards" / "settled.md").read_text()
    new_dash = (dash + f"- {fact_id}\n").encode()

    return new_fact, new_graph, new_pins, new_dash


# ---------------------------------------------------------------------------
# Two-phase commit
# ---------------------------------------------------------------------------
def propose_transaction(
    root: Path,
    fact_id: str,
    receipt_bytes: bytes,
    new_fact: bytes,
    new_graph: bytes,
    new_pins: bytes,
    new_dashboard: bytes,
    checker_version: str = CURRENT_CHECKER_VERSION,
):
    """Phase 1: stage the desired end state. Touches only `_txn/<id>/`."""
    txn_id = f"txn-{hash_bytes(receipt_bytes)[:12]}-{time.time_ns()}"
    txn_dir = root / "_txn" / txn_id
    staged_dir = txn_dir / "staged"

    inputs = Inputs(
        receipt_sha256=hash_bytes(receipt_bytes),
        receipt_pointer_sha256=_read_receipt_pointer(root, fact_id),
        source_sha256=hash_file(_fact_path(root, fact_id)),
        graph_sha256=hash_file(root / "graph" / "graph.json"),
        checker_version=checker_version,
    )

    targets = {
        f"facts/{fact_id}.json": new_fact,
        "graph/graph.json": new_graph,
        "pins/pins.json": new_pins,
        "dashboards/settled.md": new_dashboard,
        f"receipts/{fact_id}.json": receipt_bytes,
        # The pointer flip is part of THIS transaction, not a pre-step: a
        # receipt should never be marked authoritative unless the fact/
        # graph/pins/dashboard update it backs actually committed. The
        # staleness fixture simulates a competing write to this same path
        # from OUTSIDE any transaction (`record_latest_receipt`, below) to
        # model "another lane recorded a newer receipt while this one was
        # in flight".
        f"receipts/latest/{fact_id}.sha256": hash_bytes(receipt_bytes).encode(),
    }

    writes = []
    for relpath in sorted(targets):
        data = targets[relpath]
        staged_name = relpath.replace("/", "__")
        io_write_new_file(staged_dir / staged_name, data, label=f"stage:{relpath}")
        writes.append(
            WriteOp(relpath=relpath, staged_name=staged_name, sha256=hash_bytes(data))
        )

    journal = Journal(
        txn_id=txn_id, fact_id=fact_id, status="prepared", inputs=inputs, writes=writes
    )
    _write_journal(txn_dir, journal, label="journal-prepared")
    _LAST_STAGED_JOURNAL[str(txn_dir)] = journal
    return txn_id, txn_dir


def _check_receipt_fresh(journal: Journal, root: Path) -> None:
    """A transaction is staged against whatever receipt pointer is
    authoritative AT PROPOSAL TIME (possibly "no receipt yet", for a fact's
    first transaction). If a concurrent lane has since recorded a DIFFERENT
    receipt as authoritative for this fact_id -- via `record_latest_receipt`,
    outside this transaction entirely -- this transaction's view is stale,
    regardless of whether its own receipt would otherwise be fine."""
    current_pointer = _read_receipt_pointer(root, journal.fact_id)
    if current_pointer != journal.inputs.receipt_pointer_sha256:
        raise StaleReceiptError(
            f"stale receipt: authoritative receipt for {journal.fact_id} is now "
            f"{current_pointer[:12]}, this transaction staged against "
            f"{journal.inputs.receipt_pointer_sha256[:12]}"
        )


def _check_source_fresh(journal: Journal, root: Path) -> None:
    current = hash_file(_fact_path(root, journal.fact_id))
    if current != journal.inputs.source_sha256:
        raise StaleSourceError(
            f"stale source: facts/{journal.fact_id}.json changed on disk since "
            f"staging (staged against {journal.inputs.source_sha256[:12]}, now "
            f"{current[:12]})"
        )


def _check_graph_fresh(journal: Journal, root: Path) -> None:
    current = hash_file(root / "graph" / "graph.json")
    if current != journal.inputs.graph_sha256:
        raise StaleGraphError(
            "stale graph: dependency-derived cascade graph changed since staging "
            f"(staged against {journal.inputs.graph_sha256[:12]}, now {current[:12]})"
        )


def _check_checker_fresh(journal: Journal) -> None:
    if journal.inputs.checker_version != CURRENT_CHECKER_VERSION:
        raise StaleCheckerError(
            "stale checker: transaction staged against checker version "
            f"{journal.inputs.checker_version!r}, running checker is "
            f"{CURRENT_CHECKER_VERSION!r}"
        )


def commit(root: Path, txn_dir: Path) -> Journal:
    """Phase 2: the point of no return. Re-reads the journal FRESH from disk
    -- never the object `propose_transaction` returned -- so a concurrent
    change to the receipt pointer, source, graph, or checker version between
    proposal and commit is what gets checked, not a stale in-process value."""
    journal = _load_journal_fresh(txn_dir)  # GUARD: fresh-read, not cached
    if journal.status != "prepared":
        raise TransactionStateError(
            f"cannot commit txn {journal.txn_id}: status is {journal.status!r}, "
            "expected 'prepared'"
        )
    _check_receipt_fresh(journal, root)  # GUARD: stale receipt
    _check_source_fresh(journal, root)  # GUARD: stale source
    _check_graph_fresh(journal, root)  # GUARD: stale graph
    _check_checker_fresh(journal)  # GUARD: stale checker
    journal.status = "committed"
    _write_journal(txn_dir, journal, label="journal-committed")
    return journal


def _verify_staged_integrity(txn_dir: Path, pending: list) -> None:
    """Check every NOT-YET-APPLIED write's staged blob against the hash
    `commit()` approved. `pending` deliberately excludes writes whose target
    already matches -- `io_replace` MOVES the staged file, so on a re-entrant
    `apply()` (recovering from a mid-loop crash) the staged file for an
    already-applied write is legitimately gone, and checking it would reject
    a perfectly healthy resume as "corrupt"."""
    for w in pending:
        staged_path = txn_dir / "staged" / w.staged_name
        actual = hash_file(staged_path)
        if actual != w.sha256:
            raise CorruptStagingError(
                f"corrupt staging: {w.relpath} staged content hash {actual[:12]} "
                f"does not match journal-recorded {w.sha256[:12]} -- refusing to "
                "install any target from this transaction"
            )


def apply(root: Path, txn_dir: Path) -> Journal:
    """Phase 3: install the staged files. Re-reads the journal fresh. Safe to
    call repeatedly: a target already matching its staged hash is skipped, so
    a crash mid-loop plus a re-call finishes exactly the remaining files."""
    journal = _load_journal_fresh(txn_dir)
    if journal.status not in ("committed", "applied"):
        raise TransactionStateError(
            f"cannot apply txn {journal.txn_id}: status is {journal.status!r}, "
            "expected 'committed' or 'applied' -- commit() must run first"
        )

    ordered = sorted(journal.writes, key=lambda w: w.relpath)
    pending = [w for w in ordered if hash_file(root / w.relpath) != w.sha256]
    _verify_staged_integrity(txn_dir, pending)  # GUARD: corrupt staging

    for w in pending:
        target = root / w.relpath
        staged = txn_dir / "staged" / w.staged_name
        io_replace(staged, target, label=f"apply:{w.relpath}")

    registry = load_applied_registry(root)
    registry[journal.fact_id] = journal.inputs.receipt_sha256
    _write_applied_registry(root, registry)

    if journal.status != "applied":
        journal.status = "applied"
        _write_journal(txn_dir, journal, label="journal-applied")
    return journal


def recover(root: Path) -> list:
    """Scan every open transaction under `_txn/` and reconcile it: a
    'prepared' one (crashed before the commit flip) is rolled back by
    deleting its scratch dir; a 'committed'/'applied' one is rolled forward
    by re-running apply(), which is idempotent."""
    txn_root = root / "_txn"
    actions: list = []
    if not txn_root.exists():
        return actions
    for entry in sorted(txn_root.iterdir()):
        if not entry.is_dir():
            continue
        journal_path = _journal_path(entry)
        if not journal_path.exists():
            shutil.rmtree(entry, ignore_errors=True)
            actions.append(f"rollback (no journal written): {entry.name}")
            continue
        try:
            journal = _load_journal_fresh(entry)
        except Exception:
            shutil.rmtree(entry, ignore_errors=True)
            actions.append(f"rollback (unreadable journal): {entry.name}")
            continue
        if journal.status == "prepared":
            shutil.rmtree(entry, ignore_errors=True)
            actions.append(f"rollback (never committed): {entry.name}")
        elif journal.status in ("committed", "applied"):
            apply(root, entry)
            actions.append(f"roll-forward (applied): {entry.name}")
        else:
            actions.append(f"UNKNOWN status {journal.status!r}: {entry.name}")
    return actions


# ---------------------------------------------------------------------------
# End-to-end entry point
# ---------------------------------------------------------------------------
def run_transaction(root: Path, fact_id: str, receipt_bytes: bytes) -> str:
    """Fold `receipt_bytes` into the ledger for `fact_id`: flip the fact,
    extend the cascade graph, refresh pins and the dashboard, all atomically.

    Returns "noop-already-applied" or "applied". The idempotence guard lives
    HERE, before the cascade is even recomputed: replaying the same
    (fact_id, receipt) pair a second time must not re-derive and re-append a
    cascade/dashboard entry.
    """
    registry = load_applied_registry(root)
    receipt_sha = hash_bytes(receipt_bytes)
    if registry.get(fact_id) == receipt_sha:  # GUARD: idempotent replay
        return "noop-already-applied"

    new_fact, new_graph, new_pins, new_dashboard = cascade_append_settled(
        root, fact_id, receipt_bytes
    )
    _, txn_dir = propose_transaction(
        root, fact_id, receipt_bytes, new_fact, new_graph, new_pins, new_dashboard
    )
    commit(root, txn_dir)
    apply(root, txn_dir)
    return "applied"


# ---------------------------------------------------------------------------
# CLI (manual poking / demo only -- the gate and tests drive the library
# functions directly)
# ---------------------------------------------------------------------------
def _cli_main(argv: list) -> int:
    import argparse

    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="cmd", required=True)

    p_init = sub.add_parser("init-ledger")
    p_init.add_argument("root", type=Path)
    p_init.add_argument("fact_id")

    p_run = sub.add_parser("run")
    p_run.add_argument("root", type=Path)
    p_run.add_argument("fact_id")
    p_run.add_argument("receipt_file", type=Path)

    p_rec = sub.add_parser("recover")
    p_rec.add_argument("root", type=Path)

    args = p.parse_args(argv)
    if args.cmd == "init-ledger":
        init_ledger(args.root, args.fact_id)
        print(f"CREDIT_TXN|init-ledger|root={args.root}|fact_id={args.fact_id}")
        return 0
    if args.cmd == "run":
        result = run_transaction(
            args.root, args.fact_id, args.receipt_file.read_bytes()
        )
        print(f"CREDIT_TXN|run|fact_id={args.fact_id}|result={result}")
        return 0
    if args.cmd == "recover":
        actions = recover(args.root)
        for a in actions:
            print(f"CREDIT_TXN|recover|{a}")
        print(f"CREDIT_TXN|recover|actions={len(actions)}")
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(_cli_main(sys.argv[1:]))
