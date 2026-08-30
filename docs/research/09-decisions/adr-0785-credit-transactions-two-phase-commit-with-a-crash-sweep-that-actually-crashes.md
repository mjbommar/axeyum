# ADR-0785: credit transactions are two-phase-commit, verified by a crash sweep that actually crashes

Status: accepted
Date: 2026-08-30
Index-summary: L0 S6 of ADR-0717. `scripts/credit-transaction.py` is a
fault-injectable two-phase-commit engine over a fixture ledger; the gate
interrupts at all 26 measured write ops and requires every one to converge to
byte-identical OLD or NEW state, plus four independently-mutation-verified
staleness guards (receipt pointer, source, graph, checker version) and an
idempotent-replay short-circuit.
Lane: `l0-s6-credit-transaction`

Implements: [ADR-0717](adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md)
phase S6, specified in
[`docs/plan/trusted-library-safety-roadmap-2026-08-30.md`](../../plan/trusted-library-safety-roadmap-2026-08-30.md)

## Context

S6's exit criterion is specific about mechanism, not just outcome:

> The checked receipt, fact transition, dependency-derived cascade, and
> generated dashboards commit through one crash-safe transaction. Checkers
> operate on a fresh read of the proposed state, not mutable in-process
> assumptions.
>
> Exit: interruption at every write boundary leaves either old state or a
> complete new state; replay is idempotent; stale receipt, source, graph, or
> checker versions reject.

Today, flipping a fact to `proved` touches several files one at a time — the
fact JSON, `artifacts/ontology/settled-fact-statement-pins.json`, and several
generated dashboards — with no journal and no fresh-read discipline. An
interruption partway leaves a state no checker anticipated.

CLAUDE.md's own retrospective is explicit about what "verified" has to mean
here: a checker that cannot fail is worse than none, and a suite where
deleting six of seven guards leaves everything green means the guards were
never independently load-bearing. A crash-safety claim carries the same risk
in a sharper form — "atomic" is usually asserted, never demonstrated, because
demonstrating it means actually interrupting the process at a real write
boundary and inspecting what is left. This ADR is that demonstration, not a
description of intended behavior.

## Decision

Build the mechanism as a standalone, self-contained engine
(`scripts/credit-transaction.py`) over a small fixture ledger shape
(`facts/`, `receipts/`, `pins/`, `graph/`, `dashboards/`) rather than wiring
directly into `artifacts/facts/` in this phase — this lane's scope is the
transaction mechanism and its verification; wiring it into the real fact
flip (which also touches `scripts/validate-facts.py` and the real pins file,
owned elsewhere) is follow-on work for whoever owns that surface.

**Two-phase commit**, since POSIX gives no multi-file atomic rename:

1. `propose_transaction()` computes every write target's desired bytes and
   stages them under `_txn/<id>/staged/`, plus a journal recording each
   write's target path, staged filename and sha256, and an `inputs` snapshot
   (receipt pointer hash, fact-source hash, graph hash, checker version).
   Nothing under the ledger's real paths is touched.
2. `commit()` **re-reads the journal fresh from disk** — never the
   in-process object `propose_transaction` returned — checks all four
   staleness dimensions against fresh reads, then flips the journal's
   `status` field from `prepared` to `committed` with one atomic file
   replace. That flip is the single point of no return.
3. `apply()` re-reads the journal fresh, verifies every NOT-YET-APPLIED
   staged blob's hash still matches what `commit()` approved (refusing
   before touching any target if not), then installs each target. A target
   already matching its staged hash is skipped, which is what makes
   re-applying an already-applied transaction a no-op.
4. `recover()` scans `_txn/` and reconciles every transaction found: a
   `prepared` one (crashed before the commit flip) is rolled back by
   deleting its scratch directory, since no target was ever touched; a
   `committed`/`applied` one is rolled forward by calling `apply()` again.

Every durable write goes through exactly one of three fault-injectable
primitives (`io_write_new_file`, `io_replace`, `io_remove`), so the crash
sweep can interrupt at any one of them and nowhere else.

**Four staleness checks, four exception classes**, deliberately not one
shared "stale" check parameterized by kind — `StaleReceiptError`,
`StaleSourceError`, `StaleGraphError`, `StaleCheckerError`. Staleness of the
receipt is checked against a receipt POINTER file
(`receipts/latest/<fact_id>.sha256`) written by a checker before a
transaction opens, not against the transaction's own copy of the receipt —
this lets a concurrent lane's newer receipt for the same fact invalidate an
in-flight transaction without the two ever touching the same file at the
same instant.

**Idempotent replay** lives in `run_transaction()`, before the cascade is
even recomputed: an `applied.json` registry maps `fact_id -> receipt sha256
already folded in`, and a matching entry short-circuits to a no-op. This
matters because the cascade/dashboard content is COMPUTED from current disk
state at call time (`cascade_append_settled`), so a replay without this
guard would re-read the already-updated dashboard and append a second entry
— confirmed by a test that removes the guard by calling
`propose/commit/apply` directly, twice, and observing the real duplicate.

## What was measured, not asserted

**The crash sweep.** One full `run_transaction()` call over the fixture
ledger performs **26** low-level write ops. The sweep re-runs the
transaction once per op index with a fault injected at that exact op,
confirms `SimulatedCrash` fires, calls `recover()`, and diffs the resulting
ledger tree (excluding `_txn/`) against BOTH the pre-transaction and
post-transaction snapshots. All 26 op indices resolve to byte-identical OLD
or NEW state; none resolve to neither. The gate (`scripts/
check-credit-transaction.py`) fails closed if the sweep ever finds zero
boundaries, or if either outcome (OLD, NEW) never occurs across the sweep —
a sweep that always resolves to NEW, for instance, would mean nothing before
the commit flip was actually tested.

**Fresh read.** Constructed directly: after staging, the on-disk `txn_id`
field is overwritten with a sentinel that the in-process cached `Journal`
object does not have. `commit()` is then shown to preserve the on-disk
sentinel when it re-serializes the journal — proof it read fresh, not
cached. `txn_id` was chosen deliberately because no staleness check or
status precondition reads it, so this demonstrates the fresh-read guard in
isolation; an earlier version reused `checker_version` and turned out to be
entangled with the stale-checker guard (removing THAT guard broke the
fresh-read test too, for an unrelated reason) — worth recording because it
is exactly the kind of accidental guard-sharing this repository has been
burned by before.

**Staleness.** Four fixtures, each genuinely stale along exactly one
dimension while the other three stay fresh, each asserted to raise its own
exception class (not merely "an exception"). A fifth, fully-fresh fixture
must commit without rejecting — otherwise "every staleness fixture rejects"
could be true because `commit()` rejects everything.

**Mutation table.** `scripts/tests/test-credit-transaction-mutations.sh`
copies the engine, gate, and test file to a scratch directory (never the
shared checkout — see CLAUDE.md's warning that a mutant left in a tracked
file breaks every other lane's concurrent build), clears `__pycache__`
before each run (equal-size mutants written back to back are exactly the
shape that reports the previous mutant's result if the cache is not
cleared), deletes one of nine guards at a time, and requires that mutation
kill EXACTLY its own designated canary from a fixed set of nine narrow
tests — never zero (a decorative guard), never more than one (guards
sharing a check). All nine pass:

| guard | canary |
|---|---|
| fresh-read (commit uses disk, not cache) | `FreshReadTests.test_commit_uses_fresh_disk_journal_not_cached_object` |
| stale-receipt check | `StalenessFixtureTests.test_stale_receipt_raises_only_stale_receipt_error` |
| stale-source check | `StalenessFixtureTests.test_stale_source_raises_only_stale_source_error` |
| stale-graph check | `StalenessFixtureTests.test_stale_graph_raises_only_stale_graph_error` |
| stale-checker check | `StalenessFixtureTests.test_stale_checker_raises_only_stale_checker_error` |
| commit status precondition | `GuardBehaviorTests.test_commit_rejects_a_non_prepared_transaction` |
| apply status precondition | `GuardBehaviorTests.test_apply_rejects_an_uncommitted_transaction` |
| corrupt-staging integrity check | `GuardBehaviorTests.test_apply_refuses_corrupted_staged_content` |
| idempotent-replay short-circuit | `IdempotenceTests.test_replay_is_idempotent` |

The canary set is intentionally narrower than the full 27-test suite: the
broader integration tests (the "all four fixtures reject" aggregate, the
subprocess-level CLI exit-code checks) legitimately exercise more than one
guard by design, and running mutation verification against them would make
every staleness-guard deletion report two or three kills — a real property
of those tests, but not a measurement of whether the nine guards are
SEPARATELY load-bearing, which is the question this table answers.

**The gate fails on absence.** `scripts/check-credit-transaction.py
--empty-fixtures` and `--empty-boundaries` each exit 1 with a named reason
(`NO STALENESS FIXTURES REGISTERED`, `NO BOUNDARIES ENUMERATED`), tested at
both the function level and via a subprocess check of the real CLI exit
code.

## Alternatives

**Wire directly into `artifacts/facts/` and the real pins/dashboards in this
phase.** Rejected for this lane: the task scope explicitly excludes
`scripts/validate-facts.py` and `artifacts/facts/*.json` semantics, which
belong to lanes already working that surface. The engine's ledger shape
(facts/pins/graph/dashboards/receipts, one JSON file per fact) mirrors the
real one closely enough that wiring it in is a follow-on integration task,
not a redesign.

**A single generic `StaleInputError(kind)` instead of four exception
classes.** Rejected: this is exactly the "six of seven guards reject through
one shared check" shape CLAUDE.md warns about. Four classes make "which
guard fired" testable as a type, not a string comparison a future refactor
could silently break.

**Mutation-test against the full 27-test suite instead of a curated nine.**
Rejected after measuring it: several staleness-guard deletions killed 2-3
tests at once because integration tests legitimately re-exercise multiple
guards, which would have made "exactly one" impossible to satisfy honestly
without either weakening the integration tests or declaring the requirement
unmeetable. A disjoint, guard-scoped canary set is the standard fix and is
recorded as such rather than silently narrowed.

## Consequences

The mechanism, its crash sweep, its staleness fixtures, and its mutation
table all live under this lane's exclusive paths (`scripts/credit-transaction.py`,
`scripts/check-credit-transaction.py`, `scripts/tests/test-credit-transaction*`,
`artifacts/credit-transaction/`) and are registered in both `justfile` and
`scripts/check.sh`. What this transaction does NOT make atomic: the receipt
pointer write for a fact's FIRST-EVER transaction is itself one of the
transaction's own write targets (so it IS covered), but a caller who writes
to `receipts/latest/<fact_id>.sha256` via `record_latest_receipt()` outside
any transaction — which is exactly what the stale-receipt fixture does to
simulate a concurrent lane — is by construction not covered by this or any
transaction; that write is the "external checker already validated this"
event the staleness check exists to detect changes to, not something this
mechanism protects.

Wiring this engine into the real fact-flip path (the fact JSON, the settled
pins file, and the generated dashboards) is not done here and needs a
separate task against those owners.
