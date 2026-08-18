# ADR-0472: Isolated semantic replay of authoritative admission

Status: accepted
Date: 2026-08-18
Index-summary: Reconstruct the historical open fact in a disposable clean worktree and freshly reproduce selection, execution, crash recovery, admission, and readiness without reusing receipts

## Context

After an authoritative fact is admitted, the live ledger correctly refuses to
select it again. Replaying its execution in the settled checkout is therefore
neither possible nor desirable. Checking the original receipts again proves
historical integrity, but it does not prove that a second clean environment can
reproduce the acquisition.

The result bytes also cannot be required to match blindly. An execution receipt
binds its clean Git commit, and the admitted fact binds that execution identity.
A new clean checkout should have a new execution and transaction identity while
reproducing the same selected fact, registered operation, certified result,
acceptance policy, durable transition, and readiness effect.

## Decision

`scripts/replay-autogenesis-authoritative-admission.sh` performs authoritative
reproduction as follows:

1. require a clean source checkout and verify the retained historical readiness
   chain under the current checker;
2. create a disposable detached worktree at the current tool commit;
3. restore the selected fact's exact open row from the historical execution
   commit and commit that one-row pre-state with fixed local identity metadata;
4. freshly derive the frontier, execute the registered operation, and prepare
   the typed transaction, writing all intermediate artifacts outside the
   checkout so execution's clean-tree precondition remains meaningful;
5. inject a stop after durable intent and require exit 75 plus a byte-identical
   fact, then recover without replaying the producer;
6. freshly derive the post-frontier and authoritative readiness delta and replay
   the settled fact's registered checker; and
7. retain the complete fresh artifact bundle outside Git and emit a
   content-addressed report only when the fresh episode has the same
   semantic fact, operation, certified result, acceptance policy, admission
   event type, and readiness effect as the retained episode.

The report calls this **semantic reproduction**, not byte-for-byte reproduction.
Both the retained and fresh content identities are recorded.

## Consequences

- The caller's checkout and authoritative ledger are never mutated; the fresh
  evidence bundle is retained at an explicit caller-selected path outside Git.
- The replay proves acquisition with current tooling from an explicit historical
  open row, not merely verification of old receipts.
- A changed commit identity correctly produces new downstream object identities;
  stable semantics, rather than accidental byte equality, are the comparison.
- The leaf replay still receives no B-to-A or Autogenesis-1 credit.
- A future B-to-A replay must extend the same isolation boundary through A's
  event-triggered selection and admission.

## Rejected alternatives

### Temporarily rewrite the caller's ledger

Rejected. That weakens both safety and the executor's clean-checkout identity.

### Replay only the retained receipts

Rejected. This establishes continued verification, not independent acquisition.

### Require byte-identical fresh receipts

Rejected. Commit identity is a deliberate execution input, so a distinct clean
reproduction has distinct content-addressed outputs.
