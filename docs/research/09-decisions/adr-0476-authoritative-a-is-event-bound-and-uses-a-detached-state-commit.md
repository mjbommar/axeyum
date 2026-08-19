# ADR-0476: Authoritative A is event-bound and uses a detached state commit

Status: accepted
Date: 2026-08-18
Index-summary: Require Nat.mul_one dispatch to verify the complete B admission trigger, reconstruct an episode-local B proof, and bind a deterministic post-B Git state without mutating the branch

## Context

The authoritative B experiment made `F:nat-mul-one` newly ready, but that is
not enough to authorize its proof. A caller could otherwise present an unrelated
ready frontier, or the checker could silently use the retained `Nat.zero_add`
whose source proof predates the episode.

A second conflict appears at the Git boundary. B admission intentionally changes
the ledger before A runs, while authoritative execution previously required a
clean checkout and bound `HEAD`. Asking a human to commit B would insert an
unaccounted intervention. Binding the old source commit would make A's later
readiness replay reconstruct the wrong pre-A ledger.

## Decision

Register the exact
`authoritative-kernel-nat-mul-one-episode-apply-v1` operation. Its dispatch
requires one trigger bundle containing B's before frontier, execution,
transaction, durable admission event, and readiness delta. The executor fully
recomputes the readiness delta and verifies every content
digests and identity chain against:

- the current operation registry;
- the admitted B fact and its typed evidence row;
- the current frontier selected for A;
- exactly one authoritative B write and zero fixture writes; and
- `newly_ready: [F:nat-mul-one]` caused by B's durable event.

The untrusted proposer receives one proof-body-free entry: an episode-named B
candidate. The fresh kernel reconstructs that candidate with the registered B
induction plans and then applies it to A. Evidence must report plan rank 1 of 1,
premise rank 2 of 2, the episode candidate as the applied dependency, an empty
axiom footprint, and no dependency on retained `Nat.zero_add` or `Nat.mul_one`.

For state identity, the executor creates a deterministic unreferenced Git commit
using a temporary index. Its parent is B's clean source commit and its sole tree
change is the verified admitted B row. The real branch, worktree, and index are
unchanged. A's receipt binds this commit, so post-A readiness can reconstruct
the exact pre-A ledger. A retained experiment must archive the commit in a Git
bundle before it can receive replay credit.

Ambient checker executable overrides remain forbidden.

## Consequences

- A cannot be dispatched from dependency status alone; it requires the exact
  event that changed its eligibility.
- The A proof depends on an episode-local B declaration, not a retained answer.
- Git source identity and intermediate ledger-state identity no longer require
  a human commit or a dirty-state exception.
- The operation is still exact to this chain. A generic theorem-application
  route requires a later exercised contract.
- Implementation and unit evidence do not earn Autogenesis-1 credit. A clean
  two-write replay and retained state bundle remain required.
