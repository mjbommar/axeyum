# ADR-0471: Authoritative readiness from a durable event and reconstructed pre-state

Status: accepted
Date: 2026-08-18
Index-summary: Reconstruct pre-admission ledger state from the execution commit, bind exact before and after frontiers to the durable event, and permit an honest empty unlock set

## Context

The counterfactual Autogenesis fixture already derived one B-to-A readiness
change from a durable fixture event. The first real authoritative admission is
different: its selected fact is an isolated import-backlog leaf with no
descendants. A scheduler must still recompute and record the frontier after the
event, but it must not invent a newly ready fact merely to make the episode look
like compounding.

The prepared transaction stores the complete after-fact and the digest of the
before-fact, not a second copy of the full ledger. The exact operation execution
already binds the clean Git commit, before-fact digest, and operation-registry
digest. That is enough to reconstruct and independently check the complete
pre-state without enlarging the durable event or trusting a saved frontier on
its own.

This implements ADR-0468's rule that readiness consumes the durable admission
event rather than filesystem observation.

## Decision

**For an authoritative single-fact admission, readiness reconstruction loads
the complete fact ledger and operation registry from the exact Git commit bound
by the execution receipt, requires that the admitted fact is the only ledger
row changed in the post-state, rebuilds both frontiers under that same registry,
and binds them to the durable admission event in one content-addressed delta.**

The checker requires:

1. valid transaction, execution, and durable-event content identities;
2. exact agreement among their fact, execution, transaction, before, and after
   digests;
3. the reconstructed registry to equal the execution registry digest;
4. the live authoritative fact to equal the transaction's complete after-fact;
5. the reconstructed before-fact to equal both the execution and transaction
   before digests;
6. identical pre/post ledger populations and the admitted fact as their only
   changed row;
7. the saved before and after frontiers to equal fresh derivations over those
   two ledger states;
8. the before frontier to have selected the admitted fact; and
9. the only fact leaving the ready set to be the admitted fact itself.

`newly_ready` is the exact set difference between the derived after and before
ready sets. It may be empty. An empty set is a successful and informative leaf
transition, not an Autogenesis-1 operational unlock.

## Evidence

- The first production admission intentionally stopped after persisting its
  intent while the fact remained byte-identical, then recovered to durable
  event `234aa5bcd410270f9e65f866c605805ea1a1cd66150d4aea805102803adbe4d8`.
- Before frontier
  `f822e6c6c1b6cddeb1482628ea1192bff8372b503aa0d61919f120e08fa096a8`
  selected the fact; after frontier
  `cecee8c08d98eb0a6bcbff0b4c35fd18bd274459fa2807e11e56f98657aed7d6`
  removes it and selects nothing.
- Authoritative readiness delta
  `8aec041fb71702b16e42a1b611cf61276acf749be575e2599080b913e89b30ce`
  records one authoritative write, zero fixture writes, the admitted fact as
  the sole no-longer-ready item, and `newly_ready: []`.
- Mutation controls reject malformed ready sets, any unrelated fact changing in
  the ledger, and any unrelated fact disappearing from readiness; a separate
  positive control derives a real B-to-A unlock when A enters the after-ready
  set.

## Alternatives

### Trust the saved before and after frontier files

Rejected. Their internal digests prove integrity, not that they describe the
transaction's actual pre/post ledger states. Both are freshly rebuilt.

### Store the complete before-fact in the durable event

Rejected. The execution already binds a clean immutable Git source and exact
fact digest. Duplicating the full row enlarges the event and creates another
copy whose agreement must be governed.

### Require at least one newly ready fact

Rejected. That would force infrastructure validation to masquerade as
compounding. The leaf transition is useful precisely because it proves the
system can report zero without manufacturing progress.

### Recompute on file change before the admission event exists

Rejected. A visible after-fact with no durable event is an interrupted
transaction state. Scheduling from it would violate ADR-0468 and make crash
timing part of semantics.

## Consequences

- Authoritative readiness and fixture readiness share the same output kind but
  declare distinct modes and write counts.
- The first real closure validates event-triggered recomputation while receiving
  no B-to-A or Autogenesis-1 credit.
- Reproduction requires the execution commit to remain available in Git; this
  is already part of the clean execution identity and publication protocol.
- The next chain episode must show a non-empty exact `newly_ready` set and then
  execute A from that event-derived frontier.
