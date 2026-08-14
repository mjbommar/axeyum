# ADR-0442: Generic checked well-founded fixpoint

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 and Q2.

## Context

ADR-0441 exposes native `Acc`, its generated recursor, and `WellFounded`, but
algorithm definitions still have to assemble the dependent `Acc.rec` motive
and constructor minor themselves. That is precisely the proof-term plumbing
which made the Rado Nat development expensive and which should be centralized
before building `gcd` or any other decreasing algorithm.

Pinned Lean 4.30 defines `WellFounded.fix` through an accessibility-recursive
helper and separately proves its unfolding equation. The native prelude can use
the same semantic boundary without importing source elaboration, tactics, or
termination automation.

## Decision

Add the zero-axiom, universe-polymorphic definition

```text
WellFounded.fix.{u,v} :
  forall {alpha : Sort u} {r : alpha -> alpha -> Prop}
         {C : alpha -> Sort v},
    WellFounded r ->
    (forall x, (forall y, r y x -> C y) -> C x) ->
    forall x, C x.
```

Implement it as one generated `Acc.rec` application with motive
`fun x _ => C x` and minor `fun x _ ih => F x ih`. Keep carrier, relation,
and result family generic; a Nat-only or division-only wrapper would not serve
the broader algorithm layer. Generated recursors order the motive universe
before the inductive family's universe, so the internal instantiation is
`Acc.rec.{v,u}` even though `WellFounded.fix` declares parameters `{u,v}`.

This is core term construction, not source-level `termination_by` elaboration.
The latter remains outside the native prelude boundary.

## Evidence

A checked computation uses a carrier in `Prop` (`u = 0`) and a constant Nat
result family in `Type` (`v = 1`), deliberately distinguishing the universes.
For the empty relation, a concrete well-foundedness proof and a step returning
one make `WellFounded.fix` delta/iota-reduce to one; the zero control remains
definitionally unequal. The declaration joins the deterministic render check
and zero-axiom audit. Pinned Lean 4.30 independently admits the complete
export and rejects its existing tampered control.

## Consequences

Hand-built and reconstructed developments can now define genuinely decreasing
functions without expanding `Acc.rec` at each call site. Abstract clients still
need a checked `WellFounded.fix_eq` theorem to unfold a fixpoint when the
well-foundedness proof is neutral; that theorem is the next dependency before
the first Nat Euclidean algorithm or `gcd` definition.
