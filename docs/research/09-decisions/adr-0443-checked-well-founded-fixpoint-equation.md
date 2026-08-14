# ADR-0443: Checked well-founded fixpoint equation

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 and Q2.

## Context

ADR-0442 adds a generic, zero-axiom `WellFounded.fix`, but a fixpoint over an
abstract well-foundedness proof is neutral: clients cannot use definitional
reduction alone to expose its recursive equation. Euclidean algorithms need a
checked unfolding theorem before their defining equations can support proofs.

Pinned Lean 4.30 proves the same boundary by accessibility induction. Its
constructor case is reflexive because accessibility evidence is proof
irrelevant, including the evidence passed to recursive calls. Axeyum lacks
`funext`, so the native proof must retain that pointwise definitional argument
rather than postulate function equality.

## Decision

Add the universe-polymorphic theorem

```text
WellFounded.fix_eq.{u,v} :
  forall {alpha : Sort u} {r : alpha -> alpha -> Prop}
         {C : alpha -> Sort v}
         (wf : WellFounded r)
         (F : forall x, (forall y, r y x -> C y) -> C x) (x : alpha),
    WellFounded.fix wf F x =
      F x (fun y _ => WellFounded.fix wf F y).
```

Prove it by `Acc.rec` on `wf x`. In the constructor minor, first reduce the
fixpoint at the explicit `Acc.intro` evidence, where the equation is
`Eq.refl`. Then use `Eq.rec` to transport to the evidence selected by `wf`;
the transport equality is itself reflexive modulo proof irrelevance. This
makes the neutral-major step explicit and requires no axiom, `funext`, or
source-level termination elaboration.

## Evidence

The cross-universe control uses a `Prop` carrier and a Nat-valued family,
applies `fix_eq`, and kernel-checks its inferred type against the fully expanded
generic equation. Reusing that proof for an equation whose right-hand side is
changed from one to zero is rejected with `DeclarationValueMismatch`. The
theorem joins the promised-name and deterministic-render checks, while the
complete logical environment remains under the existing zero-axiom audit and
pinned Lean 4.30 replay gate.

## Consequences

Abstract well-founded algorithms can now expose their defining equation inside
checked proofs. This does not yet establish any decreasing relation or number
theory result. The next dependency is a reusable proof that Nat strict order is
well-founded; only then should Euclidean division or `gcd` be defined through
the generic fixpoint.
