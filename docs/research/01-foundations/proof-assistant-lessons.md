# Proof Assistant Lessons

Status: draft
Last updated: 2026-06-10

## Purpose

Extract useful architecture lessons from proof assistants, especially Lean,
without turning Axeyum into a proof assistant.

## Scope

In scope:

- Trusted kernels, checkable evidence, tactics, elaboration, libraries.

Out of scope:

- Implementing dependent type theory.
- Depending on Lean in the hot path.

## Core Claims

- Lean's most relevant lesson is architectural: large automation can be untrusted
  if a smaller checker validates proof objects or executable evidence.
- Axeyum should distinguish fast search from trusted validation.
- Tactics are a useful mental model for programmable symbolic search strategies.
- Libraries of semantics and rewrites will matter as much as the core engine.

## Lean-Inspired Pattern

```text
untrusted automation
  -> candidate proof, model, rewrite, or witness
  -> small checker
  -> accepted result
```

Axeyum equivalents:

- Satisfying model -> concrete replay or formula evaluation.
- Unsat claim -> proof certificate, checked proof, or independent solver cross-check.
- Rewrite rule -> verified local theorem, exhaustive finite test, or solver proof.
- Analysis tactic -> structured evidence artifact.

## Design Implications

- Preserve an evidence API from the start.
- Keep validators smaller and less configurable than optimizers.
- Allow tactic-like clients to inspect and guide solver/search state.
- Build libraries: rewrite rules, encodings, instruction semantics, protocol models,
  and benchmark corpora.

## Risks

- Proof objects for modern SAT/SMT can be large.
- Over-indexing on proof checking too early can slow down discovery of the useful API.

## Open Questions

- [ ] Should the first checker validate only SAT models and CNF encodings?
- [ ] Should rewrite rules carry explicit proof obligations?
- [ ] Could Lean be used later to specify parts of the IR or rewrite system?

## Source Pointers

- Lean: https://lean-lang.org/
- Lean Mathlib: https://github.com/leanprover-community/mathlib4
- CreuSAT verified SAT solver: https://github.com/sarsko/CreuSAT

