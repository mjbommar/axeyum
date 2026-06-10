# ADR-0001: Vertical Slice Before Horizontal Layers

Status: accepted
Date: 2026-06-10

## Context

The roadmap's phases are layer-by-layer (IR, then backend, then rewriting,
then circuits). Building each layer to completion before the next risks
discovering API mistakes only at integration time, and delays the first
end-to-end result for months. This closes the crate-layout and
"what ships first" questions in the README and roadmap by sequencing, not by
final answer.

## Decision

Build a minimal end-to-end vertical slice (milestone M0) before broadening any
single layer:

- IR subset: `Bool`, `BV(n)` constants/symbols, `not/and/or/xor`, `add`,
  `eq/ult`, `extract/concat`, `ite`.
- One backend: Z3 behind a feature flag, through the Axeyum-owned solver trait.
- Ground evaluator, and model check-by-evaluation on every `sat` result.
- Start as two crates (`axeyum-ir`, `axeyum-solver` with the Z3 adapter as a
  feature); split further only when a boundary is proven by use.

M0 is done when: a doctest builds `x + 1 == 5` over `BV(8)`, gets `sat` from
Z3, lifts a model keyed by Axeyum symbols, and the evaluator confirms the
model satisfies the original term.

## Evidence

Reasoning from the research notes: the mission note warns that too-general
scope delays useful implementation; the crate-boundaries note flags premature
splitting as churn risk; the evidence note requires check-by-evaluation early.
A vertical slice satisfies all three simultaneously.

## Alternatives

- Full Phase-1 IR first (all operators, arrays question settled): rejected;
  operator breadth is mechanical once the slice proves the arena, sort
  checking, trait, and model-lifting shapes.
- Pure Rust path first (skip native backends): rejected; without an oracle
  there is no differential testing for anything that follows.

## Consequences

- Easier: every later phase lands into a working pipeline with an oracle and a
  checker already in place.
- Harder: some M0 APIs will be rewritten as layers broaden; accepted cost.
- Revisit: crate split decisions after Phase 3, when rewrite/query boundaries
  are exercised by real code.
