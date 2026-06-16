# ADR-0032: Standalone congruence-closure e-graph crate (`axeyum-egraph`)

Status: accepted
Date: 2026-06-16

## Context

The stack reasons about equality eagerly and per-theory: uninterpreted functions
by Ackermann reduction (ADR-0013, quadratic, no equality sharing) and arrays by
eager elimination (ADR-0010). Neither shares congruence reasoning, so every
eager→lazy theory upgrade on the parity roadmap — EUF on a real e-graph, lazy
arrays, datatypes, arithmetic equality propagation, and **all** quantifier work
(e-matching) — is blocked on a shared, incremental congruence structure. The
top-down reference review (`docs/plan/track-1-engine/P1.4-egraph.md`,
`docs/plan/references/z3-theories.md`) identified an incremental e-graph as the
single keystone to "do first": it is simultaneously the equality bus, the model
substrate, and the proof forest the later theories and the CDCL(T) loop
(P1.5/P1.6) all attach to.

The crate-split discipline (ADR-0001) says add a crate only once a boundary is
proven by use. Here the boundary is exercised on arrival: the e-graph is a
self-contained data structure with no dependency on the IR, queries, or backends
(it is generic over a caller-assigned `u32` function symbol), and it will be a
shared dependency of multiple solver theories rather than an internal of any one.
A standalone crate keeps it testable in isolation (brute-force congruence
oracle), reusable, and free of the solver crate's heavy dependency graph.

## Decision

**Introduce `axeyum-egraph`, a dependency-free crate owning the incremental
congruence-closure e-graph**, built in the task order of P1.4.

- The first slice (T1.4.1 + T1.4.2) is the structural core: hash-consed e-node
  creation (`EGraph::add(decl, args)`), a path-compressing union-find (`find`),
  and the deferred-merge cascade (`merge`) that re-canonicalizes parents through a
  signature table so transitive congruence closes. Handles are lifetime-free
  `Copy` ids (`ENodeId`) per the project rule; the crate forbids `unsafe`.
- Follow-up tasks extend the *same* structure rather than forking it: an
  explanation / proof forest (explain-to-LCA, T1.4.3), a backtrackable trail for
  push/pop and CDCL(T) (T1.4.4), an **independent congruence checker** that
  re-derives refl/symm/trans/cong with its own union-find (T1.4.5, the EUF analogue
  of `check_drat`/Farkas — extends "trusted small checking" to equality), and
  theory-variable lists per class for the equality bus (T1.4.6).
- The design ports the modern Z3 `euf_egraph` shape (signature table over argument
  roots; union-find separate from the proof forest; explain to the LCA with
  timestamped congruence justifications), adapted to Axeyum's `Copy`-id style.

## Consequences

- **Easier:** EUF without Ackermann blow-up, lazy arrays/datatypes, e-matching, and
  Nelson–Oppen theory combination can all attach to one congruence bus; the
  independent checker keeps equality reasoning inside the "untrusted search,
  trusted small checking" identity (ADR-0002).
- **Harder / deferred:** wiring the e-graph into the solver (an `axeyum-ir` term →
  e-node bridge, the CDCL(T) loop) is later work (P1.5); this crate stays
  IR-agnostic until then. The first slice does not yet produce explanations or
  support backtracking, so it is not yet usable as a theory solver — it is the
  substrate those tasks build on.
- **Revisit when:** the term bridge lands (decide whether `decl` ids come from the
  IR arena or a per-solver interner) and when the proof forest is added (the
  explanation format must line up with the eventual Alethe/Lean proof track,
  Track 3).
