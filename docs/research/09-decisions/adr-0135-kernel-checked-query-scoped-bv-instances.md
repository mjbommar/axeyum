# ADR-0135: Kernel-checked query-scoped BV instances

Status: accepted
Date: 2026-07-13

## Context

ADR-0134 checks a query-scoped set of positive-universal Bool/BV source
instances and a residual QF_BV refutation, but its Lean route was still open.
A standalone proof of the ground residual is insufficient: reconstruction must
show that every residual assumption follows from an untouched source assertion.

cvc5 records instantiations as applications of quantified formulas, and Z3's
model-based quantifier paths likewise turn complete bindings into source
instances before ground solving. The Lean theorem must preserve that boundary:
search may select bindings, but only typed universal elimination may introduce
an instance into the proof.

## Decision

**Reconstruct the admitted ADR-0134 source shape as genuine typed universal
theorems, derive every ground assumption from those theorems, and then check a
compact propositional refutation.**

The route:

- scans only top-level conjunction trees whose quantified leaves are positive
  Bool/BV universals with quantifier-free bodies accepted by ADR-0134;
- represents Bool with the Lean Bool inductive and each admitted BV width with
  a typed bit-field inductive, rejecting widths above 64;
- translates each untouched quantifier-free source body through the existing
  structurally hashed AIG lowering, preserving one shared kernel DAG;
- introduces only axioms for the untouched ordered source assertions;
- projects ground conjunction leaves and applies each universal proof to the
  certificate's exact typed constructor witnesses;
- checks every resulting residual assumption against an independently lowered
  source body before it enters the SAT tail;
- emits shallow named AIG gates and reconstructs their Alethe clause proof to
  `False`; and
- renders the checked term as a self-contained Lean module with the required
  Bool/BV inductives.

The resolution normalizer now distinguishes definitional negation movement from
classical double-negation cancellation. Any `not (not p)` to `p` conversion is
proved explicitly from the route's declared excluded-middle axiom and
kernel-checked; a clause proof is never reused at a merely classically
equivalent type.

The kernel caches successful inference results only for expressions with no
free variables and no loose bound variables. Closed terms are independent of
the local context, and this cache prevents repeated traversal of hash-consed
source/proof DAGs. Failed or open inference is never cached.

## Evidence

The implementation was checked against:

- `references/cvc5/src/theory/quantifiers/instantiate.cpp`;
- `references/cvc5/src/theory/quantifiers/cegqi/ceg_instantiator.cpp`;
- `references/z3/src/sat/smt/q_mbi.cpp`;
- `references/z3/src/smt/smt_model_checker.cpp`; and
- Lean's dependent `Or.rec`, `False.rec`, Bool recursor, and inductive checking
  exercised by the existing external-Lean harness.

Focused tests require two distinct instances of one BV universal, derive both
from the original theorem, reject a tampered witness sort, exercise the public
fragment router, and compare 32 generated SAT/UNSAT cases with direct Z3. The
representative external-Lean suite includes the two-instance theorem and rejects
`sorryAx` when a Lean binary is available. This host has no `lean` or `elan`
binary, so local validation completed the mandatory in-tree kernel gate and
registered, but did not execute, that external process. Kernel regression
coverage verifies that only successful closed inference enters the cache.

The public `psyco-107-bv` certificate remains replay-checked by ADR-0134, but
its duplicate full Lean reconstruction is deliberately an ignored stress test:
two debug measurements exceeded three minutes at roughly 2.3 GiB RSS. This ADR
does not raise the public quantified-BV Lean count from 8/18 until that
corpus-scale proof completes within an appropriate gate.

## Alternatives

- **Axiomize each ground instance.** Rejected: it loses the source theorem and
  trusts instance selection.
- **Prove only the carried residual CNF.** Rejected: the CNF assumptions would
  not be connected to the original query.
- **Expand substituted IR terms independently.** Rejected: simplification can
  change circuit topology and duplicate large proof trees.
- **Treat double negation as definitional equality.** Rejected: it is not a
  kernel reduction and previously produced an ill-typed resolution term.
- **Run the public stress case in every debug test suite.** Rejected: the
  measured cost is not suitable for the default workspace gate.

## Consequences

ADR-0134 now has a genuine source-instantiation Lean route for the admitted
bounded shape, with fail-closed source checking and no instance axioms. The
next proof-engineering task is compact sharing or a checked serialized proof
format for the corpus-scale resolution tail, followed by ranking the remaining
quantified-BV UNSAT certificate families for the same source-bound treatment.
General negative quantifier contexts, existentials, free BVs in quantified
assertions, functions, arrays, mixed arithmetic, and nested QSAT remain outside
this route.
