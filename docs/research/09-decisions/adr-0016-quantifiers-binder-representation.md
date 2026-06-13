# ADR-0016: Quantifiers — Binder Representation and Finite-Domain Semantics

Status: accepted
Date: 2026-06-13

## Context

The quantifier-free layer is complete and unified behind one dispatcher. The
north star — "a complete framework for general reasoning, logic, and proving" —
requires **quantifiers**: the step from deciding quantifier-free formulas to
reasoning with `forall`/`exists`. This is the rung that turns the stack from an
SMT solver into a general reasoning engine.

Quantifiers force a long-standing open question (research-questions.md): **what
binder representation** should the IR adopt — de Bruijn indices, locally
nameless, or named with alpha-canonicalization — and which arena/interning
decisions it constrains. They also force a semantics question: the ground
evaluator is the trust anchor (every `sat` is replayed through it), so it must be
able to *evaluate* a closed quantified formula.

## Decision

Add quantifiers staged like every prior theory: a decision record, then an IR +
evaluator sub-increment, then solving.

- **Binder representation: named bound variables, reusing `SymbolId`.** A
  quantifier binds an existing declared symbol: the operators
  `Op::Forall(SymbolId)` and `Op::Exists(SymbolId)` take the body as their single
  argument, and the bound variable appears inside the body as an ordinary
  `Symbol(var)` node. The result sort is `Bool`. Rationale: this reuses the
  existing symbol/`Assignment` machinery, so the **ground evaluator works
  immediately** by binding the symbol while it ranges over the domain — no new
  `BoundVar` node, no de Bruijn index shifting, no capture-avoiding substitution
  needed for the evaluator. Modeling the binder as an `Op` (not a new
  `TermNode`) also keeps the cross-crate ripple to the operator-match sites,
  matching how the arithmetic operators were added.
- **Finite-domain evaluator semantics.** `forall x:S. body` evaluates by
  enumerating every value of `S` (`Bool` → `{false,true}`, `BitVec(w)` → all
  `2^w` values up to a width cap), binding `x` to each, evaluating `body`, and
  conjoining (`exists` disjoins). Infinite or non-enumerable domains (`Int`,
  `Real`, arrays) and over-wide bit-vectors are an evaluator error, not a wrong
  answer. This gives an exact, checkable semantics for finite-domain quantified
  formulas — enough to anchor trust for the bit-vector/Boolean fragment.
- **Solving is deferred.** The backends reject quantified (non-quantifier-free)
  formulas as `Unsupported`; quantifier *solving* (E-matching / instantiation
  layered on the DPLL(T) core, or finite-domain expansion) is the next
  sub-increment. The IR + evaluator land first, exactly as for arrays, EUF, and
  arithmetic.

## Evidence

- Named binders make the evaluator a one-line extension of the existing
  symbol-binding path; the alternatives each require new machinery before any
  quantified formula can be evaluated.
- Finite-domain enumeration is the standard executable semantics for quantifiers
  over finite sorts and is exactly checkable (no approximation), preserving the
  trust identity for the fragment it covers.

## Alternatives

- **De Bruijn indices.** Best for *structural* alpha-equivalence (alpha-equal
  terms intern identically) and capture-free substitution, which matters for
  efficient instantiation. Rejected *for now* because it needs a new `BoundVar`
  node and index-shifting substitution before the evaluator can run; revisit when
  instantiation is built (see Consequences).
- **Locally nameless.** Combines de Bruijn (bound) with names (free); same
  up-front substitution cost as de Bruijn for this slice.
- **A new `TermNode::Quantifier` variant.** Cleaner conceptually, but a far
  larger cross-crate match ripple than an `Op`; the `Op` encoding is sufficient
  and keeps the body as a normal application argument that generic passes already
  traverse.

## Implementation Progress

- 2026-06-13: sub-increment 1 (IR + evaluator) shipped — `Op::Forall(SymbolId)`
  and `Op::Exists(SymbolId)` over a `Bool` body, `TermArena::forall`/`exists`
  builders, and a ground evaluator that enumerates the bound variable's finite
  domain (`Bool`, `BitVec(w)` up to `2^16`), short-circuiting; infinite/
  non-enumerable domains are an `UnsupportedQuantifierDomain` error. Tested:
  Boolean tautology/contradiction quantifiers, bit-vector `forall`/`exists`
  ranging over all values, nested `forall x. exists y. x = y`, and a real-domain
  `forall` correctly erroring. The `Op` encoding kept the cross-crate ripple to
  the operator-match sites; backends reject quantified formulas as
  `Unsupported`, and the SMT-LIB writer renders binder form.
- 2026-06-13: quantifier **solving by finite-domain expansion** shipped —
  `axeyum_rewrite::expand_quantifiers` rewrites each finite-domain quantifier to
  the conjunction (`forall`) / disjunction (`exists`) of its instances
  (substituting each domain value for the bound symbol; `BitVec` capped at
  `2^10`), and `axeyum_solver::check_with_quantifiers` expands then dispatches the
  quantifier-free result via `check_auto`, replaying the *original* quantified
  formula through the enumerating evaluator (the trust anchor). Complete for
  finite domains. End-to-end tests: a universal tautology → `sat`, a false
  universal → `unsat`, an existential constraining a free variable, a nested
  `forall x. exists y. x = y` → `sat`, and an infinite domain → `Unsupported`.
  Remaining: E-matching for infinite-domain quantifiers and the SMT-LIB parser
  side.
- 2026-06-13: SMT-LIB quantifier parsing shipped — the parser accepts
  `(forall ((x T) …) body)` / `(exists …)` by declaring a **uniquely-named fresh
  symbol** per bound variable (so it cannot capture a free symbol or another
  binder), scoping the names to the body via the existing `let`-style scope
  stack, and wrapping the body in nested `forall`/`exists`. With the existing
  writer this gives a parse → write → parse round-trip; a nested-binding test
  confirms two separate `x` binders do not collide. The binder rollout now
  matches the other theories (IR, evaluator, expansion solving, SMT-LIB I/O);
  only E-matching for infinite-domain quantifiers remains.
- 2026-06-13: **enumerative ground instantiation** added for infinite-domain
  refutation — `axeyum_rewrite::instantiate_universals` replaces each top-level
  `forall x. body` with the conjunction of `body[x := t]` over the formula's
  ground terms of `x`'s sort, and `axeyum_solver::prove_unsat_by_instantiation`
  solves the result with `check_auto`. Because instantiation only weakens, an
  `unsat` transfers soundly (a satisfiable instantiation is `unknown`; a
  quantifier-free query is decided exactly). This refutes `Real` universals that
  finite-domain expansion cannot enumerate; integer universals degrade to
  `unknown` because bounded integer bit-blasting reports unsat-in-range as
  `unknown` (ADR-0014). True E-matching with trigger patterns is the scalable
  successor.
- 2026-06-13: **trigger-based E-matching** added —
  `axeyum_rewrite::instantiate_with_triggers` and
  `axeyum_solver::prove_unsat_by_ematching`. For each top-level `forall x. body`
  it picks the body's `apply`/`select` subterms mentioning `x` as triggers and
  matches them against the assertions' ground subterms, binding `x` to the
  matched terms. Crucially this binds `x` to **compound** ground terms (`f(a)`,
  `select(m,i)`) — which the leaves-only enumeration of `instantiate_universals`
  never tries — so it refutes goals enumeration cannot reach. Bindings are
  unioned with the enumerative leaves, so it is strictly at least as capable, and
  soundness is unchanged (every instance follows from the universal; trigger
  choice only affects *which* sound instances are produced). `solve`'s quantifier
  fallback now uses it. A test shows `forall x:BV16. g(x)=0` ∧ `g(f(a))≠0`:
  leaves-only enumeration stays `unknown`, while E-matching binds `x:=f(a)` and
  refutes exactly. Remaining: multi-trigger/multi-variable matching and an
  E-graph-backed match index for scale.

## Consequences

- The IR can express quantified formulas and the evaluator decides closed
  finite-domain ones, so a future quantifier solver's `sat` models stay
  checkable.
- **Interning is not yet alpha-canonical:** two alpha-equivalent quantified
  terms over differently-named bound symbols do not intern equal. That is a
  solving-time efficiency concern, not a soundness one, and is deferred.
- When instantiation / E-matching is built, capture-avoiding substitution over
  named binders is the known pain point; a follow-up ADR may migrate the binder
  representation to de Bruijn at that point. The `Op`-based encoding localizes
  that future change.
- A bound variable also appears in the arena's free-symbol list; this is benign
  while quantified formulas are rejected by solvers, but the eventual solver must
  treat bound occurrences distinctly.
