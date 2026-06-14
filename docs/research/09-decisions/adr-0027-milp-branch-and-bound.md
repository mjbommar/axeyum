# ADR-0027: Mixed Integer/Real Arithmetic by Branch-and-Bound

Status: accepted (implemented 2026-06-14)
Date: 2026-06-14

## Context

`QF_LIRA` couples the integer and real theories through the `to_real`/`to_int`
coercions. The exact rewrites (`eliminate_to_real_const_compare`, `fold_to_real_sums`)
already dispatch the common "coerced integer vs. a constant" pattern completely.
What remained incomplete was a `to_real(x)` coupled to a **real variable** (e.g.
`to_real(x) = y ∧ 1000.3 < y < 1000.9`): the coercion relaxation (replace
`to_real(x)` with a fresh real, link it to `x` only over a small constant range,
ADR follow-up to the LIA work) cannot link an unbounded integer, so it returns
`unknown` on exactly the cases where integrality is what decides the query.

A complete decision for the linear mixed fragment is mixed-integer linear
programming (MILP) — the same branch-and-bound that ADR-0020 used for unbounded
`QF_LIA`, but branching only on the integer-constrained variables while the real
variables stay continuous.

## Decision

**Decide the conjunctive linear mixed integer/real fragment by branch-and-bound
over the existing Farkas-checked LRA engine.** The query (coercions intact) is
lowered to an all-real LP — every integer symbol becomes a fresh real symbol,
`to_real(i)` becomes that same symbol (so the coupling is *exact*, not relaxed),
and the integer linear operators map 1:1 to their real counterparts. The former
integer symbols are remembered as the integrality constraints. Then:

- Each node solves the LP with `check_with_lra` (Fourier–Motzkin with a
  self-checked Farkas certificate on `unsat`).
- `unsat` at a node is sound: the LP relaxation has *more* solutions than the
  mixed problem, so its infeasibility implies the node's.
- A `sat` LP model with a fractional integer column branches on that column
  (`x ≤ ⌊v⌋` ∨ `x ≥ ⌊v⌋+1`); the two half-spaces cover every integer, so the
  node is `unsat` iff both branches are, `sat` if either is.
- A `sat` leaf with all integer columns integral is **replayed against the
  original mixed query** through the ground evaluator (the evaluator computes the
  true `to_real`), so a spurious candidate becomes `unknown`, never a wrong `sat`.
- A node budget bounds the search; on exhaustion, or for anything outside the
  linear mixed fragment (nonlinear, `to_int`/`is_int`, bit-vectors, non-conjunctive
  structure the LRA engine rejects), the procedure returns `unknown` and
  `check_auto` falls back to the sound coercion relaxation.

This is tried in `check_auto` *before* the relaxation, so it strictly improves
completeness without weakening any existing result.

## Evidence

- ADR-0020 established the same branch-and-bound over the exact-rational simplex
  for `QF_LIA`; this reuses that shape with an integer-column-restricted branch
  rule, which is the textbook MILP relaxation.
- Soundness rests on two anchors already trusted in the codebase: the LRA
  engine's self-checked Farkas certificate (`unsat` per node) and ground-evaluator
  replay (`sat`). No new trusted component is introduced.
- Tests (`tests/coercions.rs`): `to_real(x) = y ∧ 1000.3 < y < 1000.9` is decided
  `unsat` (both `x ≤ 1000` and `x ≥ 1001` leaves Farkas-refuted), and
  `… < y < 1001.3` is decided `sat` (`x = 1001`) with the coupling replay-checked
  — both cases the bounded relaxation returns `unknown` on.

## Alternatives

- **Hand-written mixed simplex.** Rejected: it would re-implement (and re-trust)
  an LP core, with `unsat` resting on new unaudited code; reusing the
  Farkas-checked engine as the LP oracle keeps the trust base unchanged.
- **Raise the coercion-relaxation link bound.** Rejected: it only shifts the
  incompleteness boundary and blows up the encoding; it never handles an
  unbounded coerced integer.
- **Full Nelson-Oppen combination.** Deferred: heavier than needed for the linear
  fragment, and branch-and-bound already decides it completely (modulo budget).

## Consequences

- **Easier:** conjunctive `QF_LIRA` with integer/real coupling through `to_real`
  decides (sat and unsat) where it previously returned `unknown`.
- **Harder / bounded:** disjunctive mixed structure beyond what the conjunctive
  LRA engine accepts still falls back to the relaxation; the node budget caps the
  search (then `unknown`). Re-solving the LP from scratch per node is not
  incremental — acceptable at the current budget, a future optimization.
- **Unchanged:** the soundness contract (Farkas `unsat`, replayed `sat`),
  determinism, and the no-C-dependency / `unsafe`-free guarantees.
- **Revisited when:** a workload needs disjunctive mixed reasoning (then a
  DPLL(T) MILP loop) or incremental node solving.
