# ADR-0020: Unbounded QF_LIA via Branch-and-Bound over the Simplex

Status: accepted
Date: 2026-06-13

## Context

The first integer-arithmetic fragment (ADR-0014) decides `QF_LIA` by **bounded**
bit-blasting: integers are encoded at a fixed width, so it is sound only for
`sat` (a found model is replayed) and must report `unknown` for `unsat` and for
out-of-range constants — a genuine model might exist outside the chosen width.
That leaves a coverage gap on the road to a Z3/cvc5-class solver
([solving-strategies note](../03-architecture/solving-strategies-and-memory-model.md),
gap 1): real, *unbounded* integer reasoning, sound for both `sat` and `unsat`.

The exact-rational simplex already in the tree for `QF_LRA` (ADR-0015) decides
the *real relaxation* of an integer problem. Branch-and-bound over it closes the
integrality gap with no new numeric core.

## Decision

**Add `check_with_lia_simplex`: decide conjunctive `QF_LIA` by branch-and-bound
over the exact-rational simplex, sound for both `sat` and `unsat`.**

- Collect the conjunctive linear-integer constraints (a dedicated `IntCollector`
  mirroring the LRA collector for the integer operator set; the LRA collector is
  left untouched).
- Solve the relaxation with the existing `simplex_feasible`. If it is infeasible,
  the integer problem is `unsat`. If the model is all-integer, it is a genuine
  integer solution. Otherwise pick the first fractional integer variable `x` with
  value `v` and branch `x ≤ ⌊v⌋` ∨ `x ≥ ⌊v⌋+1`, recursing.
- `sat` returns a `Value::Int` model **replayed** through the ground evaluator
  (the trust anchor). `unsat` is sound by exhaustive integer branching: the two
  branches cover all integers, so a fully-closed tree (every leaf's relaxation
  infeasible) means no integer solution exists.
- A node budget (`MAX_LIA_BNB_NODES`) bounds the search; exhaustion yields
  `unknown`, never a wrong verdict.

This is exposed as a standalone decision procedure for the conjunctive fragment;
wiring it into the auto-dispatcher (to give sound `unsat` where bounded
bit-blasting currently says `unknown`) and a `DPLL(T)` layer for Boolean-
structured `QF_LIA` are follow-ups.

## Evidence

- Reuses the ADR-0015 simplex and `Constraint`/`LinExpr` types verbatim; only the
  branch loop and the integer collector are new.
- Tests (oracle-free): `2x == 1` and `0 < x < 1` are proved **`unsat`** (which
  bounded bit-blasting cannot); a fractional relaxation (`1 ≤ 2x ≤ 3`) is
  branched to `x = 1`; large magnitudes (`x = 1_000_000`) are handled; linear
  systems return replayed models.
- Branch-and-bound is the standard, well-understood MILP-feasibility method;
  exhaustive integer branching is the textbook soundness argument for `unsat`.

## Alternatives

- **Keep only bounded bit-blasting.** Rejected: cannot prove `unsat`, and is
  bounded — both are coverage gaps for destination 2.
- **Omega test / cutting planes (e.g. Gomory).** Deferred: stronger termination
  and tighter cuts, but more machinery; branch-and-bound over the existing
  simplex is the smallest sound step and a clean base to add cuts to later.
- **Tangle integer support into the LRA collector.** Rejected for now: the LRA
  collector feeds the delicate Farkas path; a separate `IntCollector` avoids any
  risk to `QF_LRA` soundness.
- **Term-level Int→Real translation driving `check_with_lra`.** Rejected: more
  term plumbing and a parallel symbol space, versus branching directly on the
  simplex constraints.

## Consequences

- **Easier:** sound, unbounded `QF_LIA` (both verdicts); a base for `QF_LIA`
  `unsat` evidence and for a future `DPLL(T)` integer layer and cutting planes.
- **Harder / to watch:** branch-and-bound need not terminate on unbounded
  feasible regions with no integer point; the node budget makes that `unknown`
  (sound) but means completeness is budget-bounded until cuts/bounds are added.
  Only the conjunctive fragment is handled; disjunction/disequality stay
  `unsupported` pending a `DPLL(T)` layer.
- **Revisited when:** the dispatcher integration lands (choosing simplex-LIA for
  conjunctive integer queries over bounded bit-blasting), and when cutting planes
  or explicit bound derivation are added to strengthen termination and to produce
  a checkable `unsat` certificate (the LIA analogue of the Farkas/DRAT artifacts).
