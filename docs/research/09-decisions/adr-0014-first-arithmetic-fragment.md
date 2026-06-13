# ADR-0014: First Arithmetic Fragment — Linear Integer Arithmetic, Bit-Blasted

Status: accepted
Date: 2026-06-13

## Context

The finite-domain core (full scalar `QF_BV`, arrays, EUF, and their composition)
is complete end to end. The next rung of the north-star ladder is **arithmetic**:
reasoning about integers and reals, not just fixed-width bit-vectors. This is the
gateway to the rest of the framework — theory combination presupposes at least
one arithmetic theory, and most real verification/analysis obligations mix
arithmetic with the theories already supported.

The foundational DAG gates any new logic fragment on a decision record. Two axes
to choose: which arithmetic (integers `LIA` vs reals `LRA`), and which decision
procedure (bit-blasting a bounded encoding vs a native arithmetic procedure like
simplex / branch-and-bound).

Trust identity constraints (untrusted search, trusted checking) apply unchanged:
every `sat` must carry a model checkable by the ground evaluator; `unsat` must be
checkable or honestly downgraded to `unknown`.

## Decision

The first arithmetic fragment is **quantifier-free linear integer arithmetic
(`QF_LIA`)**, and the first decision procedure is **bounded bit-blasting onto the
existing `QF_BV` pipeline**.

- **Integers are a first-class IR sort (`Int`).** The IR gains an `Int` sort,
  integer constants, and the linear operator set (`+`, `-`, unary `-`, `*`, and
  the order comparisons `<`, `<=`, `>`, `>=`); equality and `ite` are already
  polymorphic. The ground evaluator interprets `Int` as mathematical integers
  (exact within the `i128` reference range; out-of-range intermediate values are
  a usage error, consistent with the bounded-first decision below). This is
  sub-increment 1.
- **Decision procedure: bounded bit-blasting first.** A later sub-increment
  lowers `Int` constraints to `QF_BV` at a chosen, explicit bit-width, reusing
  the entire trusted core (BV → AIG → CNF → SAT, model replay). This is the
  cheapest first procedure and inherits the existing trust anchors verbatim.
- **Soundness contract of the bounded procedure.** A model found in the bounded
  range is a *real* integer model, so `sat` is sound and replayable. Bounded
  search is **not** complete for `unsat` (an unbounded model could exist outside
  the range), so "no model in range" is reported as **`unknown`** (with the range
  as the reason), never as `unsat`. This keeps `unknown` first-class and honest.
- **`*` is kept in the IR but the fragment is linear.** The evaluator handles
  general `Int` multiplication (it is total over integers); the *linear* fragment
  restriction (at most one non-constant factor per product) is a property the
  bit-blaster / future procedures enforce or exploit, not an IR-level ban — the
  IR must not foreclose nonlinear extensions.

## Evidence

- Bit-blasting integers is the standard cheapest route to `QF_LIA` for bounded
  problems and is exactly how the existing scalar `QF_BV` path already works, so
  it reuses model replay and the proof-producing UNSAT core with no new trust
  surface.
- The bounded/`unknown` contract mirrors the resource-budget `unknown`
  classification already in `SolverConfig`, so it fits the established result
  model.
- Sub-increment 1 in isolation (sort + evaluator) is validated the same way the
  array and EUF IR increments were: exhaustive small-range evaluation of the
  operator semantics.

## Alternatives

- **`QF_LRA` (reals) first.** Reals need a simplex core to be useful and do not
  bit-blast onto the BV pipeline, so they would require a brand-new trusted
  procedure before delivering any value. Integers reuse the existing core;
  reals follow once a native arithmetic procedure exists.
- **Native procedure (simplex / branch-and-bound) first.** The scalable and
  eventually necessary target — required for unbounded completeness and for
  reals — but large, and it cannot reuse the bit-blast trust anchors. Deferred
  to a later ADR; bounded bit-blasting delivers checked `sat` now.
- **No `Int` sort (model integers as wide bit-vectors directly).** Rejected: it
  paints the framework into the finite-domain corner the north star warns
  against, and conflates wrap-around BV semantics with integer semantics.

## Implementation Progress

- 2026-06-13: sub-increment 1 (IR + evaluator) shipped — the `Int` sort,
  `IntConst`, the linear operator set, `Value::Int`, and evaluator support,
  verified exhaustively over a small integer range.
- 2026-06-13: the bounded bit-blasting decision procedure shipped —
  `axeyum_rewrite::blast_integers` maps integers to signed width-`B`
  bit-vectors (`int_*` → `bv*`/`bvs*`), and
  `axeyum_solver::check_with_int_blasting` solves the blasted query with
  `SatBvBackend`, **reads the model back as exact integers, and replays the
  original integer assertions**. The soundness contract is enforced: bit-vector
  `sat` + exact replay → `sat`; replay failure (width-`B` wraparound) → `unknown`;
  bit-vector `unsat` → `unknown` (not `unsat`); out-of-range constant → `unknown`.
  End-to-end tests cover satisfiable linear equations (incl. negative
  solutions), contradictory bounds → `unknown`, and out-of-range → `unknown`.
- 2026-06-13: `QF_LIA` scenarios and SMT-LIB I/O shipped — a `Family::Integer`
  in `axeyum-scenarios` (`integer_system` boxed/ordered/sum-pinned constraint
  systems, `integer_equation` boxed linear equations) with `integer_catalog`,
  each satisfiable by construction and decided through `check_with_int_blasting`
  in a solver differential test; and the SMT-LIB parser/writer now handle the
  `Int` sort, integer literals, `(- n)` negation, `+`/`-`/`*`, and chainable
  `<`/`<=`/`>`/`>=`, with a `QF_LIA` parse → write → parse round-trip. The
  `QF_LIA` rollout now matches the array/EUF tracks end to end.

## Consequences

- The IR expresses `QF_LIA`; the evaluator is its semantic reference, so a future
  bounded bit-blaster's `sat` models are checkable end to end.
- Backends that do not yet handle `Int` (the pure-Rust BV bit-blaster, the Z3
  oracle) reject `Int` with a clear `Unsupported`/error until the lowering
  sub-increment lands — exactly as arrays and EUF were staged.
- A second arithmetic ADR will be needed before adding a native procedure
  (simplex/branch-and-bound), reals (`QF_LRA`), or integer division/modulo
  totality semantics.
- The `unknown`-on-out-of-range contract must be surfaced wherever the bounded
  procedure is exposed, so callers never mistake bounded `unknown` for `unsat`.
