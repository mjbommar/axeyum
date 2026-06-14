# ADR-0024: Nonlinear Real Arithmetic via Linear Abstraction + Replay

Status: accepted (first slice implemented 2026-06-14)
Date: 2026-06-14

## Context

The stack decides linear real arithmetic (QF_LRA, ADR-0015) via an exact-rational
simplex in a lazy-SMT loop. Nonlinear real arithmetic (QF_NRA) — constraints with
products of two non-constant reals, `x·y` — is a Z3/cvc5 parity gap and shows up
in program reasoning (and, e.g., symbolic-scale GPU block formats: `element ·
2^scale` with a symbolic scale). Full NRA is decidable (CAD) but heavy; we want a
*sound* first step that reuses the LRA machinery rather than a from-scratch
decision procedure.

## Decision

**Decide NRA by linear abstraction + replay, the same sound relaxation pattern
already used for the lazy bit-vector and datatype paths
(`check_with_nra`).** Each genuinely nonlinear product `x·y` (a `RealMul` whose
operands are *both* non-constant; `c·y` stays linear) is replaced by a fresh,
*unconstrained* real variable; the residual is pure LRA and goes to the existing
`check_with_lra_dpll`.

Because the fresh variable is unconstrained, the abstraction only enlarges the
model space:

- **`unsat` of the abstraction ⇒ `unsat` of the original** (sound): if even the
  relaxation has no model, neither does the original. Crucially, the *same*
  product maps to the *same* variable, so e.g. `x·y = 5 ∧ x·y = 6` is proved
  `unsat` with no nonlinear reasoning.
- **`sat` of the abstraction is a candidate**, replayed against the original
  assertions with the ground evaluator (which computes the true products), and
  accepted only if it actually satisfies them; otherwise the result is `unknown`.

It is also strengthened with **sound multiplication lemmas** about each product
`r = a·b` — the sign rules (`(a≥0 ∧ b≥0) → r≥0`, etc.) and the zero rule
(`r = 0 ⟺ a = 0 ∨ b = 0`). These are valid facts, so they preserve the
relaxation (the original model with `r = a·b` satisfies them), but they let the
LRA loop decide *sign-based* nonlinear queries with no nonlinear reasoning — e.g.
`x·x < 0` is now `unsat` (x² ≥ 0), `x>0 ∧ y>0 ∧ x·y<0` is `unsat`, and
`x=0 ∧ x·y=5` is `unsat`.

So the procedure is **sound in both directions and incomplete**: it decides
queries resolvable from the linear part plus these sign/zero facts (and replays
candidate `sat` models against the true products), and returns `unknown` — never
a wrong answer — when a deeper nonlinear fact is needed (e.g. magnitude bounds).
It is routed automatically from the dispatcher's real path.

## Evidence

- The lazy bit-vector abstraction (ADR-0019) and the datatype free-variable
  expansion both establish "abstract the hard sub-terms to fresh variables
  (relaxation), solve the residual, replay/refine" as a sound, reusable pattern;
  NRA fits it exactly, reusing `replace_subterms`, `check_with_lra_dpll`, and the
  ground evaluator with no new core machinery.
- Tests (`tests/nra.rs`): `x·y = 5 ∧ x·y = 6` → `unsat`; `x·y = 6 ∧ x = 2 ∧ y =
  3` → `sat` (replay confirms `2·3 = 6`); `x·y = 6 ∧ x = 2 ∧ y = 4` → never a
  wrong `sat` (returns `unknown`/`unsat`); linear queries delegate straight to
  LRA.

## Alternatives

- **Full CAD / Gröbner / virtual substitution.** The complete approaches;
  deferred — far more code and soundness surface. The abstraction lands a sound,
  useful slice now and reuses the proven LRA path, exactly as bounded LIA
  preceded the integer simplex and lazy-BV preceded heavier BV reasoning.
- **Incremental linearization (cvc5-style).** A natural *refinement* of this
  ADR: on a replay failure, add lemmas (`r = x·y` tangent planes, sign/monotonicity
  axioms) and re-solve. This slice stops at one round (`unknown` on failure); the
  refinement loop is the next step and does not change the soundness basis.

## Consequences

- **Easier:** nonlinear-real queries no longer fall over; many are decided
  soundly (same-product contradictions, linearly-pinned products), and the rest
  are honest `unknown`s. Reuses the entire LRA stack.
- **Harder / next:** completeness — the refinement loop (linearization lemmas),
  and eventually a real nonlinear core — is future work. `unknown` is first-class
  here, never an error.
- **Revisited when:** a workload needs the nonlinear facts the abstraction drops
  (then incremental linearization), mirroring how bounded slices preceded the
  fuller procedures elsewhere in the stack.
