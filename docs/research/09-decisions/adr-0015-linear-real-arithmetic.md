# ADR-0015: Linear Real Arithmetic via Exact-Rational Simplex

Status: accepted
Date: 2026-06-13

## Context

The arithmetic rung now covers bounded `QF_LIA` (integers, bit-blasted —
[ADR-0014](adr-0014-first-arithmetic-fragment.md)) and all theories compose
through one eager pipeline. The next theory is **quantifier-free linear real
arithmetic (`QF_LRA`)**. Reals are qualitatively different from every theory so
far: they are *not finite-domain*, so they cannot be bit-blasted onto the
`QF_BV` core. `QF_LRA` therefore forces the project's **first non-`QF_BV`
decision procedure** — the step the north star always required, and the reason a
separate ADR is needed rather than reusing ADR-0014's bounded-blasting route.

Trust identity (untrusted search, trusted checking) still applies: a `sat` must
carry a model the ground evaluator can check, and the model for reals is a
**rational** assignment.

## Decision

Adopt `QF_LRA` with an **exact-rational simplex** decision procedure, staged the
way every prior theory was.

- **`Real` is a first-class IR sort.** The IR gains a `Real` sort, rational
  constants, and the linear operator set (`+`, `-`, unary `-`, `*`, and the
  order comparisons `<`, `<=`, `>`, `>=`); equality and `ite` are already
  polymorphic. This is sub-increment 1.
- **Values are exact rationals.** A pure-Rust `Rational` (normalized `i128`
  numerator/denominator, no external bignum dependency — Hard Rules) is the
  evaluator's real value. The evaluator is exact within the `i128` reference
  range; out-of-range intermediate values are a usage error, consistent with the
  bounded-first stance of ADR-0014. Exact rationals (not floats) are mandatory:
  the model must be *checkable*, and floating point is neither exact nor sound.
- **Decision procedure: exact-rational simplex** (later sub-increment). A
  general-simplex / Fourier–Motzkin-class procedure over conjunctions of linear
  constraints produces a rational model for `sat` and detects infeasibility for
  `unsat`. The procedure is untrusted: every `sat` model is replayed through the
  ground evaluator against the original constraints (the trust anchor), so a bug
  in the search cannot produce an unsound `sat`.
- **Linearity is a fragment property, not an IR ban.** `*` stays in the IR and
  the evaluator multiplies general rationals; the linear restriction (at most one
  non-constant factor) is enforced/exploited by the procedure, so the IR does
  not foreclose nonlinear real arithmetic later.

## Evidence

- Exact-rational simplex is the standard `QF_LRA` core (e.g. the
  Dutertre–de Moura general simplex used in modern SMT solvers); rationals keep
  it sound and the model checkable, unlike floating point.
- Sub-increment 1 (sort + rationals + evaluator) is validated the way the array,
  EUF, and integer IR increments were: exhaustive/﻿targeted small-value checks of
  the rational arithmetic and comparison semantics.
- A `Rational` over `i128` needs no C/C++ or external crate, honoring the
  default-build Hard Rule.

## Alternatives

- **Bit-blast reals (fixed-point).** Rejected: fixed-point is not real
  arithmetic; it reintroduces rounding/overflow unsoundness and cannot represent
  arbitrary rationals a simplex pivot produces.
- **Floating-point simplex.** Rejected: fast but unsound; the resulting model is
  not exactly checkable, breaking the trust identity. Exact rationals are
  required even if slower.
- **`i128` arbitrary fallback only / require a bignum crate now.** Deferred:
  `i128` rationals decide the small instances the first slice targets; a bignum
  backing (still pure Rust) can be introduced later under its own decision if
  overflow becomes the binding limit.

## Implementation Progress

- 2026-06-13: sub-increment 1 (IR + evaluator) shipped — a pure-Rust exact
  `Rational` (`i128` numerator/denominator, normalized, with `Neg`/`Add`/`Sub`/
  `Mul`/`Ord` and overflow-checked arithmetic), the `Real` sort, `RealConst`,
  the linear operator set (`real_add`/`real_sub`/`real_neg`/`real_mul` and the
  order comparisons), `Value::Real`, and evaluator support. The rational
  arithmetic and the operator semantics are checked against an exact reference
  over a grid of fractions. The `Real` sort rippled across all crates; the
  pure-Rust BV backend (via `first_unsupported_sort`) and the Z3 oracle reject
  `Real` with a clear `Unsupported`, exactly as integers were staged before
  bit-blasting.
- 2026-06-13: the first decision procedure shipped — `axeyum_solver::check_with_lra`
  decides **conjunctive** `QF_LRA` by **exact-rational Fourier–Motzkin
  elimination** (chosen over full simplex for the first slice: exact, complete,
  and far simpler to get right; δ-rational simplex is the scalable upgrade). It
  parses assertions into linear atoms (`and`/`not` pushed in, equality split
  into two inequalities; `or`/disequality → `Unsupported`, needing DPLL(T)),
  eliminates variables over exact rationals, and reconstructs a rational model by
  forward substitution. Every `sat` model is **replayed through the evaluator**
  (the trust anchor — a Fourier–Motzkin bug cannot produce an unsound `sat`);
  `unsat` is currently lower-assurance (Farkas certificate is the planned
  evidence). End-to-end tests: strict interval with a fractional witness, empty
  interval → `unsat`, two-variable system, `3x = 1` pinning `x = 1/3`, a strict
  cycle → `unsat`, and disjunction → `Unsupported`. Remaining `QF_LRA`:
  scenarios, SMT-LIB I/O, and (later) DPLL(T) for full Boolean structure plus a
  δ-rational simplex for scale.
- 2026-06-13: `QF_LRA` scenarios and SMT-LIB I/O shipped — a `Family::Real` in
  `axeyum-scenarios` (`real_system` boxed/ordered/sum-pinned rational systems,
  `real_ratio_equation` pinning fractional witnesses) with `real_catalog`,
  decided through `check_with_lra` in a solver differential test; and the
  SMT-LIB parser/writer now handle the `Real` sort, decimal literals (`n.ddd`),
  `(/ a b)` rational division, `(- n)` negation, **sort-directed `+`/`-`/`*`/
  comparisons** that coerce integer numerals to `Real` in real contexts, and a
  `QF_LRA` round-trip (integer-valued reals render as `n.0` so they never
  re-parse as `Int`). The `QF_LRA` rollout now matches the other theories end to
  end (modulo the deferred DPLL(T) Boolean structure and δ-rational simplex).
- 2026-06-13: **lazy SMT / DPLL(T) shipped** — `axeyum_solver::check_with_lra_dpll`
  lifts the conjunction-only limit: it Boolean-abstracts each real order atom to
  a fresh proposition, solves the propositional skeleton with `SatBvBackend`,
  checks the chosen atom literals with the conjunctive `check_with_lra`, and
  learns a blocking clause on each theory conflict until SAT and theory agree (or
  the skeleton is exhausted → `unsat`). Termination is by finitely many atom
  assignments; every `sat` model is replayed against the original assertions (the
  trust anchor). End-to-end tests: a disjunction of real constraints (previously
  `Unsupported`) now decides, a feasible-branch case split, a
  Boolean-unsatisfiable combination → `unsat`, mixed Boolean variables and theory
  atoms, and pure conjunctions. This is the **lazy theory-combination engine**;
  generalizing it across multiple theories at once (Nelson-Oppen) and adding
  real equality/disequality are the next steps. Invariant surfaced and fixed: the
  SAT backend completes *all* declared symbols (including real theory variables)
  to defaults, so only Boolean values are taken from the propositional model —
  the theory solver owns the real assignment.
- 2026-06-13: **real equality/disequality** added to the lazy-SMT path — a real
  `(= a b)` atom abstracts to `(a <= b) and (a >= b)`, so equality and its
  negation (disequality `a < b or a > b`) flow through the existing order-atom
  machinery and the SAT case split; no special disequality reasoning in the FM
  theory solver is needed. Tests: a disjunction of real equalities, a
  disequality forcing a contradiction (`x != 0 ∧ x <= 0 ∧ x >= 0` → `unsat`),
  and a satisfiable disequality. Remaining `QF_LRA`: a δ-rational simplex for
  scale, and Nelson-Oppen combination with the bit-blasted theories.
- 2026-06-13: **Farkas `unsat` certificates shipped** — the planned `unsat`
  evidence is now real. `check_with_lra` threads a nonnegative multiplier vector
  through Fourier–Motzkin (each original constraint starts as a unit vector;
  each elimination step `(-b)·p + a·n` accumulates the combination with positive
  scalars), so the infeasible residual constant constraint names the Farkas
  multipliers behind it. `FarkasCertificate { atoms, multipliers }` and
  `FarkasCertificate::verify` rebuild the refutation independently of the
  elimination — checking the multipliers are nonnegative and not all zero, that
  `Σ λ_i · atom_i` cancels every variable, and that the residual constant
  relation is itself false (`0 < 0` or `0 <= -c`, `c > 0`). The certificate is
  **self-checked before `check_with_lra` returns `unsat`**; a failed check is a
  `SolverError::Backend` soundness alarm, so a Fourier–Motzkin bug can no more
  produce an unsound `unsat` than the model-replay anchor lets it produce an
  unsound `sat`. Since the lazy-SMT/DPLL(T) loop routes theory checks through
  `check_with_lra`, every real-theory conflict is certificate-checked
  automatically. `lra_farkas_certificate` exposes the certificate for external
  auditing. This makes `QF_LRA` `unsat` **no longer lower-assurance** — it is the
  exact-arithmetic dual of DRAT for `QF_BV`. Tests: empty interval, strict cycle,
  and conflicting equalities each yield a verifying certificate; a `sat` query
  yields none; tampered certificates (dropped/negative/zeroed multiplier, a
  hand-made non-refutation) are rejected. Also wired into the consumer-facing
  `Evidence` envelope (`Evidence::UnsatFarkas` + `produce_lra_evidence`, whose
  `check` re-runs `verify`), and used in the DPLL(T) loop for **theory-conflict
  minimization** — the nonzero-multiplier atoms are the infeasible core, so the
  learned blocking clause negates just that core (sound and strictly stronger
  than blocking the full atom assignment, giving faster convergence). And
  `lra_unsat_core` reads the Farkas support (the assertions whose constraints
  have a nonzero multiplier) to seed a deletion-minimized, re-verified minimal
  unsatisfiable core — the SMT-LIB `get-unsat-core` capability, useful for
  explaining infeasible paths.
- 2026-06-13: **DPLL(T) `unsat` refutation certificates (pure-real)** —
  `certify_lra_dpll_unsat` generalizes the conjunctive Farkas certificate to
  arbitrary Boolean structure over real order atoms. On `unsat` it returns a
  self-checked `LraDpllRefutation`: the Boolean skeleton (one term per assertion,
  atoms abstracted to fresh propositions) plus the lazy-SMT loop's learned theory
  lemmas (each an infeasible real-atom core, the same minimized core used for the
  blocking clause). `LraDpllRefutation::verify` re-checks it independently of the
  search — (1) every lemma core is re-decided `unsat` by `check_with_lra` (itself
  Farkas-self-checked), so each lemma clause holds in every real model, and (2)
  the skeleton with all lemma clauses is propositionally unsatisfiable, confirmed
  by enumerating all Boolean assignments (capped at 22 symbols → otherwise a
  classified `unknown`, never an unverified certificate). Soundness: a real model
  of the original would induce a truth assignment satisfying the skeleton and
  every lemma clause, which (2) forbids; the abstraction is the trusted reduction,
  exactly as bit-blasting is trusted on the DRAT route. Self-verified before
  return (failure → `SolverError::Backend` alarm). Tests: a case-split conflict
  certifies + verifies, a `sat` query returns a replaying model, bit-vector
  content is rejected `Unsupported`, and a lemma-stripped refutation fails
  verification. Remaining: certify the lazy-SMT `unsat` when the skeleton also
  carries bit-blasted theories (the propositional half then needs a DRAT proof,
  not enumeration).
  Follow-up: a δ-rational simplex for scale must produce the same certificate.
- 2026-06-13: **exact-rational general simplex** added —
  `axeyum_solver::check_with_lra_simplex` decides the same conjunctive `QF_LRA`
  fragment by the Dutertre–de Moura "simplex with bounds" over exact δ-rationals
  (the δ infinitesimal encodes strict inequalities exactly; the witness is
  de-infinitesimalized by choosing a small concrete δ). It is a **second,
  independent** LRA engine guarded by the same trust anchors: every `sat` model
  is replayed through the ground evaluator, and every `unsat` is **cross-checked
  against the Fourier–Motzkin Farkas certificate** (a disagreement is a
  `SolverError::Backend` soundness alarm). A 2000-case differential fuzz test
  confirms the two engines agree on every verdict. This is the project's
  characteristic move — two independent procedures validating each other.
- 2026-06-13: **native Farkas extraction** — the simplex now certifies its own
  `unsat` from the final tableau (no Fourier–Motzkin dependency). At
  infeasibility the violating slack `b` is above its upper bound and cannot
  decrease, so every blocking nonbasic is a slack at its upper bound with a
  negative coefficient `c_n`; the refutation multipliers are `1` on `b`'s
  constraint and `−c_n` on each blocking slack's constraint, which collapse to a
  positive constant exactly because `b` violates its bound. The extracted
  `FarkasCertificate` is self-checked before `unsat` is returned (a failed check
  is a `SolverError::Backend` alarm — the safety net for the tableau-extraction
  logic), and the 2000-case differential fuzz exercises it on every `unsat`.
  Fourier–Motzkin now only backs up the (practically unreachable) iteration cap.
  The scale benefit over Fourier–Motzkin appears on large systems not yet in the
  corpus.

## Consequences

- The IR expresses `QF_LRA`; the evaluator is its exact semantic reference, so a
  future simplex's `sat` models are checkable end to end.
- Backends that cannot handle `Real` (the pure-Rust BV bit-blaster via
  `first_unsupported_sort`, the Z3 oracle) reject it with a clear `Unsupported`
  until the simplex sub-increment lands — exactly as integers were staged before
  bit-blasting.
- The Fourier–Motzkin core is the first procedure **not** reducible to the
  trusted `QF_BV` kernel. Its `unsat` is now backed by a self-checked Farkas
  certificate (the exact-arithmetic dual of DRAT for SAT), so it is no longer
  lower-assurance: model replay guards `sat`, the Farkas combination guards
  `unsat`. A future δ-rational simplex must produce the same certificate to keep
  this guarantee.
- A later ADR is needed before mixed integer/real (`QF_LIRA`), nonlinear
  arithmetic, or a bignum rational backing.
