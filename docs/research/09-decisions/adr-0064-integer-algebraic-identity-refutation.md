# ADR-0064: Integer-aware, UNSAT-only polynomial-identity refutation (QF_NIA)

Status: accepted
Date: 2026-07-08

## Context

A class of `QF_NIA` unsats is genuinely **integer-specific**: the real
relaxation is *satisfiable*, so the multivariate CAD path
(`decompose_multivariate` in `crates/axeyum-solver/src/nra_real_root.rs`, which
requires `Sort::Real` at every collector — lines with `!= Sort::Real`) can never
see them, and the bounded int-blast finds no model within its width yet cannot
conclude `unsat` (the variables are unbounded). The keystone is the cvc5 regress
row `cli__regress1__nl__nl-eq-infer` (`QF_NIA`, unsat):

```
i = −2s + i²          (E1: i² − i − 2s = 0)
i − n ≥ 1             (E2)
¬(i − n ≥ 2)          (E3: i − n < 2  ⟺  i − n ≤ 1 over ℤ)
¬(n = 2s − n²)        (D:  n² + n − 2s ≠ 0)
```

Over ℝ this is SAT (`i − n = 3/2, i = 0, s = 0`), so no real decision procedure
refutes it. Over ℤ, E2 ∧ E3 pin `i − n = 1`; substituting `n = i − 1` and
`s = (i² − i)/2` (from E1) into D's polynomial collapses it **identically** to
`0`, so D asserts `0 ≠ 0` — UNSAT. This is a polynomial *identity* refutation
that is only valid over the integers.

The question: **how do we decide this integer-identity class without opening a
wrong-unsat (or wrong-sat) hole?** The substitution `s = (i² − i)/2` has a
*rational* coefficient, which — if it fed a SAT-model construction — could
produce a non-integer witness (wrong-sat over `QF_NIA`, the `a946f925`-class
trap). And the tight-bound step `i − n < 2 ⊢ i − n ≤ 1` is valid *only* over ℤ.

## Decision

**Add an integer-aware, UNSAT-only polynomial-identity refutation
(`integer_algebraic_refutation`, `nra_real_root.rs`), wired as an
`Unknown`-fallback in `check_auto` / `check_auto_explained` (`auto.rs`, trace
route `integer-algebraic-refutation`).**

The route:

1. Collects every assertion as an **integer** polynomial comparison `poly ⋈ 0`
   (`collect_int_multi_conjuncts` / `match_int_multi_constraint` /
   `collect_int_multi`, the `Op::Int*` / `IntConst` analogues of the existing
   real collectors); any non-integer / non-polynomial shape **declines**.
2. Derives the equalities to substitute: the asserted `Eq` atoms, plus
   **integer tight-bounds** — every inequality atom is normalized to `g ≥ 0`
   (`atom_as_ge`, integer-tightening strict `<`/`>` by ±1), and a pair
   `g ≥ 0`, `−g ≥ 0` from two atoms pins `g = 0`.
3. Runs a substitution fixpoint: each equality that isolates a variable
   (`as_linear_definition`, or a standalone-linear variable via the new
   `MultiPoly::solve_for_var`) is substituted into the other equalities **and**
   the asserted disequalities. A disequality that reaches the **zero
   polynomial** is `0 ≠ 0` ⇒ **UNSAT**; a residual equality that reduces to a
   nonzero constant is likewise UNSAT.

**Soundness rests on three pillars:**

- **UNSAT-only — never a model.** The route returns `true` (⇒ `Unsat`) or
  `false` (decline); it never constructs a witness. Hence the rational-coefficient
  substitution `s = (i² − i)/2` carries **no wrong-sat risk** — it is used solely
  to reduce an asserted disequality to the zero polynomial. This is the decisive
  design choice that sidesteps the integer/rational trap that reverted the naive
  "extend `decompose_multivariate`'s elimination loop" attempt (0-ROI *and*
  soundness-fragile).
- **Every substitution is an asserted consequence.** `y := L` comes from an
  asserted equality `poly = 0` (a valid ℚ-consequence at every model satisfying
  it), and each injected `g = 0` follows from two asserted inequalities
  `g ≥ 0 ∧ −g ≥ 0`. So when an asserted `p ≠ 0` reduces to `0`, the conjunction
  is unsatisfiable over ℤ (indeed over ℚ).
- **One integer-specific step, explicitly gated.** The strict-to-non-strict
  tightening `p < 0 ⟺ −p − 1 ≥ 0` is the *only* place integrality is used, and
  it is sound because the collectors accept **only** `Int`-sorted terms (the
  route is unreachable for `QF_NRA`). All arithmetic is exact `Rational`;
  overflow declines.

The route fires **only on an `Unknown` verdict** (additive; it never downgrades
a route-produced `sat`/`unsat`) and is verdict-invariant between `check_auto`
and `check_auto_explained` (pinned by `route_trace`).

## Evidence

- Decides `nl-eq-infer` (`QF_NIA`, unsat) matching cvc5 + `:status`; the
  `frontier_nia_unsat` ratchet holds (`progress_frontier` 8/8).
- Unit gate `tests/nia_algebraic_refutation.rs` (5): the keystone unsat, a
  minimal tight-bound identity, and **three wrong-sat-negatives** — a genuinely
  satisfiable integer query (no upper bound; a *loose* `[1,3)` bound that does
  not pin the difference; a free polynomial disequality) must **not** be refuted
  (asserts `≠ Unsat`).
- `corpus_regression` DISAGREE = 0 (`:status`), `--lib` 731 passed,
  `route_trace` 6 passed, clippy `-D warnings` clean.
- **z3 `nia_differential_fuzz` (2500 instances, ~2082 jointly decided vs Z3) +
  `nra_differential_fuzz` (2000 instances): DISAGREE = 0** — the adversarial
  vs-Z3 gate for a wrong-unsat/wrong-sat on the integer path.

## Alternatives

- **Extend `decompose_multivariate`'s elimination loop with `solve_for_var`**
  (the first attempt) — rejected: `nl-eq-infer` is `QF_NIA` and never reaches
  that `Sort::Real`-gated path, so it had **0 corpus ROI**, *and* it fed the
  rational def into a SAT-model build (wrong-sat trap over ℤ). Measured and
  reverted under measure-don't-seed.
- **Real-relaxation of the `QF_NIA` query into the CAD** — rejected: unsound-for-
  this-class in the sense that it *cannot* decide it — the relaxation is SAT, so
  the CAD returns `sat`/`unknown`, never the (integer-only) `unsat`.
- **Bounded int-blast at larger width** — rejected: the variables are unbounded
  (`i`, `n`, `s` with only a bounded *difference*), so no finite width proves
  unsat.
- **Emit a SAT model from the substitution** (make the route two-directional) —
  rejected: reintroduces the rational-def wrong-sat trap. UNSAT-only is a
  deliberate soundness boundary.

## Consequences

- **Easier:** a genuinely integer-specific unsat class now decides soundly;
  `MultiPoly::solve_for_var` / `as_solvable_definition` are reusable isolation
  primitives (standalone-linear variable amid nonlinear terms).
- **Harder / revisit:** the route is conservative (identity-to-zero only). It
  does not yet handle disequality *inequalities* (`p ≤ 0` refuted by a lower
  bound identity) or multi-disequality resolution; broadening is gated on
  measured corpus ROI (measure-don't-seed).
- **Standing rule:** this is an unsat-emitting route on the soundness-fragile
  integer-arithmetic axis — every change must re-run `nia_differential_fuzz`
  (DISAGREE = 0 absolute) plus the wrong-sat-negatives, because a rational-def or
  tight-bound slip is a wrong-verdict.

## Backlinks

- Code: `crates/axeyum-solver/src/nra_real_root.rs`
  (`integer_algebraic_refutation`, `atom_as_ge`, `collect_int_multi*`,
  `MultiPoly::solve_for_var` / `as_solvable_definition`), `auto.rs` (the two
  `Unknown`-fallback hooks).
- Tasks #88 (this route), #83/#86 (arithmetic residue map that surfaced the
  class), #84/#85 (deadline bounding — the sibling NIA-path work).
- Related: ADR-0058 (funded NRA CAD/nlsat arc — the real-side engine this
  complements), ADR-0060 (arith online CDCL(T) dispatch).
