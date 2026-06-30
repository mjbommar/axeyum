# P2.5 · Phase B — Incremental linearization (the cheap front layer)

**Size:** M–L · **Depends on:** Phase A (polynomials, lemma builders) · **Delivers
the first measured NRA/NIA decide-rate gain.**

> This is the highest-leverage first increment. It generalizes axeyum's existing
> `x*x` / even-power handling and the McCormick/SOS lemmas in `nra.rs` into a
> principled lemma-on-demand CEGAR loop (Cimatti et al., TOCL 2018). Sound,
> incomplete, `unknown`-safe — exactly the axeyum stance.

## The loop (CEGAR over LRA+EUF)

1. **Abstract.** Replace every nonlinear multiplication `x*y` (and power, and —
   later — transcendental application) with a fresh variable / uninterpreted
   function `f_mul(x,y)`. The residual is pure **LRA+EUF**, which axeyum already
   solves well.
2. **Solve** the abstraction with the existing LRA online solver (and EUF on the
   e-graph once P1.4/P1.5 land; today via the one-shot refinement loop in
   `nra.rs`).
3. **UNSAT ⇒ original UNSAT** (sound: the abstraction has *more* models). Retain
   the linear refutation as the certificate.
4. **Model found ⇒ check** each `f_mul(a,b) = a·b` against the candidate. If all
   hold, the candidate **replays** ⇒ `sat` (drop fresh vars first). Otherwise pick
   the falsified products and add **lemma instances** that exclude this spurious
   model; go to 2.
5. **No refinement possible / budget hit ⇒ `unknown`** (never a guess).

## Lemma schemas (implement in this order)

| Lemma | Form (product `r = x·y`) | Purpose |
|---|---|---|
| **Zero** | `r = 0  ⟺  x = 0 ∨ y = 0` | already in `nra.rs`; keep |
| **Sign** | `(x≥0∧y≥0)→r≥0`, `(x≤0∧y≥0)→r≤0`, … | already in `nra.rs`; keep |
| **Commutativity** | `f_mul(x,y) = f_mul(y,x)` | EUF sharing of equal monomials |
| **Monotonicity** | `(x₁≤x₂ ∧ y≥0) → x₁·y ≤ x₂·y`, … | already partially in `nra.rs` |
| **Tangent-plane** | at spurious `(a,b)`: `T_{a,b}(x,y)=b·x+a·y−ab`; add the four quadrant bounds `(x>a∧y<b)∨(x<a∧y>b) → r<T`, etc. | the central refinement — exact at `(a,b)`, bounding elsewhere |
| **Monomial bounds** | propagate bounds across shared monomials (cvc5 `MonomialBoundsCheck`) | tighten the LRA relaxation |
| **Factoring** | `x·z + y·z` → introduce `k=x+y`, `k·z` | catch common-factor refutations |

cvc5's ordering (from the internals survey): init/factoring → flatten-monomial →
sign → magnitude-0/1/2 (increasing density) → infer-bounds → tangent-planes → ICP
(Phase C) → coverings (Phase D). Mirror this staging so cheap lemmas fire first.

## Monomial sharing (emonics)

Share equal monomials so `x·y` reasoned about once even if it appears many times
(Z3 `emonics`; cvc5 `MonomialDb` trie). This is the T2.5.1 task from the original
stub and is a prerequisite for the monomial-bounds lemmas being effective.

## Transcendentals (stretch, within Phase B)

`sin`, `cos`, `exp`, `log`: tangent-line + secant-line piecewise-linear
upper/lower bounds chosen numerically to stay **sound under irrationals**, plus
sign / monotonicity / known-value lemmas (Cimatti CADE-26 2017). Surfacing `sat`
here requires a model-checkable witness — for transcendentals that usually means
deferring `sat` to `unknown` and only trusting the **UNSAT** direction (same
discipline as ICP, Phase C).

## Implementation path: reuse the `dpll_t` lazy-SMT loop (the #66 keystone)

> **Code-grounded 2026-06-30.** The measurement showed the dominant QF_NRA gap is
> **Boolean structure** — the CAD only sees flat conjunctions
> ([08-evaluation §root cause](08-evaluation-and-soundness.md)). The good news from
> reading the code: the lazy-SMT loop that handles Boolean structure **already
> exists** in `crates/axeyum-solver/src/dpll_t.rs` (`check_with_lra_dpll_within`):
>
> 1. abstract each atom to a proposition; SAT-solve the Boolean skeleton;
> 2. read the chosen atoms' truth into a **conjunction** `theory_lits`;
> 3. **theory-check** that conjunction — *currently* `check_with_lra_within`;
> 4. on a theory conflict, learn the blocking clause (the infeasible core);
> 5. verified-sound: "neither the propositional nor the theory search can yield an
>    unsound `sat`", and `certify_lra_dpll_unsat` lifts the Farkas certificate to
>    arbitrary Boolean structure.
>
> **The conjunctive cube `theory_lits` is exactly what `decide_real_poly_constraint`
> (the CAD) consumes.** So the keystone is not a new DPLL(T) — it is:
>
> - **B.0a** Generalize the `dpll_t` loop so the **theory-check step (3) is
>   pluggable** (pass a `Fn(&[TermId], deadline) -> Result<CheckResult,_>` instead
>   of hard-wiring `check_with_lra_within`). Pure refactor; the LRA path stays
>   identical (regression-clean).
> - **B.0b** Add `check_with_nra_dpll` that drives the same loop with a **nonlinear
>   theory check**: try `decide_real_poly_constraint` (CAD) on the cube first, then
>   the `nra.rs` relaxation; `unsat` cube → blocking clause, `sat` cube
>   (replay-checked) → `sat`, `unknown` cube → bounded retry then `unknown`.
> - **B.0c** Route `check_with_nra` to `check_with_nra_dpll` when the query has
>   Boolean structure over nonlinear atoms (today it declines/relaxes). Re-measure.
> - **Soundness:** the CAD theory-check is already sound (replay-checked `sat`,
>   exact `unsat`); the `dpll_t` blocking-clause machinery is already verified. The
>   conflict core for a nonlinear `unsat` cube is initially the whole cube
>   (sound, coarser lemmas) — minimize later. Gate with `nra_differential_fuzz`.
>
> This is the measured highest-leverage NRA increment: it unlocks the existing
> decision-complete CAD on real (Boolean-structured) benchmarks. It is also the
> concrete first slice of the full [CDCL(T) loop (P1.5)](../../track-1-engine/P1.5-cdcl-t-loop.md).

## Tasks

| id | task | size | exit |
|---|---|---|---|
| T-B.1 | Refactor `nra.rs` abstraction into `nra/abstract.rs` + `nra/linearize.rs`; preserve current behavior (regression-clean) | M | identical verdicts to today on the existing suite |
| T-B.2 | Monomial DB + commutativity/emonics sharing | M | repeated monomials reasoned once; measured node reduction |
| T-B.3 | Full tangent-plane lemma generator (4 quadrant bounds) replacing the ad-hoc point lemmas | M | more NRA instances decided (measured) |
| T-B.4 | Monomial-bounds + factoring lemmas | M | additional measured gains |
| T-B.5 | Lift the ≤2-cross-product cap once lemmas + monomial sharing keep LRA bounded (re-measure the OOM threshold) | M | cap raised without OOM regression on the 64 GB box |
| T-B.6 | (stretch) transcendental tangent/secant lemmas, UNSAT-only | L | transcendental UNSAT instances decided; `sat`→`unknown` |

## Exit criteria

- The incremental-linearization loop is a clean module on the Phase-A core, behaves
  identically to today on the existing suite, then **measurably** raises the
  NRA/NIA decide-rate on the public corpora (re-run the scoreboard).
- Every `sat` replays; every `unsat` retains the linear refutation certificate.
- The ≤2-cross-product cap is raised (or removed) with a re-measured OOM threshold,
  documented.
- `nra_differential_fuzz` (vs Z3) stays DISAGREE=0.
