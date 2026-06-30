# P2.5 · 02 — Architecture: the layered nonlinear engine

## Design principle: cheap-first, complete-last

Z3 and cvc5 both run nonlinear arithmetic as a **portfolio of cooperating
procedures**, ordered cheapest-to-most-complete, all feeding the same CDCL(T)
core. We adopt the same shape. A query is attacked in tiers; each tier either
decides, prunes, or escalates:

```
            ┌─────────────────────────────────────────────────────────┐
            │  CDCL(T) core (Track 1, P1.5) — Boolean skeleton + LRA    │
            │  linear arithmetic solver gives the model candidate       │
            └───────────────┬─────────────────────────────────────────┘
                            │ nonlinear atoms abstracted to fresh vars
                            v
   TIER 1  Incremental linearization  (Phase B) ── lemmas on demand:
           sign · zero · monotonicity · tangent-plane · factoring · monomial bounds
                            │  (incomplete; catches the easy majority, fast)
                            v
   TIER 2  Interval Constraint Propagation  (Phase C) ── contract boxes,
           cheap refutation + feasibility witnesses; filters before the oracle
                            │  (sound, incomplete; δ-sat optional for transcendental)
                            v
   TIER 3  Complete oracle  (Phase D) ── NLSAT/MCSAT  *or*  Cylindrical Algebraic
           Coverings: model-constructing search with algebraic-number assignment,
           projection by resultants/discriminants/PSC
                            │  (COMPLETE for QF_NRA, behind a resource budget)
                            v
                    sat (model) │ unsat (covering/proof) │ unknown (budget hit)
```

All three tiers sit on the **Phase A algebraic core** (polynomials, root
isolation, real algebraic numbers, sign determination). NIA (Phase E) wraps the
whole stack with real-relaxation + branch-and-bound + a bounded bit-blast finish.

## Why layered and not "just build CAD"

- Tier 1 alone closes a large fraction of the practical gap in weeks, and gives a
  **measured** decide-rate improvement long before the oracle lands. This is the
  cvc5 lesson: incremental linearization is the default; coverings are the fallback.
- Tier 3 is doubly-exponential worst case; you never want to run it when Tier 1/2
  suffices. The tiers also generate *theory lemmas* that help the SAT core prune,
  not just final verdicts.
- Each tier is independently soundness-checkable and independently fuzzable.

## Component dependency DAG (the real build order)

```
rational/bigint  (exists: axeyum_ir::Rational; needs arbitrary-precision lift)
      │
      ├─> multivariate polynomial  (sparse: monomial→coeff)
      │        │
      │        ├─> univariate polynomial (dense)  ──> resultant / subresultant (PSC)
      │        │            │                                   │
      │        │            └─> root isolation (Sturm/Descartes)│
      │        │                        │                       │
      │        │                        v                       │
      │        │              real algebraic numbers <──────────┘
      │        │                        │
      │        │                        └─> sign determination at α
      │        │
      │        └─> McCormick / tangent-plane lemma builders (Tier 1)
      │
      ├─> interval arithmetic ──> ICP contractors (Tier 2)
      │
      └─> projection operator (McCallum/Lazard)  ──┐
                                                   ├─> NLSAT explain / CAC covering (Tier 3)
              algebraic-number assignment ─────────┘
                          │
                          └─> NIA: real-relax + branch-and-bound (Phase E)
```

The **long pole is the algebraic core** (Phase A): resultants, root isolation,
and robust algebraic-number arithmetic. Everything in Tiers 1–3 is comparatively
shallow once that core is solid and well-tested.

## Crate / module layout — extend `axeyum-ir`, do NOT add a crate

> **Corrected per ADR-0044.** An earlier draft proposed a new `axeyum-poly` crate.
> That contradicts the **accepted** ADR-0044, which deliberately put the exact-poly
> + Sturm + resultant primitives in **`axeyum-ir/src/poly.rs`** (one isolation
> implementation shared by the IR value layer and the solver) precisely because
> `eval` — which lives in `axeyum-ir` and must replay-check algebraic models —
> needs them, and ADR-0001 says split a crate only when a boundary is *exercised*
> (reuse satisfies it). **We extend the existing modules.**

The math core **already exists and is bignum-backed**:

```
crates/axeyum-ir/src/
  poly.rs            # EXISTS: RatVec + exact-Rational poly helpers (trim/degree/
                     #   deriv/rem/gcd/monic/exact-div/squarefree_part), Sturm core
                     #   (sturm_chain/count_roots_in/isolate_roots_sturm),
                     #   resultant_univariate / sylvester_determinant.  ADR-0044/0045.
  real_algebraic.rs  # EXISTS: Value::RealAlgebraic (Vec<BigInt>/BigRational),
                     #   sign_at, compare, field arithmetic α±β/α·β/−α.  ADR-0044/0046.
  ── to ADD: McCallum/Hong projection; richer multivariate mpoly ops as needed.

crates/axeyum-solver/src/
  nra_real_root.rs   # EXISTS: single-variable exact decider (fast pre-path + oracle)
  nra.rs             # EXISTS: linear-abstraction + McCormick + spatial B&B (the cheap
                     #   tier; Phase B upgrades it into a principled incr-lin loop)
  (CAD slices)       # EXIST: decide_nonstrict_cad_nvar_algebraic, visit_all_cells_value,
                     #   fiber_boundary_poly, multi_resultant, cell_samples, …
  ── to ADD: an incremental-linearization tier module (Phase B), an ICP module
     (Phase C), a per-cell certificate emitter (Phase D §evidence), and the NIA
     incr-lin UNSAT engine (Phase E).
```

So the build is **fill-in-the-gaps on an existing engine**, not greenfield. The
"long pole" framing in Phase A is downgraded accordingly (see
[00-current-state.md](00-current-state.md)).

## The Tier-3 choice is already made: we have CAD

> **Corrected.** This was framed as an open NLSAT-vs-CAC choice. In fact the
> roadmap already **built CAD directly** (projection-by-resultant + lifting +
> cell sampling; 2-var complete, N-var decision-complete, fuzz-gated). So Tier 3
> exists. The remaining Tier-3 work is **performance** (McCallum/Hong projection
> to cut cell blow-up) and **per-cell evidence** (Lean parity), not picking an
> engine. The NLSAT-vs-CAC table below is retained only as background for a
> possible future explanation-driven optimization.

| | NLSAT/MCSAT (Z3) | Cylindrical Algebraic Coverings (cvc5) |
|---|---|---|
| Search | model-constructing, conflict-driven | recursive interval covering |
| Explain | projection-based, tightly coupled to SAT trail | covering set → UNSAT cert |
| Proof story | harder to certify | covering is closer to a checkable object |
| Implementation surface | larger (trail, explain, watches) | self-contained recursion |
| Our lean | — | **CAC first** — smaller surface, better certificate story for Lean-parity (Track 3) |

We will likely build **CAC** as the primary complete oracle (cleaner certificate
for the trust ledger / Alethe) and keep NLSAT-style explanation as a possible
later optimization. Both are documented in Phase D.

## Soundness contract (every tier obeys)

1. `sat` ⇒ a concrete (rational or `RealAlgebraic`) assignment that **replays**
   through the ground evaluator against the original (un-abstracted) term.
2. `unsat` ⇒ either (a) Tier-1/2 relaxation refutation (sound because relaxation
   only grows the model space) with a retained certificate, or (b) a Tier-3
   covering / projection certificate that is independently re-checkable.
3. Anything else ⇒ `unknown` (budget, depth, degree, magnitude, transcendental).
4. No tier may convert another tier's `unknown` into `sat`/`unsat` without its own
   independent justification.

## Interaction with Track 1 (CDCL(T)) and Track 3 (proofs)

- Tiers 1–2 are **theory propagators** on the [CDCL(T) loop](../../track-1-engine/P1.5-cdcl-t-loop.md):
  they emit valid lemmas that the SAT core learns from. Until P1.5 lands they run
  as a one-shot refinement loop (today's `nra.rs` shape), which is the bridge.
- Tier-3 coverings are the natural **Alethe reduction-proof**
  ([P3.5](../../track-3-proof-lean/P3.5-reduction-proofs.md)) and **trust-ledger**
  ([P3.0](../../track-3-proof-lean/P3.0-trust-ledger.md)) object; the SOS fragment
  already reconstructs to Lean and is the seed for certified nonlinear `unsat`.
