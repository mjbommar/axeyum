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

## Crate / module layout

A new internal crate keeps the math core reusable (NIA, quantifier elimination,
SOS reconstruction all consume it) and keeps `axeyum-solver` lean:

```
crates/axeyum-poly/                  (NEW — pure-Rust, no_std-friendly, no C/C++)
  src/
    rational.rs        # re-export / extend axeyum_ir::Rational; bigint fallback
    monomial.rs        # Monomial = sorted (var,exp) vector; ordering
    mpoly.rs           # sparse multivariate polynomial
    upoly.rs           # dense univariate; GCD, pseudo-division
    resultant.rs       # Sylvester resultant, subresultant (PSC) chain, discriminant
    sturm.rs           # Sturm sequence, Descartes' rule, root counting
    root_isolation.rs  # isolating intervals; refinement
    algebraic.rs       # RealAlgebraic: defining poly + interval; cmp/arith/sign
    interval.rs        # interval arithmetic (correctly rounded rationals)
    projection.rs      # McCallum / Lazard projection operators

crates/axeyum-solver/src/nra/        (NEW module tree — replaces nra*.rs files)
    mod.rs             # entry: tiered orchestrator (replaces check_with_nra)
    abstract.rs        # nonlinear-atom → fresh-var abstraction (from nra.rs)
    linearize.rs       # Tier 1: lemma-on-demand loop + lemma schemas
    icp.rs             # Tier 2: interval constraint propagation
    nlsat.rs           # Tier 3: model-constructing search + explain
    cac.rs             # Tier 3 alt: cylindrical algebraic coverings
    nia.rs             # Phase E: integer relax + branch-and-bound (absorbs nia_square)
```

Existing `nra_real_root.rs` (single-variable, exact, already excellent) is
retained as a **fast pre-path** and as a differential oracle for the new
multivariate code on single-variable instances.

> **ADR required** before the crate lands: `axeyum-poly` as a new boundary
> (per ADR-0001 "add crates only after a boundary is proven by use" — the
> boundary is proven by NRA+NIA+QE+SOS all consuming it). Decide there: own
> arbitrary-precision integers vs. a vetted pure-Rust bigint dep (must keep
> `forbid(unsafe_code)` and WASM build green).

## The Tier-3 choice: NLSAT/MCSAT vs CAC

Both are complete for QF_NRA; both need the same Phase-A core. Decision deferred
to an ADR after Phase A, but the current lean (see
[06-phaseD-nlsat-cac.md](06-phaseD-nlsat-cac.md)):

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
