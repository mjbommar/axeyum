# QF_BV proof-track operator coverage and extension paths (P3.7)

Status: **research/scoping (2026-06-18).** Maps exactly which BV operators the
Alethe→Lean **proof track** covers, why the boundary sits there, and the concrete
path to extend it. Grounded in inspection of the Carcara reference
(`references/carcara/carcara/src/checker/`).

## The covered set is exactly the 17 core bitblast operators

The emitter (`bitblast_alethe.rs`), the reconstruction (`reconstruct.rs`), **and**
Carcara's checker all support the same 17 `bitblast_*` rules — no more, no less:

```
var const not and or xor xnor extract sign_extend concat comp add neg mult equal ult slt
```

This three-way agreement is not a coincidence: the emitter only emits what Carcara
checks, and reconstruction only lifts what the emitter emits. Carcara's registered
bitblast rules (`grep -rhoE 'bitblast_[a-z_]+' references/carcara/src`) are exactly
this list.

## Status update (2026-06-18): route 1 LANDED for the cleanly-reducible ops

`axeyum_rewrite::lower_derived_bv` (`40e679b`) implements the front-end
denotation-preserving lowering for `bvsub`, `bvnand`, `bvnor`, and the six
unsigned/signed comparisons (`bvugt`/`bvule`/`bvuge`/`bvsgt`/`bvsle`/`bvsge`) → core.
Each rule is exhaustively checked denotation-preserving over all 3-bit inputs, and
`bvsub`/`bvule` queries now reconstruct end-to-end to a kernel-checked `False`
(`axeyum-solver` tests). **Remaining:** the route-2 `bv_poly_simp` upgrade (to certify
the *un-lowered* original), and shifts/division (no cheap reduction). The rest of this
note is the original analysis.

## The gap: derived operators are rejected (confirmed by probe)

The IR (`axeyum-ir`) has many operators with **no** core bitblast rule. A probe
(`prove_qf_bv_unsat_alethe` on width-2 queries) confirms the emitter returns `None`
(cannot emit) for them:

- **`bvsub`** — `emit_some=false`
- **`bvule`** — `emit_some=false`
- **`bvnand`** — `emit_some=false`

Also in this gap: `bvnor`, `bvugt`, `bvuge`, `bvsle`, `bvsgt`, `bvsge`, the shifts
(`bvshl`/`bvlshr`/`bvashr`), and division/remainder (`bvudiv`/`bvurem`/`bvsdiv`/
`bvsrem`/`bvsmod`). All exist in the IR `Op` enum and evaluate correctly
(`eval.rs`); only the **proof emission** rejects them.

## Why: no Carcara `bitblast_*` rule, so the proof must reduce to core first

Carcara has no `bitblast_sub`/`bitblast_ule`/… . To certify a derived operator the
proof must **rewrite it to the core 17** via a Carcara-valid step, then bitblast the
core form. Two relevant rule families exist in Carcara:

- **`bv_poly_simp` / `bv_poly_simp_eq`** (→ `polynomial::poly_simp`) — polynomial
  normalization over `add`/`neg`/`mult`/constants. The natural vehicle for
  `bvsub a b → bvadd a (bvneg b)` (and constant folding / `bvneg` distribution).
- **`pbblast_*`** (pseudo-boolean bitblasting) — a **separate** scheme that DOES
  have rules for the comparisons (`pbblast_bvule/bvugt/bvuge/bvsle/bvsge/bvsgt/
  bvult/bvslt/bveq`, plus `bvand`/`bvxor`). It is an alternative to the AIG-style
  `bitblast_*` path; mixing the two schemes in one proof is a design question, so
  treat pbblast as a fallback, not the first move.

## Extension paths, in recommended order

1. **`bvsub` (cheapest, no new scheme).** Reduce `bvsub a b → bvadd a (bvneg b)`.
   Both `add` and `neg` are already covered end-to-end (Carcara + reconstruction).
   Needs: (a) emitter emits a `bv_poly_simp`-style rewrite step proving
   `(bvsub a b) = (bvadd a (bvneg b))`, validated by Carcara; (b) reconstruction
   lifts that rewrite to a Lean equality (denotation-preserving; both sides
   bit-blast identically). Once the rewrite step round-trips, the rest is the
   existing add/neg machinery.

2. **`bvnand`/`bvnor`.** `bvnand a b → bvnot (bvand a b)`, `bvnor → bvnot (bvor …)`.
   Same shape as (1) but the rewrite is a simple boolean definition rather than
   polynomial — check whether Carcara accepts it under a `bv_*` simplify rule or
   only via pbblast.

3. **Unsigned/signed comparisons** `bvule/bvuge/bvugt/bvsle/bvsge/bvsgt`. Boolean
   reductions to the covered `bvult`/`bvslt`:
   - `bvule a b ≡ ¬(bvult b a)`, `bvuge a b ≡ ¬(bvult a b)`, `bvugt a b ≡ bvult b a`
   - signed analogues via `bvslt`.
   The reduction is a Lean-trivial boolean identity on the reconstruction side; the
   open question is the Carcara-valid emission (a rewrite step vs. the `pbblast_*`
   comparison rules). Resolve that before implementing.

4. **Shifts** (`bvshl`/`bvlshr`/`bvashr`) and **division** (`bvudiv`/`bvurem`/…).
   No Carcara core bitblast and no cheap reduction: shifts expand to a barrel
   (mux/concat) network, division to a multiply+remainder constraint. These are the
   **hardest** and should come last (and likely want the shared/`let` encoding from
   [[bitblast-reconstruction-multiplier-blowup]] to stay polynomial).

## Implementation findings (2026-06-18, code-level investigation)

Confirmed against the actual code in all three subsystems:

- **Carcara accepts the `bvsub` bridge.** `bv_poly_simp` (→ `polynomial::poly_simp`)
  checks `(= t s)` when both sides normalize to the same polynomial mod 2^width, and
  `Polynomial::from_term` parses `BvAdd`/`BvNeg`/`BvSub`/`BvMul`
  (`references/carcara/.../rules/polynomial.rs:44-58`). So
  `(= (bvsub a b) (bvadd a (bvneg b)))` is a valid `bv_poly_simp` step — the rewrite
  vehicle is confirmed available, not hypothetical.
- **The emitter rejects derived ops at the RENDERING level**, earlier than the
  bitblast dispatch. `bv_term_to_alethe` → `op_smt_name` maps only the 15 covered
  `Op` variants (`_ => None`), so `bv_term_to_alethe(bvsub …)` returns `None` and the
  whole step fails before `bitblast_op_step`. Supporting `bvsub` therefore needs a
  **driver-level rewrite** (in `qfbv_alethe.rs`, where the formula is walked and steps
  assembled), not just a new `bitblast_op_step` arm.
- **The canonicalizer does NOT do the general expansion.** `axeyum-rewrite`'s
  `canonical.rs` has `rewrite_bv_sub` (only `bvsub-zero` / `bvsub-self` simps) and
  `rewrite_bv_compare` (comparison normalization), but no general
  `bvsub → bvadd a (bvneg b)` / `bvnand → bvnot (bvand …)` lowering. So
  "canonicalize-then-prove" does **not** cover derived ops out of the box.

### Two implementation routes (pick per soundness bar)

1. **Front-end expansion (lighter, trusted transform).** Add a denotation-preserving
   `bvsub → bvadd a (bvneg b)` (and the nand/nor/compare reductions) lowering pass —
   either extend the canonicalizer or a dedicated pre-pass — applied before
   `prove_qf_bv_unsat_alethe`. The Lean certificate then certifies the *expanded*
   formula; soundness for the original rests on the expansion being
   denotation-preserving (test it via the ground evaluator over all small inputs).
   Fastest path to coverage; weaker guarantee (the expansion is not itself
   Lean-checked).
2. **In-proof `bv_poly_simp` bridge (heavier, fully Lean-checked).** The emitter emits
   the `(= (bvsub a b) (bvadd a (bvneg b)))` step (Carcara-valid per above), threads it
   into the bbterm chain via `cong`/`trans`, and reconstruction lifts that equality to
   a kernel-checked Lean equality (both sides share a bit form → `def_eq`). Certifies
   the *original* formula end-to-end. The right destination; more emitter + reconstruct
   surgery.

Recommended: do route 1 first for breadth (cover `bvsub`/`nand`/`nor`/comparisons via a
tested denotation-preserving lowering), then upgrade `bvsub` to route 2 to prove the
fully-checked pattern, then generalize.

## Reconstruction-side note

Every reduction adds a **rewrite/definition step** to the proof; reconstruction must
lift each to a kernel-checked Lean equality. Because the rewrites are
denotation-preserving and both sides share a bit form, the cleanest lift is to prove
the equality at the bit level (the two `@bbterm`s are `def_eq`), reusing the
now-polynomial CNF-intro/bridge machinery
([[bitblast-reconstruction-end-to-end-status]]). No new soundness surface: each step
stays `check_against`-gated.
