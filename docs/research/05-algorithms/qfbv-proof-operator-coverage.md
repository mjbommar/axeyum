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

## Reconstruction-side note

Every reduction adds a **rewrite/definition step** to the proof; reconstruction must
lift each to a kernel-checked Lean equality. Because the rewrites are
denotation-preserving and both sides share a bit form, the cleanest lift is to prove
the equality at the bit level (the two `@bbterm`s are `def_eq`), reusing the
now-polynomial CNF-intro/bridge machinery
([[bitblast-reconstruction-end-to-end-status]]). No new soundness surface: each step
stays `check_against`-gated.
