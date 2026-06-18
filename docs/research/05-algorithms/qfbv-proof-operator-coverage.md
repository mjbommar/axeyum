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

`axeyum_rewrite::lower_derived_bv` (`40e679b`, extended) implements the front-end
denotation-preserving lowering for the derived operators that reduce cleanly to core:
- arithmetic/logical: `bvsub`, `bvnand`, `bvnor`;
- comparisons: `bvugt`/`bvule`/`bvuge`/`bvsgt`/`bvsle`/`bvsge` → `bvult`/`bvslt` forms;
- structural: `zero_extend → concat (0:k) x`, `rotate_left`/`rotate_right` →
  `concat` of two `extract`s.

Each rule is exhaustively checked denotation-preserving over all small inputs, and
`bvsub`/`bvule`/`rotate_left` queries reconstruct end-to-end to a kernel-checked
`False` (`axeyum-solver` tests).

**Const-`concat` reconstruction bug — FIXED.** `zero_extend` lowers to
`concat (bvconst 0:k) x`; reconstruction of `bitblast_concat` had used an opaque
`@bit_of` projection for a **constant** operand's bits, while the emitter bit-blasts
the constant to Boolean literals in the `@bbterm` — a `TypeMismatch` (atom vs
`False`). Fixed in two places: `operand_bit_term` now returns the constant's actual
bit value (`true`/`false`) for a `#b…` literal, and `gate_term_to_prop` maps the
Boolean literals to the prelude `True`/`False` (so an embedded const bit renders
identically in arithmetic gadgets too). `zero_extend` and `rotate` now both
reconstruct end-to-end (`axeyum-solver` tests).

**Constant-amount shifts LANDED.** `bvshl`/`bvlshr`/`bvashr` by a **constant** amount
reduce to core: `shl k → concat x[w-1-k:0] (0:k)`, `lshr k → concat (0:k) x[w-1:k]`,
`ashr k → sign_extend x[w-1:k] by k` (with the SMT-LIB `k ≥ w` / `k = 0` edge cases).
Exhaustively denotation-checked (amounts `0..=w` and `> w`); a `bvshl a 1` query
reconstructs end-to-end.

**Variable-amount shifts LANDED (barrel shifter).** `lower_var_shift` expresses a
non-constant `bvshl`/`bvlshr`/`bvashr` as a barrel network: stage `i` (`2^i < w`)
applies the constant shift by `2^i` selected by bit `i` of `s` (splatted via
`sign_extend` of a 1-bit slice), through an `and`/`or`/`not` mux; the high bits of
`s` (`≥ ⌈log₂ w⌉`) drive an overflow mux to the SMT-LIB `s ≥ w` result (`0`, or
all-sign for `bvashr`). Exhaustively denotation-checked over **all** `(x, s)` pairs
for widths 2/3/4 (every overflow corner), and a variable `bvshl a s` query
reconstructs end-to-end to a kernel-checked `False`.

**Unsigned division LOWERED (end-to-end blocked).** `lower_derived_bv` now reduces
`bvudiv`/`bvurem` to core via one unrolled long-division (shift-subtract) pass —
`divide` — exhaustively denotation-checked over **all** `(x, y)` for widths 2/3/4,
including `y = 0` (SMT-LIB totality `udiv = all-ones`, `urem = x` falls out for free).
The lowering is sound and usable, and **`bvudiv`/`bvurem` now reconstruct end-to-end
at width 2** (committed test). Two notes:
1. **`cnf_intro` over Boolean constants — FIXED.** The divider's adders over the
   zero-const bits produce `xor`/`equiv` Tseitin clauses whose operands are the
   literals `false`/`(not false)`; the truth-table case-split had treated them as
   free atoms and explored the impossible `(not false) = false` world, raising a
   spurious `MalformedStep`. Fix: `collect_atoms` and `try_equiv_xor` skip the
   Boolean literals (they are fixed values, not free atoms), and `prove_term_true`/
   `_false` discharge them (`True.intro` / `id : False → False`). General reconstruction
   robustness, not div-specific.
2. **Term blowup (still open).** The unrolled divider is a large term; reconstruction
   is intractable beyond tiny widths (width 3 already exceeds an 8 GB / 120 s bound) —
   the same representation problem as the multiplier
   ([[bitblast-reconstruction-multiplier-blowup]]), wanting the shared/`let` encoding.
   That is why the committed div test is pinned at width 2.

**Signed division family LOWERED.** `bvsdiv`/`bvsrem`/`bvsmod` reduce to the unsigned
`divide` of the operand magnitudes plus sign adjustments (the SMT-LIB definitions,
incl. `bvsmod`'s 5-way rule), exhaustively denotation-checked over all `(x, y)` for
widths 2/3/4 (sign quadrants, `y = 0`, `INT_MIN`). With this, **the entire `QF_BV`
operator set now lowers to the 17-op core** — every derived operator is covered by a
tested denotation-preserving lowering. End-to-end *reconstruction* works for all
except the multiply/divide family at non-tiny widths (the term-blowup below).

**Remaining:** the multiply/divide **term-blowup** (the shared/`let` encoding — the
one representation fix that makes wide `bvmul`/`bvudiv`/… reconstructible), and the
route-2 `bv_poly_simp` upgrade (certify the *un-lowered* original). The rest of this
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
