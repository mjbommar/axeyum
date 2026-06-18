# Bit-blast reconstruction — the multiplier term blowup (P3.7)

Status: **measured finding + guard landed (2026-06-18).** Records why wide
`bvmul` Alethe→Lean reconstruction is intractable with the current inlined
encoding, the guard that prevents OOM, and the durable fix (shared/`let`
encoding).

## What happened

A validation probe reconstructing an **8-bit `bvmul`** proof end-to-end OOM'd the
process. The committed reconstruction tests use width 2 and are unaffected; the
blowup only shows at larger widths.

## Root cause: the inlined multiplier term is exponential in width

`reconstruct.rs::mult_bit_term` (and the emitter's
`bitblast_alethe.rs::shift_add_multiplier_bits`) build the shift-add multiplier
result bit as an **un-shared `AletheTerm` tree**. The carry recurrence

```
carry[j][k] = (or (and  res[j-1][k-1] shift[j][k-1])
                  (and (xor res[j-1][k-1] shift[j][k-1]) carry[j][k-1]))
```

embeds `res[j-1][k-1]` **twice** (once in the first `and`, once inside the
`xor`), so each round roughly multiplies the node count. Measured node count of
the top result bit (via the recurrence, no allocation):

| width | top-bit nodes | width | top-bit nodes |
|---|---|---|---|
| 4 | 113 | 9 | 198 979 |
| 5 | 451 | 10 | 981 785 |
| 6 | 1 937 | 11 | 4 926 559 |
| 7 | 8 767 | 12 | 25 062 625 |
| 8 | **41 193** | | |

Building that tree, lowering it to a kernel `Expr`, and `def_eq`-checking the
reflexive iff over it exhausts memory at width 8 and is hopeless at 32/64-bit
(real QF_BV). **Only the multiplier is affected** — the ripple-carry adder/`bvneg`
embed `carry[i-1]` once, so they are `O(width^2)` (a 64-bit adder bit is ~4 k
nodes, fine).

## The guard (landed: `5953b7d`)

The `bvmul` `bv_bit` branch computes `mult_bit_node_count(i)` (the recurrence
above, no allocation) and, if it exceeds `MULT_BIT_NODE_BUDGET = 20_000`
(~7-bit), returns a clean `ReconstructError::UnsupportedTerm` instead of OOMing.
Reconstruction processes the top bit first, so a wide multiplier is rejected
before any large term is built. Tested: 8-bit `bvmul` → guarded; width-2 still
reconstructs.

This makes the failure **sound and bounded** (a clean "unsupported", never a
crash) but leaves wide-multiplier proofs **unreconstructed** — an honest
correction to the "QF_BV operator set complete" milestone (`58e9062`): the
operator set is covered, but the multiplier only at small widths.

## The durable fix: a shared / `let` encoding

The exponential blowup is purely a *representation* problem — the multiplier
circuit is polynomial-size as a **DAG** (each `res[j][k]`/`carry[j][k]` gate is
one node, `O(width^2)` gates). Inlining it to a tree is what explodes it. The fix,
in order of preference:

1. **Reconstruction-side sharing.** Memoize gate→`ExprId` so identical
   sub-circuits map to one kernel `Expr` (a DAG). This needs the *gadget* side
   (the emitter's `@bbterm`) to also be shared, otherwise the `AletheTerm` itself
   is already exponentially large in memory before reconstruction sees it.
2. **Emitter-side sharing (the real fix).** Emit the multiplier (and any
   carry-chain) with **auxiliary Tseitin definitions** — a fresh proof
   variable/step per `res[j][k]`/`carry[j][k]` gate, referenced rather than
   inlined — exactly how a CNF Tseitin encoding avoids the blowup. The Alethe
   proof becomes `O(width^2)` and Carcara-checkable; reconstruction then walks the
   shared definitions. This is an ADR-level change to `bitblast_alethe.rs` +
   `reconstruct.rs` and is the prerequisite for certifying real-width multiplier
   proofs.

Until (2) lands, multiplier proofs are reconstructable only at small widths
(`≤ ~7-bit`), which is sufficient for the unit/integration coverage but not for
production QF_BV. Adder/`neg`/bitwise/structural/comparison ops are unaffected and
reconstruct at any width the SAT layer can handle.

## Concrete fix mechanism (2026-06-18, Carcara-grounded)

Reading Carcara's actual rules pins the exact fix — it is **not** an exotic `let`
encoding, it is Carcara's own incremental scheme that our emitter bypasses:

- Carcara's `bitblast::add` (and `mult`, …) computes the expected `res` via
  `ripple_carry_adder(arg_i, …)`, which calls **`build_term_vec(arg, size, pool)`**.
  That helper returns the operand's bits as **`((_ @bit_of i) arg)` projections** when
  `arg` is a *plain term*, and only inlines when `arg` is itself a literal `@bbterm`
  (`references/carcara/.../rules/bitvectors.rs`). So `(= (bvadd (bvadd a b) c) res)`
  with `res` built over `@bit_of i (bvadd a b)` is **`O(size²)`** and Carcara-valid.
- **Our emitter inlines.** `BbReducer::reduce_term` (`qfbv_alethe.rs:497–528`) reduces
  each child to its `@bbterm` **form** (`child_forms`), `cong`-substitutes the op to
  `op(child_forms…)`, and calls `bitblast_op_step` over those `@bbterm` forms — so our
  `build_term_vec` takes the inlined-args branch and the bit expressions embed the
  children's full bit trees → exponential for nested arithmetic.

**The fix (both sides):**
1. *Emitter:* bitblast each compound op **directly on its original term**
   (`= op(orig children) (@bbterm projections)`), dropping the `cong`+`@bbterm`-form
   substitution — operands stay as terms so `build_term_vec` projects. Validate with
   `carcara_crosscheck`.
2. *Reconstruction:* resolve `@bit_of i child` for a **compound** `child` via that
   child's own `@bbterm` definition (today `operand_bit_term` only projects leaves /
   inlines `@bbterm` args), so the per-bit iffs stay small. The bridge / `bv_widths`
   already track the needed child definitions.

This is the prerequisite for wide `bvmul`/`bvudiv`/… and removes both the emission
*and* reconstruction blowup (the kernel `check_against` over large Props goes away
because the Props become `O(size)` per bit). ADR-level, Carcara-sensitive — a focused
fresh-session change, but now precisely specified rather than "share it somehow".

## Landed: projection encoding for compound operands (2026-06-18)

The projection encoding above is **implemented** in `qfbv_alethe.rs` (`BbReducer`),
`bitblast_alethe.rs`, and `reconstruct.rs`, and is **Carcara-validated** (all 46
`carcara_crosscheck` tests pass, including the compound/nested/arithmetic drivers).

- **Emitter.** `BbReducer::reduce_term`/`reduce_predicate` now bit-blast each compound
  op **directly on its original child terms**, so `build_term_vec` projects
  `((_ @bit_of i) child)` — the conclusion is `(= op(orig children) (@bbterm
  projections))`, `O(size²)`, no `cong`/`trans`/`@bbterm`-form substitution.
- **The cross-term connection.** Projecting `((_ @bit_of i) t)` makes it an *opaque*
  SAT atom, breaking the link to a compound operand's bits. We restore it with a
  per-compound **bit-definition**: `bitblast_equal` over the proven `(= t (@bbterm
  g…))` yields `B_t = (and (= ((_ @bit_of i) t) g_i) …)` — a Carcara-valid step —
  then `equiv1` + `resolution` derive the unit `(cl B_t)`, fed into the refutation.
  (There is **no** Carcara rule to project a bit out of an `@bbterm`, so this
  `bitblast_equal` bridge is the only Carcara-valid way to tie the projection to its
  gadget; confirmed by exhaustively testing `evaluate`/`cong`/`refl`/… against the
  binary.)
- **Reconstruction.** `gate_term_to_prop` resolves `((_ @bit_of i) compound)` (and a
  `#b…` literal) through the faithful bit model `bv_bit`, so the projection agrees
  structurally with the LHS; `bv_bit`/`alethe_bv_width` gained `concat`/`sign_extend`/
  `bvcomp` cases for nested operands; the bit-definition `(cl B_t)` reconstructs as a
  reflexive `And`-fold of `Iff.refl`s (`try_reconstruct_bit_definition`).

**Effect (measured).** *Nested* multiply `((a·b)·c)` now reconstructs to a
kernel-checked `False` at **width 6** (≈115 s) and emits to width 8, vs the old
inlined blowup at ~width 3–4. A committed regression test exercises width 4
(`end_to_end_nested_mul_projection_reconstructs`).

**Still open — the single-multiplier term.** A *single* wide `bvmul` over leaf
operands is unchanged: its gadget is one `bitblast_mult` step whose result bit `i`
is still an inlined ~4.5×/bit tree, so reconstruction's `mult_bit_term` hits
`MULT_BIT_NODE_BUDGET` at ~width 7 (the guard still fires; raising it, width-8
reconstruction exceeds 150 s). Likewise deep `bvudiv` lowering (nested multipliers)
reconstructs only at width 2 in practical time. Closing these needs the
**reconstruction-side sharing** of the multiplier DAG (item 1 above) — a separate
follow-up; the projection encoding is the prerequisite, now landed.
