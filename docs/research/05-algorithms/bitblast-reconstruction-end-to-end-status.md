# Bit-blast reconstruction — honest end-to-end status (P3.7)

Status: **measured 2026-06-18.** Corrects the "QF_BV operator set complete"
framing (`58e9062`) with what genuinely reconstructs end-to-end vs. what does not,
found by validating *nested / genuinely-unsat* proofs (not just `eq ∧ ¬eq`).

## What is actually true

**The per-operator bit-blast reconstruction is complete and sound** for the
emitter's operator set — bitwise (`not`/`and`/`or`/`xor`/`xnor`/`=`), structural
(`extract`/`sign_extend`/`concat`), arithmetic (`add`/`neg`/`mult`), comparison
(`ult`/`slt`/`comp`). Each `bitblast_*` *step* reconstructs to a kernel-checked
Prop, with negative tests confirming the kernel gate rejects wrong bits.

**But end-to-end closure to `False` was only validated on TRIVIAL refutations** —
`(= t u) ∧ ¬(= t u)` and `pred ∧ ¬pred`, whose resolution structure is a single
trivial step. Two limitations surface the moment the refutation is non-trivial:

### 1. Resolution layer is incomplete (the blocking gap)

`(bvult a b) ∧ (bvult b a)` — unsat by antisymmetry, a *genuine* multi-clause
refutation — fails reconstruction with:

```
UnsupportedResolution: no remaining premise resolves with the accumulator
                       `(cl (not (@bit_of 0 a)) (@bit_of 1 b))`
```

The bit-blasting all reconstructs; the failure is in `reconstruct_resolution_step`,
which follows a **linear greedy accumulator** (resolve the running clause with the
next premise that shares a pivot). Real refutations have a resolution **DAG** the
linear walk can't follow. So **no genuine QF_BV `unsat` (beyond `x ∧ ¬x`) closes
to `False` yet** — the operators are ready, the proof *combinator* is not.

This is the highest-priority Track-3 fix: a general resolution reconstruction that
follows the Alethe step's premise structure (pivots/DAG), not a linear scan.

### 2. Reconstruction is slow even at tiny widths

`(bvadd (bvmul a b) (bvneg c)) = a ∧ ¬…` and `(concat (bvadd a b) c) = d ∧ ¬…` at
**3-bit** each reconstruct correctly but take **~60 s** (the suite with them ran
376 s). 3-bit is tiny — this points to the kernel `infer`/`def_eq` (and/or
`gate_term_to_prop`) doing non-shared, super-linear work over the accumulated proof
terms. Combined with the multiplier blowup
([[bitblast-reconstruction-multiplier-blowup]]), the through-line is the same:
**no sharing** — terms and Props are inlined trees, and kernel operations over them
are not memoized.

## Honest milestone correction

- ✅ Per-operator `bitblast_*` reconstruction: complete + sound (small widths).
- ⚠️ End-to-end `False`: only trivial `x ∧ ¬x` refutations; **genuine refutations
  blocked on the resolution layer**.
- ⚠️ Performance: impractical even at 3-bit; needs sharing/memoization.

The committed unit + end-to-end tests (trivial refutations, width ≤ 2) are green
and fast and remain valid — they just don't exercise these two axes. No
slow/failing tests were committed (the validation tests that revealed this were
removed).

## Next steps, in priority order

1. **General resolution reconstruction** — follow the Alethe `resolution`/
   `th_resolution` premise+pivot structure as a DAG, so genuine QF_BV (and EUF/LRA)
   refutations close to `False`. This unblocks *real* end-to-end QF_BV certificates.
2. **Sharing/memoization** — hash-cons `gate_term_to_prop` results and ensure the
   kernel shares `Expr`s, so `def_eq`/`infer` are polynomial; pairs with the
   shared/`let` multiplier encoding for width.
3. Then re-validate nested + genuine-unsat proofs end-to-end and add them as
   (fast) regression tests.
