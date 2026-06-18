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

The bit-blasting all reconstructs; the failure is in `reconstruct_resolution_step`.
Instrumented probing (2-bit, fast — dumping the stuck clauses' `(±atom-key)`
literals) **confirmed** the root cause and **disproved an earlier guess** (it is
*not* the predicate↔B bridge). Two real issues:

1. **Inconsistent negation spelling — FIXED (`356f3e3`).** The upstream CNF
   spelled a negation sometimes as the literal `negated` flag and sometimes as a
   `(not X)` *atom*: a clause held `+((_ @bit_of 0) a)` while another held
   `+(not ((_ @bit_of 0) a))` — logically `a0` and `¬a0`, which `find_pivot`
   (syntactic) missed. `normalize_lit_polarity` peels leading `(not …)` atoms into
   the flag; applied to every clause entering resolution. Soundness-safe (`+(not
   X)` and `-X` are the same `Not ⟦X⟧` Prop, so clause `proof` types are
   unchanged); all existing tests green + a unit test. Effect: the antisymmetry
   stuck set shrank 5 → 3 — real progress, but **not the whole fix**.
2. **Commutative `=` arg-order spelled both ways (the next blocker).** With
   negation normalized, the antisymmetry fold stalls at `acc = (cl ¬G2 a1)` where
   `G2 = (and (= b1 a1) (and (¬b0) a0))`. The bit-equality gate appears as both
   `(= a1 b1)` and `(= b1 a1)` across the proof; these are **distinct kernel Props**
   (`Iff a b ≠ Iff b a` definitionally), so a `¬(= b1 a1)` literal cannot resolve
   against a `+(= a1 b1)` one. Unlike negation, this is **not** freely normalizable
   on the reconstruction side (it would change `clause_to_prop` and break the proof
   term); the clean fix is **emitter-side**: spell every bit-equality with a
   canonical operand order in `bitblast_alethe.rs`. (Or carry an `Iff`-symmetry
   lemma in reconstruction — more invasive.)
3. **Resolution order / greedy non-confluence (possible, still open).** The
   acc-centered greedy fold may also need to follow the proof's premise order
   rather than picking the first resolvable premise. Strict premise-order fold was
   tried and **regressed** `real_emitter_unsat_cnf_reconstructs`, so the order
   handling is subtler than a pure left fold — to be settled after (2), since (2)
   currently masks whether order alone suffices.

So **no genuine QF_BV `unsat` (beyond `x ∧ ¬x`) closes to `False` yet**, but the
path is now concrete: negation done; next the emitter-side `=` canonicalization,
then re-check whether resolution order needs work. This is the highest-priority
Track-3 fix; land each with the bvult-antisymmetry case as the end-to-end test.

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

1. **General resolution reconstruction** — both parts together: (a)
   `normalize_lit_polarity` (peel `(not …)` atoms into the flag — a confirmed,
   self-contained bug fix; could land on its own with a `find_pivot` unit test),
   and (b) **structure-following resolution** (fold in the proof's premise order
   with correct pivots, or RUP-reconstruct) to replace the non-confluent greedy
   pairing. Together these close genuine QF_BV (and EUF/LRA) refutations to
   `False`. Single highest-leverage Track-3 fix; land it with the
   bvult-antisymmetry case as the demonstrating end-to-end test.
2. **Sharing/memoization** — hash-cons `gate_term_to_prop` results and ensure the
   kernel shares `Expr`s, so `def_eq`/`infer` are polynomial; pairs with the
   shared/`let` multiplier encoding for width.
3. Then re-validate nested + genuine-unsat proofs end-to-end and add them as
   (fast) regression tests.
