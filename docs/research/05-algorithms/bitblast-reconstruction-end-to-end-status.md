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

1. **Inconsistent negation spelling (confirmed bug).** The upstream CNF spells a
   negation sometimes as the literal `negated` flag and sometimes as a `(not X)`
   *atom*: a clause held `+((_ @bit_of 0) a)` while another held
   `+(not ((_ @bit_of 0) a))` — logically `a0` and `¬a0`, but `find_pivot` matches
   syntactically and missed them. Fix: `normalize_lit_polarity` peels leading
   `(not …)` atoms into the `negated` flag. Soundness-safe — `+(not X)` and `-X`
   encode to the identical `Not ⟦X⟧` Prop, so clause `proof` types are unchanged.
   Measured effect: the stuck set shrank 5 → 3 clauses. Real, but **not
   sufficient**.
2. **Greedy resolution is non-confluent (the deeper blocker).** After
   normalization the residual 3 clauses are **not jointly unsatisfiable**
   (`a1=⊤` satisfies two, `b1=⊤` the third) — proof that the greedy
   "resolve any complementary pair" loop *already went wrong earlier*, consuming a
   clause some later step needed and leaving an unrefutable remnant. Binary
   resolution is refutation-complete only for *some* order; arbitrary pair-picking
   dead-ends. Alethe's basic `resolution` does **not** list pivots, so the checker
   must reconstruct a valid order. The fix is **structure-following resolution** —
   fold in the proof's intended (premise) order with correct pivot selection, or
   reconstruct via RUP over the premises — not greedy pairing.

So **no genuine QF_BV `unsat` (beyond `x ∧ ¬x`) closes to `False` yet**. Both the
normalization and pool experiments were **reverted** (they get 5 → 3 but don't
close, and have no demonstrating end-to-end test — undemonstrated change to
soundness-critical resolution code is not committed). The confirmed diagnosis is
the deliverable; the fix is a focused next piece.

This is the highest-priority Track-3 fix.

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
