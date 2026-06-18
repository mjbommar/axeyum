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
2. **Commutative `=` arg-order spelled both ways — FIXED (`6f0fd2c`).** The
   bit-equality gate appeared as both `(= a1 b1)` and `(= b1 a1)` (from
   `(bvult a b)`'s ladder vs `(bvult b a)`'s); these are **distinct kernel Props**
   (`Iff a b ≠ Iff b a`), so `¬(= b1 a1)` couldn't resolve against `+(= a1 b1)`.
   Not normalizable on the reconstruction side (would change `clause_to_prop`), so
   the fix is **emitter-side**: `eq2_canon` orders the operands by key in the
   ult/slt ladders and `bitwise_equal_and`. Proofs stay check_alethe-valid.
   Effect: antisymmetry stuck set 3 → 2.
3. **Resolution order / non-confluence — the LAST blocker (open).** With (1) and
   (2) fixed, antisymmetry stalls on two clauses that are **not jointly
   unsatisfiable** (`C0 = ¬G2 ∨ ¬b0`, `C1 = ¬G1 ∨ a1`): an earlier resolution
   consumed a clause a later step needed. **Both** strategies tried are
   non-confluent — acc-centered greedy *and* pairwise pool dead-end this way; and a
   strict premise-order left fold **regressed** `real_emitter_unsat_cnf` (so it is
   not a clean chain either). Binary resolution reconstruction from an unordered
   premise set with implicit pivots is genuinely order-sensitive.
   **Principled fix — mirror Carcara's `greedy_resolution`** (read from
   `references/carcara/carcara/src/resolution.rs`). Its algorithm is *not*
   sequential binary resolution; it is **conclusion-guided and set-based**:
   - Normalize each literal to `(negation_count, inner_term)` via
     `remove_all_negations` (peel *all* leading `not`s; complementarity is a
     parity difference of 1 on the same inner term — a superset of our
     `normalize_lit_polarity`).
   - Pre-collect the **conclusion** literals. Then sweep every premise literal:
     if it is in the conclusion, put it in the `working_clause`; otherwise it is a
     **pivot** that must be eliminated against its complement.
   - **"Only one pivot eliminated per clause"** — at most one pivot per premise;
     this is the soundness guard that makes the check confluent (it rejects the
     `equiv_neg1`+`equiv_neg2` unsound example).
   - At the end every pivot must be eliminated (special cases: a leftover
     `false` for an empty conclusion; a single term with even extra negations).
   For **reconstruction** (we need the Lean proof term, not just a yes/no) the
   plan is: run Carcara's sweep to obtain the pivots + their pairing (the
   `pivot_trace`), then build the binary-resolution proof term in *that* order via
   the existing `binary_resolve`. This replaces both the greedy accumulator and
   the pool, and is exactly the derivation Carcara/the emitter accept — so it
   closes the bvult-antisymmetry closing step (empty conclusion ⇒ all literals are
   pivots that pairwise cancel) without dead-ending.

So **no genuine QF_BV `unsat` (beyond `x ∧ ¬x`) closes to `False` yet**, but two of
the three blockers are **fixed and shipped** (negation `356f3e3`, `=` canon
`6f0fd2c`) and the last is isolated with a principled direction (mirror Carcara's
resolution checker). Land it with the bvult-antisymmetry case as the end-to-end
test — at which point genuine QF_BV refutations close to kernel-checked `False`.

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
