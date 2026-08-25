# Seven theorems, one missing primitive

**2026-08-25.** Seven lanes working on unrelated targets have stopped at the
same absence. Writing it down because no single lane could see the pattern, and
because the seventh report finally made the mechanism precise enough to build.

## The absence

There is **no product over a predicate-defined subset of `[0,n)`**, and no
lemma that permuting such a subset leaves the product unchanged.

The asymmetry is what makes this actionable. `Nat.countRange` **does** fold over
a Boolean-predicate subset of `[0,n)` — that is how `Nat.totient` is defined.
`Nat.prodRange` exists but only over a **contiguous** range. So the counting
side of the pattern is built and the product side is not; this is a gap in an
existing design, not a new one.

`permutation.rs` and `restrict_pair.rs` do not cover it either: measured by the
Euler lane, they handle a fixed two-element complement, or bijections already
known on **all** of `[0,n)` — never a bijection of a subset carved out by a
predicate.

## What it blocks

1. **Euler's totient theorem.** The proof multiplies the residues coprime to
   `n`; multiplication by a coprime `a` permutes that subset. Both halves need
   the primitive. (`totient.rs`'s own module doc says so, written by an earlier
   lane, and the Euler lane re-derived it independently.)
2. **Uniqueness of prime factorization.** Needs multiset equality.
3. **General-`n` Chinese Remainder Theorem.** Needs a list of moduli.
4. **Permutations as group elements.** The symmetric group needs an unbounded
   `Eq (Nat → Nat)`.
5. **Lagrange's identity at general `n`.**
6. **`det2` generalized past four scalar arguments.**
7. The `O(log e)` cost claim for exponentiation by squaring — this one needs a
   **product type** to thread a step counter, which is a *different* absence.

Items 2–4 and 7 are really about missing **carriers** (multiset, list, product
type). Items 1, 5, 6 are about the missing **fold**. Keeping those apart matters:
the fold is buildable today on the `countRange` pattern, the carriers are not.

## What the seventh report added

Earlier instances read as "this kernel has no `Finset`, so the theorem is
unstatable" — true but not actionable. The Euler lane made it specific: the
needed object is `prodRangeIf n p f` plus **invariance under a `p`-preserving
bijection of `[0,n)`**. That is a concrete declaration with a concrete proof
obligation, and it does not require a finite-set carrier — only the fold and an
induction with a remove-one-element re-indexing step.

Whether that re-indexing step is expressible is the open question. If it is not,
the answer is that the real missing thing is a finite carrier after all, and
that would be worth knowing sharply.

## A correction to how this was briefed

I told the Euler lane that `fermat.rs` structures Fermat's little theorem with a
permutation argument and that reading it was the most important preparation.
**That is false.** `fermat.rs` proves it by the Frobenius / "freshman's dream"
identity `(a+b)^p ≡ a^p + b^p [p]`, from the binomial theorem plus
`prime_dvd_choose`. There is no permutation step in it, and the route is
prime-specific — it does not generalize to composite `n` at all.

The lane checked rather than following me, and said so. That is the second time
today a brief of mine asserted something about the codebase that a lane
correctly refuted; the first was telling a lane that
`1 ≤ n → n = succ (pred n)` was spelled with `Nat.le 1 n` when every existing
copy uses `Nat.lt zero n`. Briefs should name the file to read and the question
to answer, not the answer.

---

## Correction, same day: the primitive is PORTABLE, not missing

The lane sent to build this came back with a finding that materially changes the
note above, and in the good direction.

**The fold landed.** `Nat.prodRangeIf p f n` now exists, defined by delegation to
the already-declared `Nat.prodRange` — the same device `Nat.totient` uses over
`Nat.countRange` — so both defining equations close by pure `Eq.refl`. With
`prodRangeIf_zero`, `prodRangeIf_succ`, and a bounded congruence
`prodRangeIf_congr_lt`. `countRange`'s convention, for the record, is that the
predicate is **`Nat → Bool`, never `Prop`**, selected through
`NatOps::bool_select_nat`; the product version matches it, or the two would not
compose in Euler's proof.

**The permutation invariance is not missing from the kernel — it is missing from
`Nat`.** `int_prelude/prod.rs` (3,214 lines) already declares
`Int.prodRange_permute`, `Int.prodRange_swap`, `Int.prodRange_swap_adjacent`,
`Int.prodRange_congr_lt` and `Int.modEq_prodRange`. So a working, kernel-checked
existence proof of exactly this machinery has been in the tree the whole time,
over a different carrier.

**And it is already consuming it for the neighbouring theorem.**
`int_prelude/wilson.rs` (5,884 lines) proves Wilson's theorem — *the product of
all units mod p* — by permuting that product with the modular-inverse
involution, supported by `Nat.inverseIndex_injective`, `_involutive`,
`_maps_into`, `_fixed_point` and `_interior_fixed_point_free`. Euler's totient
theorem is the same shape: a product over units, permuted by multiplication by a
coprime `a`.

So the conclusion inverts. Euler's theorem is **not** blocked on a missing
carrier and does **not** require porting 650+ lines of swap machinery to `Nat`
first. It should be attempted **over ℤ, following Wilson's route**, where every
piece it needs is already built and load-bearing.

### The precise obstruction, for whoever does port it to `Nat`

Worth keeping, because it is sharper than "no `Finset`". Invariance reduces
cleanly to a predicate-free statement: with `h i := bool_select_nat (p i) (f i) 1`,
`p`-preservation makes the composed selector equal `h ∘ σ` pointwise, so
everything turns on `prodRange (h ∘ σ) n = prodRange h n`.

The "remove one element and re-index" step — which this note guessed would be
the hard part — **is already built**: `Nat.restrict_injective`,
`Nat.restrict_maps_into`, `Nat.injective_on_imp_surjective_on` (pigeonhole), and
`finite.rs`'s `point_override`/`select_nat_true`/`restrict_off`/`override_eq_at`.
The real gap is elsewhere: the pigeonhole witness `i0` with `σ i0 = n` **need not
be `n`**, so `prodRange`'s `succ` equation peels the top of the fold while the
value that must move there sits at an arbitrary interior position. Closing that
needs a swap-two-arbitrary-positions lemma — which is what `Int.prodRange_swap`
is, and whose own doc records that it took three drafts.

### The general lesson

This note asserted a primitive was absent after seven lanes each reported it
absent from where they were standing. Seven concurring reports are not a
measurement: every one of them was looking at `nat_prelude/`, and none had
reason to look at `int_prelude/prod.rs`. **Before recording an absence, query
every carrier by the bare operation name** (`prodrange`, `permute`, `swap`), not
by the namespace you expect. This is the same failure that produced four
duplicate lanes today, one carrier away.
