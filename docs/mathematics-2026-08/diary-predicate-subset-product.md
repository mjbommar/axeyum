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
