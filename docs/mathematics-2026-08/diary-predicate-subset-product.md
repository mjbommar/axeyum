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

---

## Correction to the correction: the ℤ machinery is FULL-RANGE, and does not solve this

The correction above is **wrong on the point that matters**, and the lane it
redirected is the one that found out. Recording it rather than editing it away,
because the way I got it wrong is the more useful artifact.

`Int.prodRange_permute`'s actual statement, read from source rather than
inferred from its name:

```text
∀ f σ n, InjectiveOn σ n → MapsInto σ n →
  Eq Int (prodRange f n) (prodRange (fun k => f (σ k)) n)
```

`MapsInto σ n` makes `σ` a self-map of **the whole `{0,…,n−1}`**. It is the
permutation lemma for a *contiguous range*, not for a predicate-defined subset.
Likewise `Nat.injective_on_imp_surjective_on` — the pigeonhole — is stated for
full-range self-maps only.

**So the predicate-scoped versions genuinely do not exist, over any carrier.**
The original seven-lane finding stands. What landed today is the *fold*
(`Nat.prodRangeIf`); what is still missing is invariance of that fold under a
bijection of the subset it selects, plus a predicate-scoped pigeonhole.

### Why Wilson did not need it, which is the whole subtlety

Wilson's theorem is about a **prime** modulus, and every residue in `[1, p−1]` is
then a unit. The "subset of units" *is* the contiguous range, so full-range
machinery suffices — and `wilson.rs` does not even use `prodRange_permute` for
its main step: it uses a fixed-point-free **involution collapse**
(`Int.prod_range_pairing_collapse`), which is sound precisely because no residue
is skipped.

Euler's theorem is about a **composite** modulus, where the units are a proper,
predicate-carved subset. That is the entire difference between the two theorems
from this kernel's point of view, and it is invisible from the outside: they look
like the same argument, and one of them is one lemma away while the other is not.

### How I got it wrong

I matched on a **name**. `Int.prodRange_permute` is what the missing thing would
be called, and it exists, so I recorded the primitive as portable and redirected
a lane on that basis. I never read its hypotheses.

This is the same failure that produced four duplicate lanes today, and I had
already written the rule for it twice — *use names to generate candidates,
decide by statement.* The ledger-audit lane applied it correctly and refuted 14
of 16 name-level matches. I did not apply it to my own conclusion.

Note also that this correction cost less than it could have: the lane was told
to report "precisely what blocked you if anything did", it did, and the redirect
still produced two real theorems (`Int.euler_unit_coprime`,
`Int.euler_unit_injective` — the MapsInto and InjectiveOn halves for
multiplication by a unit) that any future route needs. A wrong brief with a
correct escape hatch is recoverable; a wrong brief that demands success is not.

---

## Third correction: half the obstruction was AVOIDABLE, not solvable

The predicate-scoped **pigeonhole** landed, and it needed none of the machinery
this note spent three revisions arguing about.

`Nat.injective_on_p_imp_surjective_on_p` — with `Nat.injectiveOnP`,
`Nat.mapsIntoP`, `Nat.surjectiveOnP` — is proved by **extending the map instead
of restricting the range**:

```text
f' i := bool_select_nat (p i) (f i) i        -- fix every point outside the subset
```

`f'` is injective and self-maps `[0,n)` outright: an in-subset point can never
collide with a fixed outside point, because `MapsIntoP` keeps every image inside
the subset. So `f'` goes **unmodified** into the existing full-range
`Nat.injective_on_imp_surjective_on`, and reading a genuine witness back out
needs ruling out exactly one spurious case — the witness landing on an outside
fixed point, impossible since the target is itself `p`-true.

**No induction on `n`, no remove-one-element re-indexing, no swap lemma.**

### What that says about the three previous revisions

This note recorded, in order: the primitive is missing (seven lanes); it exists
one carrier away (wrong — a name match with the hypotheses unread); it genuinely
does not exist, full-range only (correct). All three took for granted that the
reduction had to go *inward* — restrict the range to the subset and re-index.
Extending outward to a total map was never considered, by any of the seven lanes
or by me, and it makes the hard part disappear.

The lesson is not "we missed a trick". It is that **an obstruction reported
independently by seven lanes still only tells you where seven lanes stopped, not
that the path is blocked.** Concurring reports raise confidence in the
*symptom* and say nothing about the *diagnosis* — every one of those lanes was
standing in the same place looking the same direction, which is exactly the
condition under which agreement carries no information.

### What is still genuinely missing

`Nat.prodRangeIf_permute` — invariance of the **product** under a subset
bijection. The extension trick does not rescue it: `f'` fixes outside points, so
`prodRangeIf` over `f ∘ σ` and over `f` still differ in how the fold visits
them, and a fold's `succ` step peels the *top* of the range while the pigeonhole
witness can be interior. That is what `Int.prodRange_swap` exists for, and its
own doc records that it took three drafts. Euler's totient theorem still needs
it.

So the score is: pigeonhole **done, cheaply**; product invariance **open, and
the ~650-line swap port is still the honest estimate.**

---

## Fourth correction: the conjecture is HALF right — the reduction is free, the
## floor under it was undercounted

A conjecture came in that the pigeonhole's extension trick — fix every point
outside the subset, hand the result unmodified to the full-range lemma — also
rescues `Nat.prodRangeIf_permute`, contradicting the "does not rescue it" claim
two sections up. Checked against the actual code and the actual statements,
not against the name.

**The reduction half is correct, and the third correction's "does not rescue
it" was reasoning about the wrong construction.** That section tried extending
`prodRangeIf` itself and hit the interior-swap problem again. The conjecture
instead extends **the selector**, using exactly `extend_id` (already declared
in `subset_product.rs`, built for the pigeonhole): with `h i := bool_select_nat
(p i) (f i) 1` and `σ' i := bool_select_nat (p i) (σ i) i`, checking both
branches of `p i` shows `h ∘ σ' = ` the selector for `f ∘ σ`, **pointwise, with
no induction**:

- `p i` true: `σ' i = σ i`, so `h(σ' i) = bool_select_nat(p(σ i))(f(σ i)) 1 =
  f(σ i)` (using `p`-preservation), which is exactly the selector for `f∘σ` at
  `i`.
- `p i` false: `σ' i = i`, so `h(σ' i) = h i = 1` — **both sides are the
  multiplicative identity**, which is the conjecture's own observation and is
  exactly right.

`σ'` is a full injective self-map of `[0,n)` by the same argument the
pigeonhole already uses. So `prodRangeIf p (f∘σ) n` unfolds to `prodRange (h∘σ')
n`, and the ENTIRE remaining proof obligation — with zero predicate-specific
induction — is `Nat.prodRange (h∘σ') n = Nat.prodRange h n` for a full-range
injective self-map `σ'`. That is `Nat.prodRange_permute`, verbatim, applied to
`h`, not to `f`. `Nat.prodRangeIf_permute` is therefore LITERALLY a corollary
of `Nat.prodRange_permute` plus `extend_id` plus a `bool_case` split — the same
device already sitting in this file, not a new one.

**The floor under it is real, is `Nat`-only, and is bigger than "~650 lines,"
not smaller.** Verified by inventory, not by name:

```
cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory -- --include-constructed
  -> positive control Nat.gcd: 48 matches
  -> awk -F'\t' over column 2, grep -iE 'prodrange|permute|swap':
     Nat has only prodRange_zero, prodRange_succ, prodRangeIf_{zero,succ,congr_lt}.
     Every *permute*/*swap* row is `Int.*` (prodRange_permute, prodRange_swap,
     prodRange_swap_adjacent) or unrelated (sumRange_swap, det2_swap_rows, …).
```

`Int.prodRange_permute`'s verbatim rendered type (`int_theorem_inventory`)
confirms the third correction's reading exactly: `σ` ranges over `Nat.mapsInto`
— a **full** self-map of `[0,n)`, not a subset map. And `declare_prod_range_permute`
itself (`int_prelude/prod.rs:3185`) is a short induction (~30 lines) that
does nothing but call `permute_step`, which calls `prod_range_swap`
(`declare_prod_range_swap`, `int_prelude/prod.rs:2430`, ~755 lines) which
calls `prod_range_swap_adjacent` (`declare_prod_range_swap_adjacent`,
`int_prelude/prod.rs:937`, ~1,493 lines including its private helpers). That
is **~2,280 lines** of swap/permute machinery, not ~650 — the diary's own
earlier estimate undercounted by more than 3x, measured by counting the
functions rather than guessing from the doc comment's own "took three drafts"
line.

**One genuine mitigation, also checked rather than assumed:**
`int_prelude/prod.rs`'s own `point_override`/`po_inner`/`select_nat_true`/
`select_nat_false`/`override_eq_at` (lines 2608–2717, ~110 lines, private to
that file) are structural duplicates of `nat_prelude/finite.rs`'s own
`point_override`/`po_inner`/`select_nat_true`/`select_nat_false`/
`override_eq_at` (lines 1392–1575) — the latter's own doc comment on the
neighbouring `ne_of_lt` says so explicitly ("the `NatDev` counterpart of
`int_prelude/prod.rs`'s private `ne_of_lt`"). So a `Nat`-native port of the
swap machinery does **not** need to re-derive that ~110-line override
apparatus; `finite.rs` already carries it, one visibility bump away
(`fn` → `pub(super) fn` on `point_override`/`po_inner`/`override_eq_at`) from
reuse. That trims the port, it does not eliminate it — `swap_adjacent`'s
~1,400 remaining lines are the adjacent-transposition induction itself, which
has no existing `Nat` counterpart at any visibility.

**A route that looks free and is not, checked and closed:** `int_prelude`
depends on `nat_prelude` (`build_int_prelude` calls `build_nat_prelude` first,
`int_prelude.rs:1179`), never the reverse. So a `Nat.prodRange_permute` proved
<!-- absent: Nat.prodRange_permute -->
by casting through `Int.ofNat`, reusing the *already-existing*
`Int.prodRange_permute` (`Int.of_nat_pow`, same file, is the existence proof
that this cast-compatibility shape is buildable), is not available from inside
`nat_prelude` — `Int.*` names do not exist yet at the point `nat_prelude` is
built. That route only opens if a future declaration lived downstream of both
preludes, which is out of this slice's scope (`subset_product.rs` only) and
would not actually be `Nat.prodRange_permute` in the `nat_prelude` namespace
Euler's proof needs.

**Verdict:** conjecture CONFIRMED for the part it was actually about —
`Nat.prodRangeIf_permute` costs zero extra induction over `Nat.prodRange_permute`
once the latter exists, via the same extension device already in this file.
Conjecture's implicit hope that this also shrinks the missing full-range lemma
is REFUTED — that lemma is `Nat`-native-only, is not reachable via the `Int`
side, and is measured at ~2,280 lines (~2,170 after reusing `finite.rs`'s
override apparatus), not the ~650 previously guessed. Not attempted in this
slice: building 1,400+ lines of new adjacent-transposition induction, sound
and axiom-free, is a multi-draft undertaking by the original author's own
account, and a `--include-constructed` inventory run plus two verbatim-type
reads is a cheaper way to spend this slice than a first, likely-wrong draft of
it.
