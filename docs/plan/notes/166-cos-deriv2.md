# Notes: 166-cos-deriv2

Detail moved out of [`../status/166-cos-deriv2.md`](../status/166-cos-deriv2.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Eight declarations, in two kernel-verified passes: step 1 (lane 159's
per-index derivative for the partial sums) needed one retry for a Rust-level
carrier slip, and step 2 (the two `UniformConvergesOn` re-indexings and the
assembly) was accepted on the first `add_declaration`.

Nothing here is a claim about π. The target is a derivative on `[0, 8/5]`;
what it unblocks — a sign-change witness for `cosFnWide` with a *derivative*
in hand, so `ivt.rs`'s approximate root can be sharpened — is the next
lane's, not this one's.

## Step 1 landed, verbatim from the source

    CReal.cosFnPartialHasDerivative :
      ∀ (n : Nat),
        HasDerivativeOn
          (fun x => sumRange (fun k => cosFnTerm k x) (Nat.succ n))
          (fun x => neg (sumRange (fun k => sinFnTerm k x) n))
          zero (ofRat (Rat.natDivSucc 8 4))

Through `Kernel::add_declaration`, with `creal_prelude_builds` green at
**93.18 s** (recent band 91–112 s), on the second attempt — see "What the
kernel rejected" below; the one rejection was Rust-shaped, not mathematical.

Three declarations under it, all axiom-free by the same build:

1. `CReal.expTermSuccScale : ∀ m, Equiv (mul (ofNat (Nat.succ m)) (expTerm
   (Nat.succ m))) (expTerm m)` — `(m+1)·(1/(m+1)!) = 1/m!`.
2. `CReal.cosFnTermDerivCoeff : ∀ j, Equiv (mul (cosTerm (Nat.succ j))
   (ofNat (Nat.succ (Nat.add (Nat.add j j) 1)))) (neg (sinTerm j))` — the
   index-shifted coefficient identity.
3. `CReal.cosFnTermHasDerivative : ∀ j, HasDerivativeOn (fun x => cosFnTerm
   (Nat.succ j) x) (fun x => neg (sinFnTerm j x)) zero (ofRat (natDivSucc 8
   4))`.

## What the index-shifted coefficient identity cost: **about 70 lines, and
it is the CHEAP kind of `Rat` fact, not the expensive kind**

Lane 159 called it the crux and nobody had priced it. Priced: it is
`declare_exp_term_succ_scale` plus five `mul_congr`/`mul_assoc` steps, and
the whole arithmetic content is one `Rat.normalize` fusion.

The reason it is cheap is worth carrying, because the neighbouring fact in
the same file is **not**. `CReal.ofNat n` unfolds to `ofRat (natDivSucc n 0)`
= `ofRat (normalize (ofNat n) 1 _)` and `expTerm n` to `ofRat (normalize 1
(factorial n) _)`, so **both factors are already `Rat.normalize`s**.
`Rat.normalize_mul_normalize` fuses them into ONE `normalize` and
`Rat.normalize_congr` reduces the goal to the cross-multiplication
`(m+1)·1·m! = 1·(1·(m+1)!)`, which is `Nat.factorial_succ` plus
`mul_one`/`one_mul`/`mul_comm`. `CReal.ofRat_mul` lifts it back.

Contrast `creal/trig.rs::exp_term_antitone_rat`, the ORDER fact
`1/(n+1)! ≤ 1/n!` about the same two terms: ~130 lines of explicit `Int`
regrouping through `normalize_cross`, `iregroup4`, and
`int_le_of_mul_le_mul_right`. **An `Eq` between two `normalize`s is one
`normalize_congr`; a `≤` between them is the full cross-multiplication
battery.** Reach for the equality form when the choice exists.

The sign half needed no parity lemma at all: `pow (neg one) (succ j)`
ι-reduces to `mul (pow (neg one) j) (neg one)`, and `mul_neg_equiv` +
`mul_one` + `neg_congr` give `~ neg (pow (neg one) j)` in three steps.
`CReal.negOnePowDouble` was not needed.

The ONE transport is `Nat.succ_add`: `cosTerm (succ j)`'s own exponent is
`Nat.add (succ j) (succ j)`, and `sinFnTerm j`'s is `Nat.add (Nat.add j j)
1`. Both ι-reduce one step to a `succ`, and the residue
`Nat.add (succ j) j = succ (Nat.add j j)` is `Nat.succ_add` — propositional,
not definitional, because `Nat.add` recurses on the RIGHT. One
`d.nat_rewrite` per site, two sites.

## `hasDerivative_pow`'s two Skolem `BoundedOn` functions were **not** an
obstacle — they cost one `d.lam_fv` each

The brief flagged them as something to check before designing. Checked: they
are `kb`/`kd` with `∀ n, BoundedOn (fun r => pow r n) a b (kb n)` and
`∀ n, BoundedOn (fun x => mul (ofNat (succ n)) (pow x n)) a b (kd n)`.

`creal/trig_fn.rs` **already built** `pow` uniform continuity at a symbolic
exponent — an inline nested induction inside
`declare_cos_fn_wide_uniformly_continuous`, with a byte-identical copy inside
`declare_sin_fn_uniformly_continuous` — and `bounded_via_uc`
(`bounded_of_uniformly_continuous` with its index read back off the inferred
type) turns any of those into a `BoundedOn` with a **computed** index.
Lambda-abstracting that index over the exponent IS the Skolem function. No
`(8/5)^n ≤ 2^n` estimate, no `Nat.pow`, no base-monotonicity lemma — none of
which this development would have supplied cheaply.

That is hiding place 2 twice over, so the copy is gone: `pow_uc_fn` is now
one function and the two `declare_*_uniformly_continuous` call it.

## Step 2's index shift: it does NOT block, and the missing piece is named

The brief asked whether the `succ n`/`n` mismatch blocks
`hasDerivative_congr`. **It does not touch `hasDerivative_congr` at all** —
the mismatch never reaches it. `sumRange`'s own ι-reduction (`sumRange f
(succ m) ≡ add (sumRange f m) (f m)`) makes the FUNCTION sides of both
induction cases definitionally equal, so both `agree_g` hypotheses are
`equiv_refl`. `hasDerivative_congr` is needed only for the two derivative
residues, `Equiv (neg zero) zero` at the base and
`Equiv (neg (A + B)) (neg A + neg B)` at the step.

Where the shift DOES bite is one arrow later, at
`hasDerivative_uniform_limit`, and there it is precise:

> `UniformConvergesOn`'s `spec` bounds the error at index `n` by
> `Rat.natDivSucc rate n`. The shifted family's error at `n` is the
> original's at `succ n`, bounded by the strictly TIGHTER `natDivSucc rate
> (succ n)`; weakening that back to `natDivSucc rate n` is **one-step
> antitonicity of `natDivSucc` in its INDEX at a SYMBOLIC numerator**.

That fact is genuinely absent from `rat_prelude`, and both near misses are
worth naming so the next lane does not re-check them:

- `Rat.natDivSucc_antitone` is `∀ j j', Nat.le j j' → Rat.le (natDivSucc 1
  j') (natDivSucc 1 j)` — numerator **1** only.
- `Rat.natDivSucc_le_scaled` is `∀ k c n, Rat.le (natDivSucc k ((c+1)·n + c))
  (natDivSucc k n)` — general numerator, but it recognises a `(c+1)·n + c`
  index, and `Nat.succ n` is not of that shape for any `c` that leaves a
  bound still shrinking in `n` (`c := n+1, n' := 0` matches the index and
  degrades the bound to `natDivSucc k 0`, a constant).

`CReal.natDivSuccStepLe` closes it without touching `rat_prelude`, and with
no new cross-multiplication: `Rat.natDivSucc_mul` factors `natDivSucc (k·1)
j` as `natDivSucc k 0 · natDivSucc 1 j`, which puts the index entirely in the
second factor where the numerator-`1` antitonicity already applies, and
`Rat.mul_le_mul_of_nonneg_left` scales the comparison back up. **It belongs
in `rat_prelude`; it is in the `CReal` namespace only because that file is
another lane's.**

The other re-indexing, `UniformConvergesOn F G → UniformConvergesOn (neg ∘ F)
(neg ∘ G)`, changes no bound at all: `creal/derivative.rs`'s
`le_abs_neg_of_le_abs` bounds a negation by whatever bounds the original
**without deciding a sign** (`abs` is not `Equiv`-invariant under `neg`, so
this is not a congruence — that helper exists precisely because it cannot
be), and `neg_add_distrib` is the one algebraic step.

## What the kernel rejected

**Once, and it was Rust-shaped.** `d.trans` comes from the `NatOps` trait and
builds `Eq AxNat`, so handing it three `Rat` terms produced

    TypeMismatch  expected : AxNat  got : Rat

with nothing in the message naming `Rat.mul`, `normalize`, or the
declaration. The whole `NatOps` `refl`/`symm`/`trans`/`chain`/`congr` family
is `Nat`-only; `rat_prelude::ops::rchain` is the `Rat` counterpart. This is
the tiny-`expected`-id tell one level up: the `expected` is not a sort, it is
the wrong CARRIER, and the fix is a different chain helper rather than
anything about the proof.

Everything else — all four step-1 declarations, including the induction and
both `nat_rewrite` transports — was accepted first time.

## Reuse, not copying

- `pow_uc_fn` extracted from two byte-identical inline copies (above).
- `neg_add_distrib`, `pow_succ_fn`, `pow_deriv_fn`, `le_abs_neg_of_le_abs`
  promoted to `pub(super)` in `creal/derivative.rs` and imported, not
  reproduced.
- `agree_lam` is new and local: every `hasDerivative_congr` call in this
  section binds and discards the two range hypotheses, because every
  agreement here is an unconditional algebraic identity.

## Verification

`env -u RUST_MIN_STACK scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib creal::creal_tests::creal_prelude_builds`, host load 2.4–2.7:

- after step 1: **93.18 s, green** (`1 passed`).
- after step 2: **98.76 s, green** (`1 passed`) — so the four step-2
  declarations cost nothing measurable against the 91–112 s band.

`every_creal_declaration_is_checked_and_axiom_free` (`--release`): **15.22 s,
green**. That is the check that matters for the headline, because it derives
coverage from `kernel.environment()` in BOTH directions — an environment
declaration missing from every shard, and a shard entry naming a declaration
no longer in the environment — so it confirms all eight are present, are
`Theorem`-kind, and have `axiom_footprint` **0**. A shard list alone would
confirm none of that.

`clippy -p axeyum-lean-kernel --lib --all-features -- -D warnings`: green
(it caught one dead helper this section built and never used;
`creal_prelude_builds` cannot see that).

`cargo check -p axeyum-lean-kernel --lib` clean throughout.
