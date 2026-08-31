# ADR-1110: Euler's totient theorem lands, axiom-free, first attempt

Status: accepted
Date: 2026-08-31
Index-summary: Closes the Fermat -> Euler handoff
(`docs/plan/status/374-euler-theorem.md`, ADR-1025). `Int.euler_totient_theorem
: forall n a, 0 < n -> Coprime a (ofNat n) -> ModEq (ofNat n) (pow a (totient
n)) one` is admitted by the trusted kernel gate on the first attempt,
axiom-free, no new induction in the final assembly -- every ingredient
(the residue permutation, the predicate-preservation iff, and four new
`prodRangeIf` congruence/coprimality/factoring lemmas landed the same
session) was proved separately and wired together.

## Context

ADR-1025 closed item 2 of the three-piece handoff (the predicate-preservation
iff) and re-sized item 1 (the `Int`/`Nat` bridge) down to "assembly, not
invention" — most of it free by defeq. Item 3, the final product/power
assembly, was the one piece the handoff called genuinely new mathematics: an
induction this kernel had not built before, pairing a restricted (subset)
product with a count.

This lane (`euler-assembly`) picked up exactly that remaining item, re-verified
each of the prior lane's claims in-tree per the standing "a handoff's report
of what REMAINS is a hypothesis" rule, and completed it in five landings.

## What landed, in order

1. **`Int.prodRangeIf_coprime`** (`euler_prod_coprime.rs`) — a restricted
   product of factors each coprime to `m` stays coprime to `m`. The one piece
   needing a genuine induction (on the range bound), using a per-element case
   split that carries the actual `pred k = true`/`= false` hypothesis (the
   "generalize the equation, instantiate at `bool_refl`" trick from
   `nat_prelude/subset_product.rs::bool_case`, ported to `IntDev` as
   `bool_case_int`) rather than the simpler "supply the goal at each literal
   constructor" idiom, because this goal genuinely needs the hypothesis to
   invoke the pointwise coprimality assumption. Two reusable pieces were
   extracted along the way and made `pub(super)` in `euler_totient.rs`:
   `coprime_mul` (two-factor coprimality multiplicativity, lifted out of
   `declare_euler_unit_coprime`'s own inline derivation) and `coprime_one`
   (`Coprime one m` unconditionally, via `Nat.coprime_one_left_iff`).
2. **`Int.prodRangeIf_factor_const_left`** (`euler_prod_factor.rs`) —
   pointwise factoring of a constant out of a restricted product. Not a fresh
   induction: the selector's payload identity holds unconditionally at every
   index, so this used the simpler literal-constructor idiom feeding
   `Int.prodRange_congr` into `Int.prodRange_mul` (both already proved).
3. **`Int.prodRangeIf_modeq`** (`euler_prod_modeq.rs`) — a restricted product
   reduces mod `n` factor by factor. Also not a fresh induction: the pointwise
   hypothesis is unconditional in the index, so this feeds
   `Int.modEq_prodRange` (already proved, unrestricted) directly.
4. **`Int.euler_totient_theorem`** (`euler_assembly.rs`) — the assembly
   itself, a nine-step chain: `preserve` (multiplication-by-`a` preserves the
   coprimality predicate, from `Int.euler_unit_coprime_iff` plus a Bool/Prop
   reflection bridge ported from `nat_prelude/totient_lemmas.rs`'s private
   `bool_eq_of_iff_eq_one`) feeds `Int.prodRangeIf_permute`; a nonnegativity
   bridge (`Int.of_nat_nat_abs_of_nonneg`) relates the permuted product to the
   raw-residue product; `Int.prodRangeIf_modeq` moves it to the unreduced
   product; `Int.prodRangeIf_factor_const_left` and
   `Int.prodRangeIf_const_eq_pow_count` (landed the prior session) turn the
   constant factor into `pow a (totient n)`; `Int.prodRangeIf_coprime`
   supplies the coprimality `Int.modEq_cancel` needs to cancel the surviving
   product, and `Int.ModEq.symm` finishes.

Every one of the four new declarations was admitted by the kernel on the
**first attempt** — no `TypeMismatch` iteration needed at any step, including
the nine-step assembly itself. `theorem_axiom_footprint` confirms:

```
integer	Int.euler_totient_theorem	0
```

## What made the assembly tractable

The predicate `pred := fun k => beq (gcd k n) 1` is a per-file local copy of
`Nat.totient`'s own internal `totient_predicate`, built with the identical
sequence of `d.gcd`/`d.num(1)`/`d.beq` calls — so `Nat.totient n` unfolds
(pure delta) to exactly the statement's `countRange pred n`, with no separate
bridging lemma. This is the same "build in unfolded form, let the kernel's
own delta/iota/beta reduction do the rest" convention every sibling file in
this handoff uses, and it is what let a nine-step, cross-file proof chain
type-check without incident: at every join point (permutation output vs. the
raw-residue selector, the unreduced-product selector vs. the factoring
lemma's own internal construction, the coprimality predicate vs.
`Nat.totient`'s own), the two sides were built via the identical primitive
call sequence rather than merely proved equal, so the kernel's defeq checker
closed the gap for free.

The one recurring Rust-level hazard, not a kernel one: `d.foo(d.bar(...))` —
a nested mutable-borrow of the same `IntDev` — does not compile (`E0499`,
"cannot borrow `*d` as mutable more than once at a time"). Every such
construction needed its inner call bound to a `let` first. Not encountered in
any of this handoff's earlier, single-purpose files (each kept its argument
lists short enough to avoid it by accident); the nine-step assembly's longer
argument lists hit it nine separate times.

## What this closes

Euler's totient theorem — the generalization of Fermat's little theorem this
session's handoff was named for — is now a proved, axiom-free kernel theorem.
`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
§2.2 and `docs/plan/status/374-euler-theorem.md`/`euler-theorem-spine.md`
should be read as superseded by this ADR for that entry: nothing remains open
in the Fermat -> Euler handoff.

## Verification

```sh
cargo test -p axeyum-lean-kernel --lib int_prelude::
# 56 passed, 0 failed, including every_int_declaration_is_checked_and_axiom_free
# and derived_laws_have_no_axiom_footprint
cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings
# clean, exit 0
cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint -- euler_totient_theorem
# integer  Int.euler_totient_theorem  0
python3 scripts/validate-facts.py            # 0 errors
python3 scripts/check-settled-fact-statements.py --write, then bare   # PASS
python3 scripts/check-autogenesis-holdout-isolation.py                # PASS, unaffected
```
