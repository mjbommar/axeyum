# ADR-0960: Euler's criterion's necessary direction lands; the second supplementary law stays open pending Gauss's lemma or a root-counting converse

Status: accepted
Date: 2026-08-31
Index-summary: `Int.euler_criterion_residue_imp_one` (a quadratic residue's half-power is exactly `≡ 1`, not merely `≡ ±1`) and `Int.euler_criterion_neg_one_imp_not_residue` (the contrapositive-ish non-residue detector for odd primes) land axiom-free in `int_prelude/qr_criterion.rs`, built on the witness-reduction pattern in `euler.rs` plus a new `pow_mul_self` induction lemma. The second supplementary law of quadratic reciprocity (2 is a QR mod `p` iff `p ≡ ±1 mod 8`) is NOT reached: it needs either the full converse of Euler's criterion (a primitive root or an `x^m - 1`-has-at-most-`m`-roots counting argument, neither buildable with this kernel's inductive list `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable` + `Nat.le`/`Nat.Fin`/`Char`) or Gauss's lemma (a `Nat.countRange`-shaped sign-counting argument over least residues, also absent).
Index-status: accepted

## Context

A theorem lane sizing Lucas' 1878 theorem on Fermat number prime factors
declined it, naming two prerequisites: multiplicative order of 2 mod `p`
(judged buildable elsewhere, Fermat's little theorem already exists) and the
second supplementary law of quadratic reciprocity, for which the tree had
almost nothing: `Int.is_quadratic_residue` (definition),
`is_quadratic_residue_one`, `is_quadratic_residue_mul` (closure facts), and
`euler_criterion_pm_one` (the *unconditional* half of Euler's criterion:
`a^((p-1)/2) ≡ ±1 [p]` for an odd prime, without deciding which sign or
relating either sign to residue-hood) — all in `int_prelude/euler.rs`, whose
own module doc already records that the full criterion "needs a primitive
root or a counting argument neither this file nor `wilson.rs` builds."

Verified before starting with a fresh `shape_search --include-constructed`
over 2,514 declarations: no Gauss's lemma, no supplementary laws, no Legendre
symbol, no Euler criterion beyond the `±1` dichotomy. Both `int_prelude/crt.rs`
and `nat_prelude/crt.rs` exist (the two-preludes-one-basename hazard this
repository's CLAUDE.md names); neither carries residue-counting machinery
relevant here. `nat_prelude/count_range_permute.rs` and
`count_range_reversal.rs` are counting/reindexing lemmas over `Nat.countRange`,
but at a different subject (permutation invariance, not least-residue sign).

## Decision

**Route chosen: extend Euler's criterion in the direction Fermat's little
theorem already decides**, rather than attempt Gauss's lemma or the full
converse in this lane. Reasoning:

- Euler's criterion's **necessary** direction (residue ⟹ half-power `≡ 1`)
  follows directly from Fermat's little theorem
  (`Int.pow_prime_sub_one_modeq_one`, already landed) applied to the
  residue witness's canonical reduction — no new axiom, no counting, no
  primitive root.
- Its contrapositive-shaped corollary (half-power `≡ -1` on an ODD prime ⟹
  not a residue) follows from the necessary direction plus `1 ≢ -1 [p]` for
  `p > 2`, itself elementary (`p ∣ 2` forces `p ≤ 2` via `Nat.le_of_dvd`).
- **Gauss's lemma was rejected for THIS lane** because it needs a
  least-residue sign-counting fold over `Nat.countRange` at a scale this
  session did not have room to build and independently verify (a bounded
  count discriminating `p mod 8`'s four residue classes, plus the
  floor-division reasoning connecting `⌊(p+1)/4⌋`'s parity to the class) —
  real, multi-session work, not a corner that shrinks under scrutiny the way
  several documented "needs deep induction" sizings in this repository have.
- **The full converse was rejected for the same reason euler.rs's own doc
  gives**: it needs either a primitive root (this kernel has no cyclic-group
  order/index machinery over the constructed integers) or a polynomial
  root-counting fact (`x^m - 1` has at most `m` roots mod a prime `p`), and
  this kernel has no `List`/`Finset`/polynomial carrier to state either.

## What landed

`crates/axeyum-lean-kernel/src/int_prelude/qr_criterion.rs` (new module):

- **`Int.euler_criterion_residue_imp_one`** — `∀ pp aa m, prime pp → pp-1 =
  m+m → 0 < aa → aa < pp → IsQuadraticResidue (ofNat pp) (ofNat aa) → ModEq
  (ofNat pp) (pow (ofNat aa) m) one`. Route: eliminate the residue witness
  `x` (`x*x ≡ a`); reduce `x` to its canonical residue `r := emod x p`
  (`reduce_witness_to_residue`, generalizing `euler::reduce_to_canonical_residue`
  from the fixed target `one` to an arbitrary in-range `a` — the nonzero step
  now contradicts `0 < a < p` via `Nat.le_of_dvd`/`Nat.lt_irrefl` rather than
  primality); Fermat gives `r^(p-1) ≡ 1`, rewritten via the caller's `p-1 =
  m+m` hypothesis to `r^(m+m) ≡ 1`; `Int.ModEq.pow` transports that along
  `x ≡ r` (same exponent both sides) to `x^(m+m) ≡ 1`; a new lemma,
  `pow_mul_self` (`(x*x)^m = x^m * x^m`, by induction on `m` — the successor
  step is exactly `euler::sq_mul_sq_eq_mul_sq` at `X := x^j`, `Y := x`,
  bumped from private to `pub(super)` for reuse), combined with `Int.pow_add`
  identifies `x^(m+m)` with `(x*x)^m`; `Int.ModEq.pow` along `x*x ≡ a`
  finally relates that to `a^m`.
- **`Int.euler_criterion_neg_one_imp_not_residue`** — `∀ pp aa m, prime pp →
  2 < pp → pp-1 = m+m → 0 < aa → aa < pp → ModEq (ofNat pp) (pow (ofNat aa)
  m) (neg one) → Not (IsQuadraticResidue (ofNat pp) (ofNat aa))`. Under a
  residue hypothesis the previous theorem gives half-power `≡ 1`; combined
  with the `≡ -1` hypothesis, `1 ≡ -1 [p]`, i.e. `p ∣ 2`; `Nat.le_of_dvd`
  forces `p ≤ 2`, contradicting `p > 2`.

Both bumped three `euler.rs` helpers (`int_exists_elim`, `residue_predicate`,
`sq_mul_sq_eq_mul_sq`) from module-private to `pub(super)` — visibility-only
changes, no behavior change.

**Axiom footprint, read from the kernel** (`theorem_axiom_footprint`,
`--release`): both theorems `0` — axiom-free, matching the surrounding
`integer` prelude's `997 theorems, 997 axiom-free`. Confirmed by
`int_prelude::int_prelude_tests::derived_laws_have_no_axiom_footprint` and
`every_int_declaration_is_checked_and_axiom_free` (both now cover the two new
names; the `derived_laws` pin was recounted 217 -> 219 via
`scripts/recount-pinned-inventory.py`, not incremented by hand).

Both theorems are stated and proved fully SYMBOLICALLY (`pp`, `aa`, `m` are
all bound `Nat` variables, never instantiated at a concrete prime) — the
harder, more revealing check this repository's own retrospectives recommend
over a concrete-only instantiation, since the whole proof chain (witness
reduction, exponent rewriting, `pow_mul_self`'s induction) is exactly the
kind of multi-step composition where a concrete numeral can paper over a
defeq gap a symbolic `fresh_fvar` cannot.

## What remains, sized for the next lane

The second supplementary law (`IsQuadraticResidue p 2 ↔ p ≡ 1 [8] ∨ p ≡ 7
[8]`, for odd prime `p`) needs, in order of what would unlock the most:

1. **Either** a primitive root existence theorem over the constructed
   integers (needs order-of-an-element / group-index machinery this kernel
   does not have — likely a full session), **or** a polynomial
   root-counting lemma (`ModEq p (pow x m) one` has at most `m` solutions
   mod a prime `p`) stated without `List`/`Finset` — plausibly via a
   `Nat.countRange`-bounded injectivity argument mirroring the pattern
   `nat_prelude/factorization.rs` and the totient refinements used (induct
   past the missing multiset-uniqueness object rather than evaluate it) —
   untried, unsized.
2. **Or, independently, Gauss's lemma**: define `leastResidueSign p a k :=`
   whether `emod (a*k) p` exceeds `p/2` for `k` ranging `1..(p-1)/2`, fold a
   `Nat.countRange`-based count of the negative signs, and show its parity
   equals the Legendre-symbol sign. For `a := 2` specifically the count has
   the closed form `⌊(p+1)/4⌋`, whose parity is a four-way case split on `p
   mod 8` — a genuinely different (and probably smaller) argument than the
   general lemma, worth sizing on its own before committing to the general
   case.
3. Either route (1) or (2), once the sign is pinned to `p mod 8`, still
   needs the case split itself: four residue classes, each an elementary
   `Nat.mod`/`Nat.dvd` argument, cheap once the hard part above exists.

None of (1)-(3) were attempted this session; sizing them further needs actual
construction, which is exactly the trap this repository's Gotchas file warns
against repeating in prose. The honest state: **the second supplementary law
is not reachable from what landed here alone, and reaching it needs one
substantial new piece of infrastructure (counting or group theory) that does
not yet exist anywhere in this kernel.**

## Verification

- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 52 passed, 0
  failed (nonzero count confirmed; was 51 passed/1 failed before the
  `derived_laws` pin update).
- `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.
- `theorem_axiom_footprint` (`--release`) on both new names — `0` each.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — PASS before and
  after (this lane never touched `artifacts/autogenesis/`).
- No fact-ledger entries added this session (no `artifacts/facts/` changes);
  `python3 scripts/check-settled-fact-statements.py` therefore has nothing new
  to check here.
