# ADR-1130: Gauss's lemma closes -- and the handoff's remaining blockers were not what it took

Status: accepted
Date: 2026-08-31
Index-summary: **Gauss's lemma is proved, axiom-free, in this kernel**:
`Int.gaussLemmaSignCount : a^m ≡ (-1)^gaussNegCount(pp,a,m) [pp]` for
`pp = 2m+1` with `Nat.PrimeCond pp` and `gcd(a,pp) = 1`. That closes the
connecting theorem ADR-0990 sized in five pieces and ADR-1070 reduced to
two, and makes this the second classical theorem to land the same day after
`Int.euler_totient_theorem` (ADR-1110), on the same skeleton -- a permuted
product cancelled by `Int.ModEq.cancel`, with a SIGN in place of Euler's
coprimality predicate. Four declarations, all admitted on the FIRST attempt,
all with an empty `axiom_footprint`. Two of ADR-1070's sizings were wrong in
the direction its own standing rule predicts (a handoff's "what remains" is a
hypothesis): the `Nat`-to-`Int` multiplication bridge it flagged as possibly
needed was free by defeq in item 1 as well as item 2, and item 3's
`prodRange_permute` step needed NO `Nat`/`Int` bridging at all. One sizing
was too OPTIMISTIC and is recorded here: `gauss_lemma.rs`'s own route to
`Lt m pp` requires `0 < m` and would have silently excluded `m = 0`.
Index-status: accepted

## Context

Gauss's lemma (the quadratic-residue one, not Euclid's) has been the standing
target of five prior ADRs. ADR-0970/ADR-0985 landed the counting primitive
(`Nat.gaussNegCount`) and the `a := 2` closed form. ADR-0990 landed piece 1
(least-residue injectivity) and sized the connecting theorem in FIVE items.
ADR-1015 and the `gauss-mapsinto-bound` lane closed piece 2 (`gaussFold` is
`InjectiveOn`/`MapsInto` on `[0,m)`). ADR-1070 landed item A
(`∏(a·k) = a^m·m!`) and the sign-product identity; the `gauss-assembly` lane
landed item 2 (`gcd(m!,pp) = 1`, both carriers).

That left two items, and `docs/plan/status/gauss-assembly.md` said so
explicitly: **(1)** the per-term congruence, and **(3)** the final assembly,
blocked on (1).

**Every named prerequisite was verified in-tree before any proof term was
written**, per this repository's standing rule that a handoff's report of what
REMAINS is a hypothesis while its report of what LANDED is reliable. The
verification changed the plan twice (below).

## Decision

**Land both remaining items. Gauss's lemma is proved.**

### Item 1 -- the per-term congruence, in three declarations

The statement is `a·k ≡ ε_k · gaussFold(pp,a,k) [pp]`, where
`ε_k := -1` when `Nat.gaussSignNeg pp a k` and `+1` otherwise.

**The `Nat` side is TWO statements, not one, and that is forced.** `Nat` has
no negation, so "`a·k ≡ −gaussFold [pp]`" cannot be said there at all. So
(`nat_prelude/gauss_lemma.rs`):

- `Nat.gauss_fold_modeq_of_sign_false : 0 < pp → gaussSignNeg pp a k = false →
  modEq pp (a*k) (gaussFold pp a k)`. On that branch `gaussFold` IS the least
  residue, so `mod_self_congr` plus one transport along `fold_eq_branch`
  closes it.
- `Nat.gauss_fold_add_modeq_zero_of_sign_true : 0 < pp →
  gaussSignNeg pp a k = true → modEq pp (a*k + gaussFold pp a k) 0`. The
  ADDITIVE form: `gaussFold = pp − leastResidue` there, so
  `mod_eq_add_right` on `mod_self_congr` plus `sub_add_cancel` (fed `mod_lt`)
  gives `a*k + gaussFold ≡ leastResidue + gaussFold = pp ≡ 0`.

**The operand order in that sum is load-bearing, not cosmetic.** `a*k` goes on
the LEFT because the `Int` side turns the sum into the negation with
`Int.add_neg_cancel_right`, which consumes `(x+y)+(−y)`; `(y+x)+(−y)` would
need a commutation step that buys nothing.

`Int.gaussTermModEq` (`int_prelude/gauss_term_congruence.rs`) then case-splits
on the `Bool` and lifts each branch through `Int.modEq_of_nat_modEq`, using
`prod.rs`'s existing `select_int_true`/`select_int_false` for the selector.
The negative branch's shift is `Int.ModEq.add_right` by `−gaussFold`, then
`add_neg_cancel_right` on the left and `add_comm`/`add_zero` on the right,
then `neg_one_mul` to reach the selector's `-1` form.

### Item 3 -- the final assembly

`Int.gaussLemmaSignCount` (`int_prelude/gauss_assembly.rs`), no new induction:

```text
A^m · m!  =  ∏_{j<m} (A · ofNat (succ j))     [prodRange_scaledIndexEqPowMulFactorial]
          ≡  ∏_{j<m} (ε_j · Φ_j)      [pp]     [gaussTermModEq, via modEq_prodRange_lt]
          =  (∏ ε_j) · (∏ Φ_j)                 [prodRange_mul]
          =  (-1)^gaussNegCount · m!           [gaussSignProdEqPowNegOneOfCount; ∏Φ = m!]
⟹  A^m ≡ (-1)^gaussNegCount  [pp]              [ModEq.cancel at m!]
```

`∏ Φ = m!` is `Int.prodRange_permute` at `σ j := pred (gaussFold pp a (succ j))`,
plus one `prodRange_congr_lt` repairing `succ (pred _)` through the positivity
half of `Nat.gauss_fold_in_range`.

## What ADR-1070's sizing got wrong, in both directions

Recorded because the repository's standing rule predicts one direction and not
the other.

**Too pessimistic, twice.**

1. ADR-1070 flagged a possible `Nat.mul`-to-`Int.mul` distribution lemma as
   needed "for this step too" (item 1), noting the `gauss-assembly` lane had
   found it unnecessary for item 2 and telling the next lane to check. It is
   unnecessary here as well, for the same reason: `Int.mul (ofNat a) (ofNat k)`
   is defeq `ofNat (mul a k)` at SYMBOLIC arguments, since `Int.mul`'s case
   split dispatches on the outer `Int` constructor only. `Int.add` behaves the
   same way, which is what makes the additive branch's `ofNat (a*k + fold)`
   land on `Int.add x g` for free, and `Int.zero` is *defined* as `ofNat 0`,
   which is what makes the bridge's right-hand side need no rewrite. **Three
   carrier bridges, all free, none of them assumed -- each was checked.**
2. ADR-1070 sized item 3's permutation step as needing piece 2's
   `InjectiveOn`/`MapsInto` "fed to `Int.prodRange_permute`" and left open
   whether a `Nat`/`Int` bridge was required (the Euler lane had needed exactly
   such a bridge, `euler_theorem.rs`'s item 1). **None is needed.**
   `Int.prodRange_permute` already quantifies over a `Nat → Nat` self-map, and
   piece 2's lemmas are already `Nat`-typed, so they apply directly. The Euler
   analogy is what made this look harder than it is: Euler's permutation is
   `k ↦ emod (a*k) n`, genuinely `Int`-valued, and needed the round trip;
   Gauss's is `Nat`-valued by construction.

**Too optimistic, once, and this one would have shipped a weaker theorem.**
The final assembly needs `Lt m pp` to feed `coprime_factorial_of_lt_prime`.
`gauss_lemma.rs` already derives exactly that bound inside
`declare_gauss_fold_in_range`, and reusing it is the obvious move. It routes
through `Nat.lt_two_mul_of_pos`, which **requires `0 < m`** -- fine there,
because that proof always has an index `0 < k ≤ m` in hand, and invisible from
the call site. Gauss's lemma has no such index and must hold at `m = 0`
(`pp = 1`). Reusing the existing route would have forced a spurious `0 < m`
hypothesis into the theorem's statement. The replacement is
`Nat.le_add_right m m : Le m (m+m)` transported along `2m = m+m`, then
`Nat.lt_succ_of_le` -- no positivity anywhere.

Generalising: **a bound proved inside another declaration carries that
declaration's ambient hypotheses, and lifting it lifts them silently into your
statement.** Check what the reused step needs, not only what it concludes.

## Naming

The kernel name is `Int.gaussLemmaSignCount`, not `Int.gaussLemma`, because
**`Int.gauss_lemma` already exists and is EUCLID's lemma**
(`Coprime a b → a ∣ b*c → a ∣ c`, `int_prelude/gcd.rs`) -- the same common
misnomer `Nat.gauss_lemma` carries. Renaming the incumbent is out of scope and
it is load-bearing (`Int.ModEq.cancel` consumes it). Both the module doc and
the fact's curated prose say which is which; a referee reading the inventory
sees the full statement in the name's row either way.

## Verification

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- **278 passed, 0
  failed** (up from 269).
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` -- **60 passed, 0
  failed** (up from 58), including `every_int_declaration_is_checked_and_axiom_free`
  and `derived_laws_have_no_axiom_footprint`, both of which read the
  ENVIRONMENT rather than a literal list and so cover the new declarations
  rather than merely listing them.
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings` clean.
- `python3 scripts/validate-facts.py` -- 2393 facts, 0 errors.
- `python3 scripts/check-settled-fact-statements.py` -- PASS, 2207 pinned,
  drifted 0.
- The `checker_command` on both new facts DISCRIMINATES: it prints `1` and
  exits 0 for the real declaration name and prints `0` and exits 1 for a
  misspelling of it (run both ways).

Every new declaration was admitted by `Kernel::add_declaration` on the FIRST
attempt, with an empty `Kernel::axiom_footprint` asserted inside the test
rather than inferred from the prelude-wide figure.

### Concrete instantiation, on the axes that could be silently wrong

The standing rule is that a symbolic accept and a concrete check fail on
disjoint defect classes. Both concrete tests are chosen to discriminate:

- `gauss_term_mod_eq_computes_on_both_sign_branches_at_pp_7_a_3` exercises
  **both** branches (`k = 1` non-negative with fold 3, `k = 2` negative with
  fold 1). They share no proof step, so one branch says nothing about the
  other. `Int.ModEq` unfolds to an `emod` equality, so the congruence itself
  is checked by COMPUTATION, not merely by its stated type. Control: replacing
  the `k = 2` sign with `+1` -- one constant, both sides still concrete
  numerals -- makes it false (`6` against `1` mod 7), and the kernel must
  refuse it.
- `gauss_lemma_matches_direct_computation_at_pp_7_for_both_parities` runs the
  theorem at `a = 3` (count 1, ODD, `27 ≡ 6`) and `a = 2` (count 2, EVEN,
  `8 ≡ 1`). **Opposite parities**, so the count-to-sign link cannot agree by
  accident. Both counts were recomputed in Python, not inherited from
  `gauss_lemma.rs`'s existing table. The coprimality hypothesis is a genuine
  `Eq.refl 1` witness (`gcd a 7` reduces); only `PrimeCond` is a context fvar,
  since the conclusion's TYPE does not depend on which proof inhabits it.
- `gauss_fold_branch_congruences_compute_at_pp_seven_a_three` does the same
  for the two `Nat` halves independently, with a control that swaps the
  negative branch's fold for the un-folded residue (`9 ≡ 2`, not `0`).

## Consequences

- The connecting theorem is closed, so the second supplementary law of
  quadratic reciprocity (`2` is a QR mod `p` iff `p ≡ ±1 (mod 8)`) is now
  blocked only on a `p mod 8` case split over the already-landed
  `Nat.gaussNegCountTwoClosedForm` -- `int_prelude/qr_criterion.rs`'s module
  doc names Gauss's lemma as one of its two routes and this is that route
  arriving. **That supplement is NOT proved here and must not be reported as
  such.**
- Gauss's lemma at a general `a` says nothing computable about whether `a` is
  a residue until `gaussNegCount pp a m` is evaluated, and only the `a := 2`
  closed form exists. Full quadratic reciprocity needs a lattice-point count
  this kernel does not have.
- `docs/plan/status/gauss-assembly.md`'s two-item list is now empty. The
  five-item sizing that began at ADR-0990 is closed across four sessions.
