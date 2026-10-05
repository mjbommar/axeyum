# Lane: gauss-final -- Gauss's lemma, items 1 and 3

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, gauss-final, 2026-08-31).**

**Gauss's lemma is proved.** `Int.gaussLemmaSignCount :
a^m ≡ (-1)^gaussNegCount(pp,a,m) [pp]` for `pp = succ (mul 2 m)` with
`Nat.PrimeCond pp` and `gcd(a,pp) = 1` -- admitted by the trusted kernel
gate, `axiom_footprint` empty. That closes the connecting theorem
ADR-0990 sized in five items and ADR-1070 reduced to two, across four
sessions. Full reasoning: **ADR-1130**.

Four declarations landed, every one admitted on the FIRST attempt:

- `Nat.gauss_fold_modeq_of_sign_false`,
  `Nat.gauss_fold_add_modeq_zero_of_sign_true` (`nat_prelude/gauss_lemma.rs`)
  -- item 1's two `Nat` halves. Two statements rather than one because `Nat`
  has no negation: the negative branch is stated ADDITIVELY
  (`a*k + gaussFold ≡ 0`), with `a*k` on the LEFT of the sum because the
  `Int` side consumes it with `add_neg_cancel_right`.
- `Int.gaussTermModEq` (`int_prelude/gauss_term_congruence.rs`) -- item 1,
  the per-term congruence. Case split on `gaussSignNeg` through `prod.rs`'s
  existing `select_int_true`/`select_int_false`; each branch lifted by
  `Int.modEq_of_nat_modEq`.
- `Int.gaussLemmaSignCount` (`int_prelude/gauss_assembly.rs`) -- item 3.
  No new induction: the same skeleton as `Int.euler_totient_theorem`
  (ADR-1110) -- a permuted product cancelled by `Int.ModEq.cancel` -- with a
  SIGN in place of Euler's coprimality predicate, which is why this folds an
  unrestricted `prodRange` where Euler folds `prodRangeIf`.

**Named `gaussLemmaSignCount`, not `gaussLemma`**: `Int.gauss_lemma` is
already taken by EUCLID's lemma, the same misnomer `Nat.gauss_lemma`
carries, and the incumbent is load-bearing (`Int.ModEq.cancel` consumes it).

**Premises in the brief and the handoff that were wrong, all in the
direction the standing rule predicts.** ADR-1070 flagged a possible
`Nat.mul`-to-`Int.mul` distribution lemma for item 1: not needed, for the
same defeq reason the `gauss-assembly` lane found for item 2, and `Int.add`
and `Int.zero = ofNat 0` are free the same way. ADR-1070 also left open
whether item 3's permutation step needed a `Nat`/`Int` bridge like Euler's:
**none at all** -- `Int.prodRange_permute` already quantifies over
`Nat -> Nat` and piece 2's lemmas are already `Nat`-typed. Euler needed the
bridge because ITS permutation is `k -> emod (a*k) n`, genuinely
`Int`-valued; Gauss's is `Nat`-valued by construction.

**One sizing was too OPTIMISTIC, and reusing it would have shipped a weaker
theorem.** `gauss_lemma.rs` already derives `Lt m pp` inside
`declare_gauss_fold_in_range`, through `Nat.lt_two_mul_of_pos` -- which needs
`0 < m`. That is invisible from the call site and fine where it lives (that
proof always holds an index `0 < k <= m`), but Gauss's lemma must hold at
`m = 0` (`pp = 1`), so reusing it would have forced a spurious `0 < m`
hypothesis into the statement. Replaced with `le_add_right m m` transported
along `2m = m+m`, then `lt_succ_of_le`. The general lesson: **a bound proved
inside another declaration carries that declaration's ambient hypotheses,
and lifting it lifts them silently into your statement.**

Nothing was rebuilt that already existed -- every step reused a landed lemma
(`mod_self_congr`, `fold_eq_branch`, `select_int_true`/`_false`,
`modEq_prodRange_lt`, `prodRange_permute`, `prodRange_congr_lt`,
`prodRange_mul`, `ModEq.cancel`), and the only new proof content is the two
`Nat` branch halves.

**Verification** (all foreground, all completed): `cargo test -p
axeyum-lean-kernel --lib nat_prelude::` 278 passed / 0 failed (up from 269);
`--lib int_prelude::` 60 passed / 0 failed (up from 58), including
`every_int_declaration_is_checked_and_axiom_free` and
`derived_laws_have_no_axiom_footprint`, both environment-derived. `cargo
clippy -p axeyum-lean-kernel --lib --tests -- -D warnings` clean;
`rustfmt --edition 2024 --check` clean on all touched files.
`validate-facts.py` 2393 facts / 0 errors;
`check-settled-fact-statements.py` PASS (2207 pinned, drifted 0).
`derived_laws` recounted 235 -> 237 with
`scripts/recount-pinned-inventory.py`, never hand-incremented.

Each new declaration carries a concrete instantiation test alongside the
symbolic build, chosen to DISCRIMINATE: both sign branches (they share no
proof step), and both count parities at `pp = 7` (`a = 3` odd, `a = 2`
even), each with a negative control the kernel must refuse. Because
`Int.ModEq` unfolds to an `emod` equality, the per-term congruence is
verified by computation rather than only by its stated type.

**What this does NOT reach**, and must not be reported as reached: the
second supplementary law of quadratic reciprocity. That is now blocked only
on a `p mod 8` case split over the already-landed
`Nat.gaussNegCountTwoClosedForm`, but it is not proved. Nor is anything
computable said about a general `a`: only the `a := 2` closed form for
`gaussNegCount` exists.

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-final | **Gauss's lemma closes.** `Int.gaussLemmaSignCount` (`a^m ≡ (-1)^gaussNegCount [pp]`) lands axiom-free, first attempt, together with item 1's `Int.gaussTermModEq` and its two `Nat` branch halves -- completing the connecting theorem ADR-0990 sized in five pieces (ADR-1130). Registered as `F:int-gausslemmasigncount` with curated prose. |
