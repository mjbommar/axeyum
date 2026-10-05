# Lane: mirror-frontier — close the `Nat` min/max mirror family

<!-- plan-section: lane-status -->

**Done (`DONE`, mirror-frontier, 2026-08-31).** Twelve `ml430` mirrors closed,
all of them the `Nat` min/max family, from the live dispatchable set. Eighteen
theorems admitted through `Kernel::add_declaration` on the first attempt, every
one axiom-free.

**Selected from the live frontier, not from a handoff.**
`python3 scripts/check-dispatchable-frontier.py --json` at lane start: exit 0,
**26 dispatchable**, 166 held-out, 12 mutation controls, 11 blocked. (The brief
said 37; the live number was 26. The queue is the authority.) Twelve of the 26
were one coherent family over `Max.max`/`Min.min`, which `nat_prelude/minmax.rs`
had declared as definitions with — per ADR-0653 — no theorem about either. That
is what made them a family rather than a scattered dozen: four rewrite cuts
close all twelve.

**Held-out isolation, before and after:** `held_out=166 settled=0 PASS` both
times. Every one of the twelve is `train` or `development` in
`nursery-v2-extension.json`; the whole `natural-minmax` family is `development`,
so the six supporting theorems declared alongside carry no ADR-0645
contamination risk (checked before declaring, not after).

## The honesty question, and where the tree was wrong

`minmax.rs`'s module doc says any mirror "stated against Mathlib's REAL,
typeclass-elaborated `Max.max`/`Min.min` stays `open` … this module only opens
the vocabulary". Read as a claim about typeclass machinery that is correct.
Read as a claim about the **propositions** it is too strong, and applying it as
a blanket would rule out every already-settled mirror mentioning `+`.

Checked at the pinned toolchain source (`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean`),
not from a paraphrase:

| site | content |
| --- | --- |
| `Init/Prelude.lean:1311` | `maxOfLe … where max x y := ite (LE.le x y) y x` |
| `Init/Prelude.lean:1328` | `minOfLe … where min x y := ite (LE.le x y) x y` |
| `Init/Data/Nat/Basic.lean:873` | `instance : Max Nat := maxOfLe` |
| `Init/Prelude.lean:2088` | `instance : Min Nat := minOfLe` |
| `Init/Data/Nat/Basic.lean:871` | `Nat.min_def : min n m = if n ≤ m then n else m := rfl` |

That is `minmax.rs`'s definition verbatim (its `Nat.ble` branch is what
`Nat.decLe` decides). Same **function**, same value at every pair; only the
delivery differs, exactly as `HAdd.hAdd`/`instAddNat` differ from `Nat.add` in
every settled `+` mirror. So these flip honestly under the def-vs-theorem
criterion. The rendered types differ from the pinned surface statements only in
binder info.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/minmax_lemmas.rs` (new), wired last in
`build_nat_prelude`, plus `minmax_lemmas_tests.rs` (new) and 18 entries in
`nat_prelude_tests::theorem_names`.

The twelve mirrors, with the type `nat_theorem_inventory` renders:

| fact | `Nat.…` | rendered type |
| --- | --- | --- |
| `F:ml430-nat-le-max-left-685a3331` | `le_max_left` | `(x0 x1 : AxNat) -> AxNat.le x0 (Max.max x0 x1)` |
| `F:ml430-nat-le-max-right-3cd92fc9` | `le_max_right` | `(x0 x1 : AxNat) -> AxNat.le x1 (Max.max x0 x1)` |
| `F:ml430-nat-max-comm-a9a3642b` | `max_comm` | `Eq AxNat (Max.max x0 x1) (Max.max x1 x0)` |
| `F:ml430-nat-le-min-of-le-of-le-407ecd4b` | `le_min_of_le_of_le` | `le x0 x1 -> le x0 x2 -> le x0 (Min.min x1 x2)` |
| `F:ml430-nat-le-min-69904590` | `le_min` | `Iff (le x0 (Min.min x1 x2)) (And (le x0 x1) (le x0 x2))` |
| `F:ml430-nat-lt-min-1a793099` | `lt_min` | `Iff (lt x0 (Min.min x1 x2)) (And (lt x0 x1) (lt x0 x2))` |
| `F:ml430-nat-add-max-add-left-37eb9f8d` | `add_max_add_left` | `Eq (Max.max (add x0 x1) (add x0 x2)) (add x0 (Max.max x1 x2))` |
| `F:ml430-nat-add-max-add-right-178bc311` | `add_max_add_right` | `Eq (Max.max (add x0 x2) (add x1 x2)) (add (Max.max x0 x1) x2)` |
| `F:ml430-nat-add-min-add-left-9728864e` | `add_min_add_left` | `Eq (Min.min (add x0 x1) (add x0 x2)) (add x0 (Min.min x1 x2))` |
| `F:ml430-nat-add-min-add-right-b483207e` | `add_min_add_right` | `Eq (Min.min (add x0 x2) (add x1 x2)) (add (Min.min x0 x1) x2)` |
| `F:ml430-nat-add-eq-max-iff-39576e6d` | `add_eq_max_iff` | `Iff (Eq (add x0 x1) (Max.max x0 x1)) (Or (Eq x0 0) (Eq x1 0))` |
| `F:ml430-nat-add-eq-min-iff-e60cf432` | `add_eq_min_iff` | `Iff (Eq (add x0 x1) (Min.min x0 x1)) (And (Eq x0 0) (Eq x1 0))` |

Six supporting theorems, also Mathlib/Lean-core names verbatim:
`max_eq_right`, `max_eq_left`, `min_eq_left`, `min_eq_right`, `min_le_left`,
`min_le_right`. No fact is registered for these — they are ordinary prelude
machinery, and the family is `development`.

## What was actually hard, and it was not the proofs

`Max.max a b` is `bool_select_nat (ble a b) b a` — a `Bool.rec` **stuck** at a
symbolic `Nat.ble a b`. Nothing about `max` reduces until the boolean is known,
so every proof begins by learning it, and two details decide whether the term
type-checks:

- **The rewrite runs in the symm direction.** `Eq.rec` at `Bool` with
  `p := true`, `q := ble a b`, along `bool_symm(ble_eq_true_of_le …)`.
  Transporting forward would need the goal as its own `refl` case. The `refl`
  case is `Eq (bool_select_nat true b a) b`, which iota-reduces because the
  scrutinee is a literal.
- **`Le b a` does NOT decide the boolean.** At `a = b` it is `true` and the
  *other* arm is selected, so `max_eq_left` and `min_eq_right` split on
  `bool_true_or_false` and close the `true` arm through `Nat.le_antisymm`,
  rather than assuming a false boolean. Getting this wrong would have produced
  a theorem false at `a = b` — the boundary case now has its own test instance.

`lt_min` is `le_min` at `succ a` by defeq (`Nat.lt` is a `Definition` unfolding
to `Le ∘ succ`), which is how Lean core states it too: `Nat.lt_min := Nat.le_min`.

Nothing here inducts and nothing forms a numeral larger than `0`, so the unary-
numeral cost documented in CLAUDE.md never comes into play.

## One negative control was vacuous, and it is recorded

The first test run failed on a control I had written at concrete `(7, 2)`:
`max 7 2` reduces to `7`, so `a ≤ max a b` and `max a b ≤ a` are **literally the
same proposition** and the "control" could not have failed. Both transposed
controls moved to the symbolic instance, where the `Bool.rec` is stuck and the
two sides are genuinely different terms. Recorded in the test file and in the
fact evidence rather than quietly fixed — this is the "negative controls fail
two ways" trap arriving in a lane that had read the entry.

## Gates run (all foreground, all complete)

| gate | result |
| --- | --- |
| `cargo test -p axeyum-lean-kernel --lib nat_prelude::` | 290 passed, 0 failed |
| `cargo test -p axeyum-lean-kernel --lib int_prelude::` | 61 passed, 0 failed |
| `cargo test -p axeyum-lean-kernel --lib nat_prelude::minmax` | 9 passed, 0 failed |
| `python3 scripts/validate-facts.py` | 2444 facts, 0 errors |
| `python3 scripts/check-settled-fact-statements.py` | `PASS`, `drifted=0` |
| `python3 scripts/check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS` |
| `python3 scripts/check-dispatchable-frontier.py` | exit 0, 14 dispatchable remain |
| `python3 scripts/check-shape-duplicates.py` | 15 groups, all allowlisted |
| each fact's `checker_command` | 12 positives exit 0; `le_max_left_bogus` exits 1 |

`every_nat_declaration_is_checked_and_axiom_free` derives its coverage from
`kernel.environment()`, so it also confirms all eighteen carry an empty
`Kernel::axiom_footprint`.

## Note for whoever merges

`check-fact-depends-derived.py --fix` also repaired one edge this lane did not
cause — `F:rat-int-right-distrib` was missing `F:ml430-int-add-mul-66aa025b`,
pre-existing drift that `validate-facts.py` was already red on. It is in this
lane's commit because the validator cannot pass with it outstanding.

## Remaining dispatchable frontier (14)

Two families and two singletons: ten `stirlingFirst`/`stirlingSecond` rows
(`stirling.rs` has the definitions), two `Nat.size` rows, plus
`fermat-primefactors-one-lt` and `squarefree-ext-iff`. The `stirling` ten look
like the next coherent group, on the same shape as this one — the definitions
exist and no theorem about either has been declared.
