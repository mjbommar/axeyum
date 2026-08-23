# 242 — One Nat division lemma gates the whole modular-arithmetic corner

**Measured 2026-08-22** by reading the raw statement streams, not by inference.

## The observation

The `Int.ModEq` family was dispatched as a candidate for this project's **second**
general family producer (there is exactly one today, covering five facts, against
24 single-fact capsules — see [239](239-the-train-budget.md)). Before building
anything, the eight exported streams under

    /nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-modeq-family-v1/

were inspected directly. Every one carries an **identical set of 32 theorem
records with proof bodies** — `{"thm": {…, "value": …}}`, which is exactly what
the statement adapter's trusted-declaration refusal exists to reject. Among
them, and unexpected in a statement about congruences:

    Nat.div_rec_lemma
    Nat.div_rec_fuel_lemma
    Nat.le.brecOn

## Why they are there

Structural, not incidental:

    Int.ModEq n a b  ≡  a % n = b % n
                     → Int.emod
                     → Nat.mod
                     → well-founded recursion
                     → Nat.div_rec_lemma

**Anything whose statement mentions `%` on ℤ or ℕ drags in Nat division's
well-foundedness.** The congruence content of `Int.ModEq` is irrelevant to the
blockage; the `%` in its unfolding is sufficient on its own.

## What that changes

`Nat.div_rec_lemma` was already the largest single first-blocker on the adapter
wall at **38 rows** ([240](240-the-cascade-is-exact.md)). It is worth more than
that number says. Behind it also sit:

| | open facts |
|---|---:|
| `integer-modular-equivalence` (train) | 20 |
| `natural-modular-equivalence` (development) | 20 |

So one lemma gates 38 rows of the reflexivity census *and* the entire modular
corner of the nursery, including the family chosen to demonstrate that a general
producer generalizes. It is not a big-and-therefore-later item; it is the gate.

## The cluster is mostly order, not division

The 32 split by subject, and the shape is the useful part:

| group | names |
|---|---|
| division | `Nat.div_rec_lemma`, `Nat.div_rec_fuel_lemma`, `Nat.le.brecOn` |
| `ble` bridge | `Nat.ble_eq_true_of_le`, `Nat.ble_self_eq_true`, `Nat.ble_succ_eq_true`, `Nat.le_of_ble_eq_true`, `Nat.not_le_of_not_ble_eq_true` |
| `sub`/`pred` | `Nat.pred_le`, `Nat.pred_le_pred`, `Nat.sub_le`, `Nat.sub_lt`, `Nat.succ_sub_succ_eq_sub` |
| order | `Nat.le_refl`, `Nat.le_succ`, `Nat.succ_le_succ`, `Nat.le_of_lt_succ`, `Nat.le_of_succ_le_succ`, `Nat.lt_of_lt_of_le`, `Nat.not_succ_le_zero` |
| misc | `eq_of_heq`, `Eq.symm` |
| **already bridged** | `Nat.le_trans`, `Nat.lt_irrefl`, `Nat.zero_le`, `Nat.not_succ_le_self`, `Nat.lt_succ_self`, `Nat.lt_succ_of_le`, `Nat.lt_add_one`, `congrArg`, `noConfusion_of_Nat` |

Only three are division proper. The bulk is the `ble`/`sub`/`pred` **order**
development — and `crates/axeyum-lean-import/src/nat_order_substitution.rs` is
precisely the module that already reconstructs order lemmas internally. Twice
now the largest blocker has turned out to be already built and merely unexposed
as a substitutable name: `Nat.zero_le` (38 rows → 0) and then `Nat.lt_irrefl`
(38 rows, one list entry and a folded match arm). **Check `B::` helpers before
writing new construction.**

## What this does not say

It does not say `Nat.div_rec_lemma` is cheap. Well-founded recursion is not an
order lemma, and the `brecOn` route may need genuinely new work. It says the
lemma is the gate, that most of what surrounds it is order material we plausibly
already have, and that a partial result — the `ble` bridge alone, with a precise
statement of what remains — is worth landing even if the division lemma does not
fall in the same pass.
