# Lane: nat-add-basics -- ten `ml430` Nat addition mirrors, closed through one shared helper

<!-- plan-section: lane-status -->

**Lane block (`DONE -- 10/10 facts closed, 173/173 nat_prelude:: tests green`,
nat-add-basics, 2026-08-29).**

## Headline

| fact | route |
| --- | --- |
| `F:ml430-nat-add-assoc-8c87a1f1` | already existed (`Nat.add_assoc`, `algebra.rs`) -- evidence only |
| `F:ml430-nat-add-comm-56a2d614` | already existed (`Nat.add_comm`, `algebra.rs`) -- evidence only |
| `F:ml430-nat-add-add-add-comm-74d2c151` | new: `Nat.add_add_add_comm` |
| `F:ml430-nat-add-eq-ab0eab69` | new: `Nat.add_eq` (`Eq.refl`, see below) |
| `F:ml430-nat-add-eq-left-8e12789f` | new: `Nat.add_eq_left` |
| `F:ml430-nat-add-eq-right-9067eb1a` | new: `Nat.add_eq_right` |
| `F:ml430-nat-add-eq-zero-64233539` | new: `Nat.add_eq_zero_iff` (NOT `add_eq_zero` -- see below) |
| `F:ml430-nat-add-eq-one-iff-f8463abc` | new: `Nat.add_eq_one_iff`, shared helper |
| `F:ml430-nat-add-eq-two-iff-25385c65` | new: `Nat.add_eq_two_iff`, shared helper |
| `F:ml430-nat-add-eq-three-iff-799a0a8f` | new: `Nat.add_eq_three_iff`, shared helper |

All 10 facts now `epistemic_status: proved`, `python3 scripts/validate-facts.py`
reports 0 errors, `python3 scripts/check-fact-depends-derived.py --fix` ran
(added 180 edges across 128 facts ledger-wide -- flipping `add_assoc`/`add_comm`
from open to proved surfaced every OTHER already-proved fact whose proof term
uses them and had no `depends_on` edge yet, not just this lane's new facts).

## Which already existed

Checked first against `nat_theorem_inventory --release`, comparing rendered
type to `formal.statement`, per the brief:

- `Nat.add_assoc` and `Nat.add_comm` were already declared verbatim in
  `nat_prelude/algebra.rs`'s `declare_additive_theorems`, predating this
  session. Closed by evidence pointing at the existing declaration -- no new
  proof code.
- `Nat.add_eq_zero` ALSO already existed (`declare_add_no_zero_summands`,
  built earlier for a bitwise `land_aux`/`lor_aux` zero-summand argument), but
  its type is the WEAKER mp-only arrow `add a b = 0 -> a = 0 /\ b = 0`, not
  the `Iff` this fact's `formal.statement` states. Read Mathlib's actual
  source (`Init/Data/Nat/Lemmas.lean` at the pinned commit `c5ea0035…`):
  `Nat.add_eq_zero` there is a `@[deprecated Nat.add_eq_zero_iff (since :=
  "2025-10-26")]` alias for the SAME `Iff`. A prelude can never redeclare a
  taken name, so the new `Iff` theorem is named `Nat.add_eq_zero_iff` (the
  post-rename Mathlib name) rather than colliding with the existing weaker
  arrow. mp reuses the existing `add_eq_zero` directly; mpr is new.

## The `add_eq_{one,two,three}_iff` group -- one shared helper

Detail moved to [`../notes/304-nat-add-basics.md`](../notes/304-nat-add-basics.md).

