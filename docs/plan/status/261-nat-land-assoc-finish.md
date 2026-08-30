# Lane: nat-land-assoc-finish — `Nat.land_assoc` closed, `Nat.lor_assoc` characterized (not attempted)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-land-assoc-finish, 2026-08-29).** Closed
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) by executing the
fully-traced derivation in `docs/plan/status/257-nat-land-assoc-impl.md` —
the fifth lane to work this target and the first to finish it. Every
traced step held as written; the one thing verified rather than trusted
was `257`'s own corrected leaf-split order (`c`, then `b`, then `a`),
re-confirmed against `guarded`'s actual `n`-outermost guard before
transcribing a single line.

## What landed and is kernel-checked

**`Nat.land_aux_assoc_of_fuel : ∀ fuel a b c, Eq (landAux fuel (landAux
fuel a b) c) (landAux fuel a (landAux fuel b c))`** (`rec_agreement.rs`),
unconditional (no `Le` hypothesis — `landAux`'s fuel-exhaustion row is
the absorbing constant `0`). Built via `agree_by_double_fuel_induction`,
step case split `c`, then `b`, then `a`:

Detail moved to [`../notes/261-nat-land-assoc-finish.md`](../notes/261-nat-land-assoc-finish.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-land-assoc-finish | `Nat.land_aux_assoc_of_fuel`/`Nat.land_assoc` built and kernel-verified, executing `docs/plan/status/257-nat-land-assoc-impl.md`'s traced derivation exactly (leaf split c,b,a confirmed against `guarded`'s guard order; hard leaf's double `div_mod_unique` reconstruction closes via `ih`+`mul_assoc`, no new lemmas); `F:ml430-nat-land-assoc-ad4775b8` closed proved/axiom-free via the standard bitwise reconciliation pattern; a pre-existing merge-splice bug in `nat_prelude_tests.rs` (silently disabling the `clog` test) fixed along the way; `Nat.lor_assoc` characterized but not attempted -- `lorAux`'s pass-through fuel row makes the direct propagation lemma analogue FALSE, not merely harder |
