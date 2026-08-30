# Lane: nat-stragglers — the two `Nat` stragglers left by `283-nat-div-mod-family`

<!-- plan-section: lane-status -->

**DONE for this dispatch (`nat-stragglers`, 2026-08-29).** Both targets closed.

```
F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0   -- proved
F:ml430-nat-base-induction-83561d4c               -- proved
```

**`add_div_of_dvd_add_add_one`.** `∀ {c a b}, c ∣ (a+b+1) → (a+b)/c = a/c+b/c`.
The prior lane's route sketch (compare divisibility's forced remainder
against a case split on `ra+rb` vs `c`) was directionally right but the
actual derivation needed was cleaner than either sketch or my own first plan:
decompose `a=c*qa+ra`, `b=c*qb+rb` via `div_mod_exec`, so `a+b+1 =
c*(qa+qb)+(ra+rb+1)`. Case-split `ra+rb+1` against `c` (`lt_or_ge`) — below
`c` this is ALREADY a valid `divMod` decomposition of `a+b+1`, and comparing
it against the one the `dvd` witness gives (remainder `0`) via
`div_mod_unique` forces `ra+rb+1=0`, refuted by `succ_ne_zero` since it's a
successor. At or above `c`, subtracting `c` once (`sub_add_cancel`) gives a
remainder `r'` also `<c` (bounded via `ra<c`,`rb<c` and
`le_of_succ_le_succ`/`add_le_add_left`/`add_le_add_right`/`le_trans`), and
comparing THAT decomposition against the same `dvd`-witness relation forces
`r'=0`, i.e. `ra+rb+1=c` exactly — pinning `ra+rb=c-1<c`, which closes the
goal against `div_mod_exec`'s own decomposition of `a+b`. No case-split on
the `dvd` witness `q`'s shape was needed at all (an earlier plan detour I
abandoned once the derivation above worked without it). New file
`nat_prelude/div_mod_lemmas.rs` extension (the ninth/last mirror in that
family); module doc there has the full step list.

Detail moved to [`../notes/293-nat-stragglers.md`](../notes/293-nat-stragglers.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-stragglers | `Nat.add_div_of_dvd_add_add_one` — the ninth/last `ml430` add/div/mod shift-family mirror, axiom-free (new file `nat_prelude/div_mod_lemmas.rs` extension). |
| 2026-08-29 | nat-stragglers | `Nat.base_induction` — strong induction over `Nat.lt`'s well-foundedness, axiom-free (new file `nat_prelude/base_induction.rs`); confirmed the pinned source is Lean core (`Init.Data.Nat.Div.Lemmas`), not Mathlib proper. |
