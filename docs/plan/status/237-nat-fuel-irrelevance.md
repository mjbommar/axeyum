# Lane: nat-fuel-irrelevance — fuel-irrelevance for `landAux`, the blocker on 7 open bitwise facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (one auxiliary; transport sized)`, nat-fuel-irrelevance, 2026-08-29).**
Fuel-irrelevance landed for `landAux`, kernel-admitted on the corrected
attempt (one direction bug, see below). None of the 7 blocked facts
(`land_comm`, `land_assoc`, `land_bit`, `lor_comm`, `lor_assoc`, `lor_bit`,
`ldiff_bit`) closed this session — see "What is still needed" for why that is
a separate, larger piece of work than fuel-irrelevance itself, and why the
brief's second acceptance criterion ("fuel-irrelevance for one auxiliary,
with transport to the others sized") is what this lane delivers.

**The statement, and why this hypothesis.** In `nat_prelude/rec_agreement.rs`:

```
Nat.land_aux_eq_land_of_le :
  ∀ fuel m n, Le m fuel → Eq (landAux fuel m n) (land m n)
```

`Le m fuel`, not an unconditional statement: the canonical call
`landAux m m n` puts `m` in the fuel slot and the recursion halves the value
argument every step, so a caller unfolding at a NON-canonical fuel (e.g.
`fuel = bit a m`, `land_bit`'s shape) always has MORE fuel than canonical,
never less — but `landAux 0 m n` for `m > 0` is genuinely `0` while
`land m n` need not be, so the statement is false without some sufficiency
hypothesis. Weaker alternatives were considered and rejected:

- No hypothesis at all: false (the `m > 0`, `fuel = 0` counterexample above).
- `Eq m fuel` (only the canonical fuel): true but useless — it says nothing
  about the very case the 7 facts need, fuel strictly above canonical.

**Which side proved, and why the transport is NOT free (correcting the
brief's framing).** The brief's suggested route was `agree_by_fuel_induction`
inducting on `fuel` alone, generalizing `m`/`n`. That route hits a
self-reference: `land m n` unfolds to `landAux m m n`, which puts the SAME
value `m` in the fuel slot, so relating it to `landAux (succ k) m n` (`k`
from the induction) needs `landAux m m n` to unfold via `m`'s own shape —
and once `m = succ predecessor` is exposed, the recursive call on THAT side
is at fuel `predecessor`, a value the induction's own hypothesis (fixed at
fuel `k`) says nothing about.

The fix, landed here: generalize over BOTH fuels at once
(`ops::agree_by_double_fuel_induction`, a new 3-value-generalized sibling of
`agree_by_fuel_induction`):

Detail moved to [`../notes/237-nat-fuel-irrelevance.md`](../notes/237-nat-fuel-irrelevance.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-fuel-irrelevance | Fuel-irrelevance for `landAux` (`Nat.land_aux_eq_land_of_le`), via a new generic two-fuel agreement induction (`agree_by_double_fuel_induction`); transport to `lorAux`/`ldiffAux` sized but not landed; none of the 7 blocked facts closed |
