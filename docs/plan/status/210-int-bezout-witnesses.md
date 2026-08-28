# Lane: int-bezout-witnesses — computable Bézout witnesses (`Int.gcdA`/`Int.gcdB`)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, int-bezout-witnesses, 2026-08-28).** Goal:
`F:ml430-int-gcd-eq-gcd-ab-63005aef` states Bézout **at named computable
witnesses**. The existing `Int.gcd_eq_gcd_ab` is the EXISTENTIAL form
(`∃ u v, ofNat (gcd a b) = a*u + b*v`), confirmed by reading
`int_prelude/gcd.rs:1448`; the coefficients live inside a `Prop` and are
unprojectable without choice, so the gap is a genuine *program*, not a
rearrangement. Building it by **fuel recursion** (`nat_prelude/log.rs`'s
device, not `WellFounded` — that route drags `propext`/`Quot.sound`).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-bezout-witnesses | lane opened: computable extended-Euclid witnesses for Bézout |
