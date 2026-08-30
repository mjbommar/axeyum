# Notes: 222-nat-asc-multichoose

Detail moved out of [`../status/222-nat-asc-multichoose.md`](../status/222-nat-asc-multichoose.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Did NOT attempt `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641`
(`k! ∣ n.ascFactorial k`) — a genuinely nontrivial divisibility induction,
out of scope for this slice per the brief ("landing ONE definition with its
boundary lemmas is a complete success"). No target in this lane's families
(`natural-binomial`, `natural-factorial`) carried a HELD-OUT or MUTATION
marker.

New facts (do NOT flip any `F:ml430-nat-*` mirror fact — these are our own
independent constructions): `F:nat-asc-factorial-zero`,
`F:nat-asc-factorial-succ`, `F:nat-asc-factorial-one`,
`F:nat-multichoose-zero-right`, `F:nat-multichoose-one`,
`F:nat-multichoose-one-right`. `python3 scripts/validate-facts.py`: 0 errors.

Next lane: `factorial_dvd_ascFactorial` (needs a real induction over
`Nat.dvd`/`Nat.choose` algebra), or `Nat.zero_ascFactorial` in our own
prelude (currently only closed via the separate autogenesis statement-
reflexivity route, not this kernel's `Nat.ascFactorial`).
