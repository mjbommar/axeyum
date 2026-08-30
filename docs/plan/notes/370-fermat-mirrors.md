# Notes: 370-fermat-mirrors

Detail moved out of [`../status/370-fermat-mirrors.md`](../status/370-fermat-mirrors.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Held-out check, run before and after: NONE of the nine dispatchable
`fermatNumber` facts were held-out.** ADR-0542-style amendment in
`artifacts/autogenesis/nursery-v2-extension.json`'s `amendments` array (dated
2026-08-30, referencing commit `0065c83b1`) had already moved the WHOLE
`fermat-numbers` family from held-out to `development` before this lane
started — confirmed by reading each of the nine target facts' `partition`
field directly in that manifest (all `"development"`), not merely by the
dispatchable-frontier script. `python3
scripts/check-autogenesis-holdout-isolation.py` reports
`settled=0|references=0|verdict=PASS` unchanged from before this lane's first
commit to after its last.

**`F:ml430-nat-fermat-primefactors-one-lt-58343c6f` — LEFT OPEN, genuinely
blocked, not merely unattempted.** Statement: `1 < n -> Prime p -> p |
n.fermatNumber -> exists k, p = k * 2^(n+2) + 1` (Lucas's refinement of the
classical Fermat-divisor theorem). This needs, in order: (1) a theory of the
multiplicative order of an element mod `p` (minimality + "order divides any
exponent making the power ≡ 1", itself a nontrivial induction) — ABSENT from
this kernel (checked: no `order_of`/`orderOf`/`multiplicative_order` name
anywhere in `nat_prelude.rs` or `int_prelude.rs`); (2) from `p |
fermatNumber n`, that the order of 2 mod p is EXACTLY `2^(n+1)`, giving
`2^(n+1) | p-1` via Fermat's little theorem (`Nat.pow_prime_modeq_self`
EXISTS and would supply this half); (3) the STRONGER `2^(n+2) | p-1` needs
knowing 2 is a quadratic residue mod `p` when `p ≡ 1 (mod 8)` — the second
supplementary law of quadratic reciprocity. `int_prelude/euler.rs` has
`Int.IsQuadraticResidue` and the UNCONDITIONAL half of Euler's criterion
(`a^m ≡ ±1`), but its own module doc says explicitly: "The full criterion —
that the SIGN decides quadratic-residue-hood — needs a primitive root or a
counting argument neither this file nor `wilson.rs` builds." That missing
sign-determination is exactly what step (3) needs. This is a multi-day
formalization project on its own (an order-of-element theory plus enough of
quadratic reciprocity to fix the sign), not a next slice. Left `open`, no
code written against it, no fact touched.
