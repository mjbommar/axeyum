# Lane: int-gcd — closing three of the seven `Int.gcd` import-backlog facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for the three landed; one fact deliberately
deferred with a sized reason`, int-gcd, 2026-08-28).** Closed
`F:ml430-int-ne-zero-of-gcd-f71f00df`,
`F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82`, and
`F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222`, each via a
genuine new kernel declaration in `int_prelude/gcd.rs`
(`declare_ne_zero_of_gcd`, `declare_gcd_eq_one_of_gcd_mul_right_eq_one`).
Left `F:ml430-int-gcd-div-5e01872f`, `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`,
and `F:ml430-int-gcd-greatest-5b31c5fe` untouched (not attempted — see
below); did not close `F:ml430-int-gcd-eq-gcd-ab-63005aef` (the brief's
"interesting one" — my characterization of it was correct, see below).

**The brief's characterization of `Int.gcd_eq_gcd_ab` was RIGHT, and the
closing work is LARGER than "small but real".** The kernel's existing
`Int.gcd_eq_gcd_ab` proves `∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v` —
confirmed by reading `declare_gcd_eq_gcd_ab` in `gcd.rs` line-by-line: the
`stmt` it builds is an `Exists`/`Exists` nest (`exists_name` applied twice),
never a named witness. Mathlib's `Int.gcd_eq_gcd_ab` is
`∀ x y, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y` — computable projections,
not an existential. These are different propositions.

Detail moved to [`../notes/196-int-gcd.md`](../notes/196-int-gcd.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-gcd | `Int.ne_zero_of_gcd` + `Int.gcd_eq_one_of_gcd_mul_right_eq_one_left`/`_right` landed as new kernel declarations in `int_prelude/gcd.rs`; three ml430 facts flipped `open`→`proved`, axiom-free; `Int.gcd_eq_gcd_ab` (existential Bézout) confirmed NOT the same fact as Mathlib's computable `gcd_eq_gcd_ab` and left open with a sized reason; `gcd_div`/`gcd_div_gcd_div_gcd`/`gcd_greatest` not attempted |
