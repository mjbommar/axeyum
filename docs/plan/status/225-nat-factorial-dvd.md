# Lane: nat-factorial-dvd — `k! ∣ descFactorial`/`ascFactorial` divisibility

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-factorial-dvd, 2026-08-28).** Both
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` and
`F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` are closed — the brief's
"landing the choose bridge plus ONE divisibility fact" bar was cleared twice
over.

`Nat.descFactorial_eq_factorial_mul_choose : n.descFactorial k = k! * n.choose k`
did not exist anywhere in the kernel before this session (confirmed by
reading `choose.rs`/`binomial.rs`/`desc_factorial.rs` in full — no
`descFactorial`-to-`choose` cross-reference existed, and both target facts'
own `open` status recorded the bridge as the deferred prerequisite). It is
the real deliverable: proved by induction on `n`, `k` generalized inside the
motive (mirroring `succ_mul_choose_eq`'s own outer-induction shape), using a
new front-peel identity `Nat.descFactorial_succ_eq_succ_mul : (succ n).descFactorial
(succ k) = succ n * n.descFactorial k` (a separate, simpler induction on `k`
with `n` held fixed) to bridge the outer IH — which is only ever about `n`,
never `succ n` — into the successor step. The successor step's `k = succ j`
case chains six identities: the front-peel lemma, the outer IH at `j`,
`mul_left_comm` (newly promoted `pub(super)` in `binomial.rs`, was file-private
to it), `Nat.succ_mul_choose_eq`, `mul_assoc` (reversed), `factorial_succ`
(reversed). `factorial_dvd_descFactorial` then falls out immediately:
`Nat.dvd_mul : a ∣ a*q` transported along the bridge equation.

Detail moved to [`../notes/225-nat-factorial-dvd.md`](../notes/225-nat-factorial-dvd.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-factorial-dvd | falling/rising-factorial ↔ `choose` bridges + `factorial_dvd_descFactorial`/`factorial_dvd_ascFactorial`, closing 2 `F:ml430-nat-factorial-dvd-*` facts |
