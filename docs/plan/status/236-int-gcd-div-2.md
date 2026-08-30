# Lane: int-gcd-div-2 — finish `gcd_div_gcd_div_gcd`, assess `gcd_div`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, int-gcd-div-2, 2026-08-29).**
`F:ml430-int-gcd-div-gcd-div-gcd-2db608dc` (`Int.gcd_div_gcd_div_gcd`) is
CLOSED. `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) is confirmed genuinely
absent and re-scoped open with a precise statement of the missing piece — not
attempted, per the "assess, do not assume" brief.

**Closed: `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`.** The prior
`int-gcd-div` lane's handoff (`docs/plan/status/234-int-gcd-div.md`) had
worked out a complete independent Bézout route (not routed through
`Int.gcd_div`, since that lemma doesn't exist) and stopped one step short at
"`Nat.mul g 1` gets stuck at `Nat.add Nat.zero g` for symbolic `g`, needs an
explicit `Nat.mul_one`-style lemma I did not verify against the kernel."

**The handoff's sizing of the stuck point was slightly off, but the fix was
exactly what it named.** The actual construction never needs `Nat.mul_one`
or `Nat.add`/`Nat.zero_add` at all — the stuck term the handoff described
would arise from a NAT-level `g*1` reduction attempt, but the route I built
never reduces at the `Nat` level for this step. Instead: `Int.mul_one(c) :
Eq Int (c*one) c` (an existing lemma taking the multiplicand symbolically,
already used pervasively elsewhere in `int_prelude`) closes `c*1 = c`
directly at the `Int` level, and the subsequent `natAbs`/
`Nat.mul_left_cancel_of_pos` cancellation is what actually descends to `Nat`
— at which point the shared factor is `natAbs c` (defeq to `g`), not a raw
`g*1` term that needs reducing. So the predecessor correctly named the RIGHT
FAMILY of lemma (`Nat.mul_one`) and the right general shape of the problem
(a stuck `Nat.add`/`succ` reduction is this repo's most-documented gotcha),
but the actual proof route I built sidesteps the specific stuck term by doing
the `c*1=c` step at `Int`, not `Nat`.

Full route (`declare_gcd_div_gcd_div_gcd`,
`crates/axeyum-lean-kernel/src/int_prelude/gcd.rs`): with `g := gcd i j`,
`c := ofNat g`, `qi := i.ediv c`, `qj := j.ediv c`, `u := gcdA i j`,
`v := gcdB i j`, `X := qi*u + qj*v`:

Detail moved to [`../notes/236-int-gcd-div-2.md`](../notes/236-int-gcd-div-2.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-gcd-div-2 | closed `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc` via `declare_gcd_div_gcd_div_gcd`, an `Int.mul_one`-based finish of the predecessor's Bézout route; confirmed `Int.gcd_div` genuinely absent (no positive-divisor version exists either) and left `F:ml430-int-gcd-div-5e01872f` open with the three missing lemma statements named |
