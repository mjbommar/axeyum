# Lane: nat-lor-comm — close F:ml430-nat-lor-comm-2666d7ef (Nat.lor_comm)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-lor-comm, 2026-08-29).** `Nat.lor_comm`
landed and `F:ml430-nat-lor-comm-2666d7ef` is closed. This was the exact task
`docs/plan/status/239-nat-fuel-transport.md` sized as "the same treatment as
`land_comm`, transported to `lorAux`" — that sizing UNDERCOUNTED it, for a
reason worth stating precisely: `land_aux_comm_of_fuel` needs no hypothesis
at all, and its `lor` twin needs two.

**What the kernel rejected, and why: nothing.** `lor_aux_comm_of_fuel` and
`lor_comm` were both admitted on the FIRST `cargo test` run — no rejection to
diagnose, exactly as `land_comm`'s own construction reported.

**Why the sizing was wrong, precisely.** `land`'s fuel-exhaustion row is the
constant `0` regardless of argument order, so
`∀ fuel m n, Eq (landAux fuel m n) (landAux fuel n m)` is TRUE even at
insufficient fuel and needs no hypothesis. `lorAux`'s row is pass-through
(`lorAux 0 m n = n`), so the unconditional analogue is FALSE:
`lorAux 0 0 1 = 1` while `lorAux 0 1 0 = 0` (simulated in Python before
committing to this as the negative-control witness — copying `land`'s own
`(1, 7, 7)` witness would have been VACUOUS here, since `lorAux 1 7 7 = 7 =
lorAux 1 7 7` swapped, no disagreement at all). So
`Nat.lor_aux_comm_of_fuel : ∀ fuel m n, Le m fuel → Le n fuel → Eq (lorAux
fuel m n) (lorAux fuel n m)` carries hypotheses `land`'s analogue does not,
and BOTH matter:

- The base case (`fuel = 0`) needs both `Le m 0`/`Le n 0` to force `m = n =
  0` via `le_antisymm` + `zero_le` — without them the base statement is
  simply false.
- The both-nonzero step needs `half_le_predecessor_of_succ` bounds for BOTH
  halves (`half_a_le_k` AND `half_b_le_k`) to apply the induction hypothesis,
  because the IH itself carries the same two hypotheses. `land`'s analogous
  step needs neither bound at all — it applies its IH unconditionally.

**Which of the four `(m = 0?, n = 0?)` cases differed from `land`'s, as the
brief asked.** All four differed in SHAPE from land's (since `land`'s guard
returns a constant `0` under both guards and `lor`'s returns a pass-through
value), but only the base case and the both-nonzero case needed genuinely
different PROOF TECHNIQUE:

Detail moved to [`../notes/243-nat-lor-comm.md`](../notes/243-nat-lor-comm.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lor-comm | `Nat.lor_aux_comm_of_fuel` (carries `Le m fuel`/`Le n fuel`, unlike `land`'s unconditional analogue) + `Nat.lor_comm`; closes `F:ml430-nat-lor-comm-2666d7ef` via reconciliation with new fact `F:nat-lor-comm`; `bitwise_comm`/`bitwise_swap` sized and left open (need generic-`f` commutativity + the `Nat.bit` decode bridge respectively) |
