# Lane: modeq-producer — widen the `nat.modeq` producer to close currently-OPEN facts

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, modeq-producer, 2026-08-28).** The task was to
move the *multi-target operation* counter, not the theorem count.

**Measured, `gen-production-provenance-ledger.py`:**
`via_multi_target` **19 -> 30**, `multi_target_operations` **4 -> 5**,
`operations` 28 -> 29. Eleven facts that were `open` at lane start are now
`proved`, every one of them through an operation that names more than one
target.

**Holdout isolation, before and after, unchanged and PASS:**
`held_out=37|settled=0|references=0`. All eleven open `nat.modeq` targets are
in the **development** partition and the eleventh open sibling this lane also
closed is **train**; nothing held-out was referenced, so no target was dropped
on partition grounds.

**What was actually built.**

- `producers::conclusion_directed_application` (new). The existing
  `bounded_application` grows a forward product closure and its 128-term
  budget is exhausted at application depth 4; **eight of the ten `Nat.ModEq`
  targets need a five-argument application and all eight declined with
  `NoTypedApplication`.** The new producer peels the goal's binders, peels each
  candidate into holes, first-order-matches the candidate's conclusion against
  the goal terminal, and discharges the remaining holes from the goal's own
  binders with bounded backtracking. 10 of 10 accepted, `axioms=0`,
  `target_dependency=false`.
- `scripts/lean/autogenesis_nat_modeq_congruence_contract_v1.lean` — ten
  axiom-free Lean candidates. Every public Lean 4.30 `Nat` remainder lemma
  carries `propext` (measured: `mod_zero`, `mod_eq_of_lt`, `add_mod`,
  `mod_mod_of_dvd`, `mod_self`), so the `Nat.mod` recurrence is rebuilt over
  `Nat.modCore`/`Nat.modCore.go` and every law derived from it by structural
  fuel induction.
- `Int.modEq_of_mul_right` in `int_prelude/modeq_family.rs` — the one still-open
  **train** member of `integer-modular-equivalence`, a twenty-line mirror of
  `declare_modeq_of_mul_left` at `Int.dvd_mul_right`.

**Two findings worth carrying.**

Detail moved to [`../notes/198-modeq-producer.md`](../notes/198-modeq-producer.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | modeq-producer | conclusion-directed producer + axiom-free Lean contract close 10 open `nat.modeq` facts; `via_multi_target` 19 -> 30 |
| 2026-08-28 | modeq-producer | `Int.modEq_of_mul_right` closes the last open `integer-modular-equivalence` train fact, widening the Int shift family 5 -> 6 |
