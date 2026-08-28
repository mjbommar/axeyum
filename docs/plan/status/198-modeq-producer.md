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

1. **The entire Lean 4.30 `Int` API is `propext`-dependent** — `Int.add_comm`
   and `Int.sub_self` included, not just the `emod` lemmas. The
   empty-axiom-footprint import route therefore cannot reach ANY `Int` target
   without rebuilding `Int` arithmetic from constructors, which is why the Int
   `ModEq` family was closed by the kernel-authored route and why this lane
   closed its train member the same way.
2. **`Nat.ModEq.gcd_eq` (`F:ml430-nat-modeq-gcd-eq-5167ff4f`) is the one
   sibling this route cannot reach**, and the reason is measured, not guessed:
   `Nat.gcd.eq_def` carries `Quot.sound` (`Nat.gcd_zero_left`, `Nat.gcd_succ`
   likewise), so no axiom-free candidate can unfold `Nat.gcd`. The mathematics
   is easy — `gcd a m = gcd (a % m) m = gcd (b % m) m = gcd b m` — and the
   blocker is entirely `Nat.gcd`'s well-founded recursion.

**Pre-existing red this lane did NOT cause, and did not fix:**
`check-development-partition.py` was already failing on `main` for
`authoritative-mathlib-nat-modeq-remainder-family-v1` (a development-only
operation with no train reference); it still is. `clippy -D warnings` on
`axeyum-lean-import` is red on `statement_goal_record.rs:131`
(`format_push_string`), untouched by this lane.

<!-- plan-section: landed-changes -->

| 2026-08-28 | modeq-producer | conclusion-directed producer + axiom-free Lean contract close 10 open `nat.modeq` facts; `via_multi_target` 19 -> 30 |
| 2026-08-28 | modeq-producer | `Int.modEq_of_mul_right` closes the last open `integer-modular-equivalence` train fact, widening the Int shift family 5 -> 6 |
