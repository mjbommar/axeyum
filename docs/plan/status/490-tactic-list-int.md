# Lane: tactic-list-int — `simp::list`, `decide`/`tactic` over ℤ and ℚ

<!-- plan-section: lane-status -->

**DONE, tactic-list-int, 2026-09-03.** Closing two named
cuts: ADR-1586 §4's `simp::list` design sketch (not built by the `simp`
lane), and ADR-1589's ℕ-only `Tactic<D: NatOps>` (ℤ/ℚ scoped out). Landed:
`simp::list` (the fourth `simp` carrier) with congruence-layer gaps filled
in `list_prelude/ops.rs` (621fc000d), the producer itself plus 15 tests
(90667bb65), and five `list_prelude/theorems.rs` base-case retirements
through it (f02488494); `decide` over ℤ (15 tests) and ℚ (14 tests) reusing
`decide::int` for `decide::rat` (9eca4f885); the `Tactic` combinator over ℤ
(5 tests, mirrors ADR-1589's ℕ design) and ℚ (5 tests, no `Simp` variant —
no `simp::rat` exists — `Linarith` is `linarith::generic` at
`Rat.orderedRing`) (ac1e20e04). ADR-1591 amends ADR-1586/ADR-1589. Two bugs
found by running (not inspecting) the work: `simp::list`'s ambient
alpha/beta carrier correction ran only on the descent path, not before
matching (broke `length_map`, a heterogeneous-carrier goal);
`decide::rat`'s first `Le`/`Lt` case blindly `whnf`'d the whole goal, which
over-unfolds past `Int.le`/`Int.lt` (themselves four-case `Definition`s)
into a stuck `Int.rec`.

**Zero `int_prelude`/`rat_prelude` retirements landed — a measured negative,
not an oversight.** Searched (a dispatched fork first, then directly):
`int_prelude/sign.rs::declare_neg_one_mul` looked promising (proves the
SAME statement `simp::int`'s own `neg_one_mul` default rule cites) but IS
that rule's own base declaration — citing it from a rule set that already
depends on it would be circular. More broadly: `ring::int` already
distributes `neg`/`sub` fully over `add`/`mul` as part of its own normal
form (see ADR-1591 §4), so every shape `simp::int`'s default rules could
expose to a `Then(Simp, Ring)` composition is already inside `ring::int`'s
own fragment directly — no genuine "`simp` needed first" case was found.
For `rat_prelude`: every existing hand proof states its order goals via
`Rat.le`/`Rat.lt` directly, not via the `Alg.OrderedRing` record's selector
applications `linarith::generic`'s own parser requires (see ADR-1591 §4's
bug note) — retiring one would need a conversion step beyond a bare
`Then`/`First` call, out of this session's remaining budget. Both `int_prelude`
and `rat_prelude` keep their full test suites green, unmodified. Recorded as
ADR-1591 §5.

**Cost, ADR-1591 §6** (`f7f39f6b4`): `--release`, 200 emissions/shape.
`simp::list` sits in the same order of magnitude as `simp::nat`'s own data
(ADR-1586) despite the extra alpha/beta bookkeeping (0.12–0.14 ms search+
emit); `decide::int`/`decide::rat` are the cheapest producers by a wide
margin (0.003–0.12 ms), `decide::rat` costing more because it delegates
through a second `Definition` unfold rather than deciding directly;
`Then(Simp, Linarith)` over ℤ costs ~4.5 ms, dominated by `linarith::int`'s
own certificate search, consistent with ADR-1589's "cost is the sum of what
it dispatches to".

**Found, not caused: `rat_prelude::det_mul_tests::
mat_subst_rows_replaces_the_window_by_relative_index` overflows the DEBUG
stack on local `main` (confirmed on a fresh `lane-snapshot.sh main`, commit
`369b773`, none of this lane's changes present) — `--release` passes
(1 passed, 7.47s).** This is the same "zero margin" class
`docs/plan/status/451-det-mul-debug-stack.md` already recorded for ℚ's debug
stack envelope (pinned at exactly the 2 MiB a spawned `#[test]` thread
gets); this specific test was not in that lane's own bisection and is a
NEW instance of the same class, not touched by this lane. Not fixed here —
out of this lane's area (`rat_prelude` internals, owned elsewhere); flagged
for whichever lane next touches `check-kernel-stack-envelope.sh` or
`rat_prelude`'s own debug-stack budget.

`check-fact-depends-derived.py --fix`: nothing to fix (`missing_edges=0`).
`validate-facts.py`: 2745 facts, 0 errors — unchanged, this lane adds no
facts. `check-merge-hygiene.sh`: PASS.

<!-- plan-section: landed-changes -->

| 2026-09-03 | tactic-list-int | status stub, lane opened |
| 2026-09-03 | tactic-list-int | list_prelude/ops.rs: expose congr layer, add term builders (621fc000d) |
| 2026-09-03 | tactic-list-int | simp::list producer + 15 tests, fourth simp carrier (90667bb65) |
| 2026-09-03 | tactic-list-int | five list_prelude/theorems.rs retirements via simp::list (f02488494) |
| 2026-09-03 | tactic-list-int | decide over Int (15 tests) and Rat (14 tests) (9eca4f885) |
| 2026-09-03 | tactic-list-int | Tactic combinator over Int (5 tests) and Rat (5 tests) (ac1e20e04) |
| 2026-09-03 | tactic-list-int | ADR-1591, close out, PLAN.md + ADR index regenerated (ce66cefdc) |
| 2026-09-03 | tactic-list-int | measured cost for simp::list/decide::int/decide::rat/tactic::int, folded into ADR-1591 (f7f39f6b4) |
