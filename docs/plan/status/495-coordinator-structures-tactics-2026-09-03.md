# Lane: coordinator-structures-tactics-2026-09-03 — the day's orchestration of the structures and tactics thrusts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, coordinator, 2026-09-03).** Eighteen lanes merged
to `main` today under one goal: Lean/Mathlib-style structures (data
structures, type classes, abstract structures) and tactics/proof strategies.
ADR-1576 through ADR-1593 record the decisions. The fact ledger went from
2,706 to 2,758 facts with 0 validation errors. Every merge was followed by
the same pass: workspace `cargo check --all-targets`, `py_compile` of every
touched script, `check-fact-depends-derived.py --fix`, `validate-facts.py`,
`check-merge-hygiene.sh`, and the affected kernel suites in `--release`.

**Tactics (producers that emit kernel terms).** `linarith` over ℕ, ℤ and
generically over `Alg.OrderedRing` / `AlgS.OrderedRing` (now reaching
`CReal.orderedRingS`, the setoid payoff being `Equiv` by antisymmetry);
`ring` over ℕ/ℤ/ℚ; `simp` over ℕ/ℤ/List; `decide` over ℕ/ℤ/ℚ; the
`Then`/`First` combinator over ℕ/ℤ/ℚ. Running retirement total: **67 hand
proofs plus 5 list-prelude proofs** replaced by producer output, each
re-admitted at a byte-identical type with axiom footprint 0. A finding that
recurred in three lanes: a producer cannot retire its own primitives, and only
the prelude build catches it, never the unit tests.

**Structures.** `Alg.*` Eq-based record spine (Magma..Field, `OrderedRing`)
with ℕ/ℤ/ℚ instances and forgetful projections; `AlgS.*` setoid spine with
`CReal.commRingS`, `CReal.orderedRingS`, `Complex.commRingS`, `AlgS.Group`
theorems (`inv_unique`, `invInv`) from which `Alg.neg_neg` is now derived.
Data structures: `Nat.Multiset`, `Nat.Finset` (now with
`card_le_of_injOn`, the Finset `pigeonhole`, and the constructive
`exists_collision` witness pair), `List.{u}` with `Perm`; consumer
`Rat.rankCols_le_rank` unconditional.

**Three defects on `main` found and fixed by the coordinator during landing,
none of them the mathematics.** (1) The eleven `creal_linarith_*` tests built
the creal prelude on the bare test thread and aborted in `--release`; wrapped
in `on_a_deep_stack`. (2) `check-theorem-inventory-completeness.py` was red:
`cross_prelude_collision_tests` had no `list` group, so `List.*` names were
never swept for collisions. (3) Five `rat_prelude` / `complex` tests sat at
zero stack margin in debug; the `det-mul-debug-stack-2` lane fixed them and
re-pinned the envelope (debug `nat` and release `rat` both 262,144 →
524,288).

**Open, sized, not built.** `rat`'s debug stack row is still exactly the 2 MiB
default with zero margin; the recommended guard is to run
`check-kernel-stack-envelope.sh --check` as a named push-gate step (a `#[test]`
guard would abort the whole binary, which is the defect itself). No `lt` field
on either ordered-ring record, so the strict fragment of `linarith::generic`
is open. `Complex` has no order. The broader creal retirement census (2,212
order-lemma call sites) beyond the 5 named is unstarted. `are_we_done` reads
`no`.

<!-- plan-section: landed-changes -->

| 2026-09-03 | coordinator | 18 lane merges landed; ADR-1576..1593; facts 2,706 → 2,758, 0 errors |
| 2026-09-03 | coordinator | `5d85e5929` creal-backed linarith tests moved onto the deep stack |
| 2026-09-03 | coordinator | collision sweep gains the `list` group; inventory-completeness gate green (12 labels agree) |
