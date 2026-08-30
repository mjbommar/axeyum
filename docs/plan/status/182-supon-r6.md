# Lane: supon-r6 — `CReal.supOn` rung 6, the per-level gap bound

<!-- plan-section: lane-status -->

**Rung 6's gap bound LANDED (supon-r6, 2026-08-28).** Three declarations,
each a first-attempt kernel accept, all axiom-free and covered by
`creal_tests::every_creal_declaration_is_checked_and_axiom_free` (which reads
the environment, not a list):

- `CReal.meshPoint_near_coarse` — the **multi-level nearest-mesh-point
  lemma**, the piece nothing in the tree had. Every level-`(j+d)` mesh point,
  at *any* refinement depth `d`, sits in one level-`j` cell: between that
  cell's left endpoint and one coarse width above it.
- `CReal.maxRange_le_add_of_exists` — `maxRange_transport` restated to take an
  `eps`-estimate instead of an `Equiv`, and an `Exists` **witness** instead of
  a supplied index function `e : Nat -> Nat`.
- `CReal.meshMax_le_add_of_step_close` — **the gap bound**:
  `le (meshMax F a b (Nat.add j d)) (add (meshMax F a b j) eps)` at arbitrary
  depth, from a one-sided pointwise hypothesis on `F`.

**The `creal/supremum.rs` module doc's "Rung 6 re-verified (2026-08-27)"
section was right about WHAT blocks rung 6 and wrong about why it is
expensive.** Its diagnosis held up exactly: the blocker is the per-level gap
bound; `trueExpOfModulus` really can jump the mesh level by arbitrarily many
doublings; a nearest-coarse-point fact at *any* depth really is what that
needs. But it prices both candidate routes as "comparable in scope to a rung
of their own" because it assumes the coarse index must be **computed** — route
1 needs an index computation, route 2 needs a finer accuracy schedule.

Neither is true. The gap bound's conclusion is `Prop`, so the coarse index can
be an `Exists` witness that the induction step re-eliminates. Kernel fact 2
(`Exists.rec` is `Prop`-only) constrains rung 7's `CReal.mk`, where `K` and
`f_lambda` are DATA; it says nothing about a `le`-valued estimate. Once the
index is existential, "which coarse cell contains fine index `i'`" never has
to be answered: induct on depth and split the fine index's parity with
`Nat.even_or_odd`. No quotient/remainder algebra, no `bucketIndex`, no
schedule refinement — and `uniform_continuity.rs`'s still-open `crossingClose`
side condition is never touched, so nothing here imports that gap.

Detail moved to [`../notes/182-supon-r6.md`](../notes/182-supon-r6.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | supon-r6 | `supOn` rung 6: the multi-level nearest-mesh-point lemma, the `eps`/existential transport combinator, and the arbitrary-depth gap bound — three first-attempt kernel accepts, axiom-free |
