# Lane: agent-creal-order — the lattice over the constructed ℝ

<!-- plan-section: lane-status -->

**ADR-0519: `CReal.max`, `CReal.min` and `CReal.abs` are BUILT, and they cost
no index shift (`WIP`, agent-creal-order, 2026-08-19).**
`max` looks like it needs a decision, and ℝ has none — but it does not have to
be *derived* from one. `Rat.le a b` **is** `Int.le (num a·den b) (num b·den a)`,
so `Rat.max` dispatches by `Int.rec` on the sign of the cross-difference, where
the sign is a **constructor**; one `Rat.max_cases` carries every lattice law and
there is exactly one `Int.rec` in the module. And `Rat.sub_max_le` — joint
one-Lipschitz-ness — means `max` does not degrade the modulus, so `CReal.max`
samples at the **same** index as its arguments: the first operation since
`CReal.neg` that costs no shift. The same lemma with the `Equiv` hypotheses in
place of the regularity facts *is* `max_congr`. `CReal.abs x := max x (neg x)`,
so it adds no sequence and no regularity obligation. **94 `CReal` declarations,
trusted surface still 0**; `Rat.abs` still does not exist. Design, the measured
mutation counts, and what is left undone with its cost:
[`../notes/creal-lattice.md`](../notes/creal-lattice.md).
*(`Rat.abs` has since landed; this status entry is a historical record.)*
<!-- was-absent: Rat.abs -- since landed -->

<!-- plan-section: landed-changes -->

| 2026-08-19 | `4c7af898d` | **ℝ is a lattice.** 15 `Rat` + 18 `CReal` declarations, every one accepted on first submission, all footprint-free. The predicted obstacle — a four-way sign split over `|a| − |b| ≤ |a − b|` — never appears. Nothing here has a side condition, so the failure mode is a *degenerate operation*, not a vacuous guard: `max x y := x` satisfies `le_max_left` by reflexivity and `abs x := x` satisfies `le_abs_self`, `neg_le_abs` and `abs_le`. So `not_le_zero_neg_one` and `not_equiv_abs_neg_one` are proved from the laws alone, the witness's exit status depends on both, and `max x x ≈ x` / `max 0 1 ≉ 0` / `min 0 1 ≉ 1` are admitted **through the kernel**. One level down, `Rat.max`/`Rat.min` are checked to COMPUTE on both branches with the wrong answer REFUSED — the nine `ℚ` laws are all one-sided and would hold of a projection. Three one-token mutations refused. |
