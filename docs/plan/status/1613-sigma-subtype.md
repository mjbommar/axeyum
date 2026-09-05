# Lane: sigma-subtype — declare `Sigma`/`Subtype` in the kernel and re-test the three sites they blocked

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, sigma-subtype, 2026-09-04).** W0-5, ADR-1613.
Three ADRs hit the same wall in one day — ADR-1595 (the image of a hom needs a
subtype), ADR-1602 (a metric subspace needs `Subtype`), ADR-1612 (L¹ needs
`Sigma` to bundle an integrability witness into a carrier) — and ADR-1606
declined a design for the same reason. The question was whether the absence was
an oversight or ADR-1495's constructor-field universe guard refusing a
`Sort (max u v)` result.

**It was an oversight. The guard never fired, and it was not touched.** It
rejects a field whose universe is strictly ABOVE the family's result universe;
every field of a dependent pair sits at or below it, and `Kernel::level_leq`
discharges `u ≤ max u v` and `u ≤ max 1 u` symbolically. The clearest evidence
it was never the obstruction: the kernel has admitted two *specializations* of
this shape all along — `Nat.Fin` (`⟨val, isLt⟩`) and `CReal` (`⟨seq, regular⟩`).
Only the universe-polymorphic form was missing.

Landed in the logic prelude (`sigma_prelude.rs`), so the existing shape_search /
projection groups index it with no new group: `Sigma.{u,v} : Type (max u v)`,
`PSigma.{u,v} : Sort (max u v)`, `Subtype.{u} : Sort (max 1 u)`, with
`fst`/`snd` (dependent), `val`/`property`, the defining equations, and `mk_eta`
as a theorem (ι-reduction plus `Eq.refl`, the `Nat.Fin.val_mk` route). Eighteen
names, **zero axioms**.

**`PSigma` is the measured asymmetry and it is not a defect.** `max u v` is zero
at `u = v = 0`, so the kernel refuses large elimination and `PSigma.rec` carries
no motive universe — it therefore gets no projections. The recursor
universe-parameter counts (3 / 2 / 2) are the assertion, because that count IS
the kernel's own per-family verdict.

**`Fin` was NOT added.** `Nat.Fin` already exists in `nat_prelude/finite.rs`,
already in the subtype form, with `val`, `isLt` and `val_mk`.

**THE DECIDING MEASUREMENT: 3 of 3.** Each blocked site's previously-unstatable
statement is now written, admitted, and axiom-free.

- **(a) ADR-1595** — `AlgS.Hom.imageGroup : AlgS.Group` over
  `Subtype H.carrier (AlgS.Hom.image G H f)`, and `AlgS.Hom.firstIsoClassical`:
  `G/ker f ≅ Im f` as three conjuncts about two `AlgS.Group` objects
  (well-defined-and-injective / homomorphism / surjective). Fourteen of the
  image group's fifteen fields are FREE — `Subtype.val` ι-reduces, so every law
  reduces to what `H` already proves. The whole cost is three membership proofs
  (one `Exists` elimination + one `H.equivTrans` each), and the three conjuncts
  are then `Iff.intro (fun h => h) (fun h => h)`, `fMul` verbatim, and
  `Subtype.property`. The subtype's equivalence is inherited from `H.equiv` on
  `val`, exactly as ADR-1595 predicted. `AlgS.Hom.firstIso` is unchanged.
- **(b) ADR-1602** — `Metric.subspace M P : Metric`, carrier
  `Subtype M.carrier P`, distance restricted; `Metric.subspace_dist` is an
  `Eq.refl`, so "the distance is the ambient one restricted" is now a theorem
  rather than a design note. No hypothesis on `P` at all. First instance:
  `Metric.crealIntervalSpace` — `[a,b] ⊂ ℝ` as a metric space in its own right.
  **W2-10's subspace half is OPEN**, not blocked on anything else; migrating the
  existing `*On` forms is a separate decision with real proof cost.
- **(c) ADR-1612** — `IntSpace.Bundled S := Sigma.{0,0} S.carrier
  (IntSpace.Integrable S)`, at `Sort 1`, which is exactly the universe
  `declare_record` fixes a carrier at. `IntSpace.bundledIntegral` is the
  integral as a TOTAL function of one argument, with `bundledIntegral_bundle`
  (an `Eq.refl`) saying the bundle loses nothing. Needs `Sigma` and not
  `Subtype`, because `Integrable` is `Sort 1` DATA.
  **What is still blocked:** the L¹ seminorm `‖f−g‖₁ = ∫|f−g|` needs absolute
  value on the carrier and an integrability witness for `|f|` — the
  lattice/`|·|`-closure gap `intspace.rs` already names. `bundledDist` is
  `|∫b₁−∫b₂|`, the right SHAPE and not the L¹ metric; it is labelled as such.

**A live gap found in passing, recorded and NOT fixed.**
`scripts/gen-py-prelude-fields.py`'s field regex excludes `:`, so a
path-qualified field type does not match and the line is **silently skipped** —
the exact amputation ADR-1512 exists to prevent. Measured: a
`pub sigma: crate::SigmaNames` field was dropped and the generator still printed
`logic=86`. Writing it bare fixed it here (`logic=109`), but
`ComplexPrelude.poly: poly::PolyNames` is still being skipped today. The fix is
not a one-line regex change — `PolyNames` is defined in two files, which is why
that field is qualified — and the script belongs to another lane, so it is in
ADR-1613's last section rather than in this diff.

**Also for the record:** ADR-1606's stated ground for rejecting `Fin n → CReal`
("the subtype route is closed") no longer holds. This lane did not reopen that
decision; ADR-1606 has other reasons.

<!-- plan-section: landed-changes -->

| 2026-09-04 | sigma-subtype | opened W0-5: confirmed `Sigma`/`PSigma`/`Subtype`/`Fin` absent at declarations=3935 with two positive controls |
| 2026-09-04 | sigma-subtype | `Sigma`, `PSigma`, `Subtype` admitted in the logic prelude, zero axioms; ADR-1495's guard never fired and was not touched |
| 2026-09-04 | sigma-subtype | `Metric.subspace` + `Metric.crealIntervalSpace` (ADR-1602's site) and `IntSpace.Bundled` + `bundledIntegral` (ADR-1612's site) |
| 2026-09-04 | sigma-subtype | `AlgS.Hom.imageGroup` and `AlgS.Hom.firstIsoClassical` — `G/ker f ≅ Im f` between two group objects (ADR-1595's site) |
| 2026-09-04 | sigma-subtype | ADR-1613 proposed: dependent pairs are an ordinary inductive; the deciding count is 3 of 3 |
