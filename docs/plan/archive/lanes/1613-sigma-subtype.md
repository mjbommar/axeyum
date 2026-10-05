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
`PSigma.{u,v} : Sort (max 1 u v)`, `Subtype.{u} : Sort (max 1 u)`, with
`fst`/`snd` (dependent), `val`/`property`, the defining equations, and `mk_eta`
as a theorem (ι-reduction plus `Eq.refl`, the `Nat.Fin.val_mk` route). Twenty
names, **zero axioms**.

**One divergence from real Lean, found by a gate and not by reasoning.**
`PSigma` was written first at the obvious `Sort (max u v)`. This kernel ADMITS
it and handles it soundly — `max u v` is zero at `u = v = 0`, so it denies large
elimination and leaves a `Prop`-only recursor. **Real Lean rejects the
declaration outright**, and `tests/real_lean_shared_prelude_crosscheck.rs`,
which elaborates the exported prelude in the pinned Lean 4.34.0-rc1, is what
said so — quoting Lean's own hint to use levels of the form `max 1 _`. `PSigma`
now carries Lean's own `Sort (max 1 u v)` and consequently gets large
elimination and both projections. The claim that the `1` is load-bearing is
itself falsifiable: the test declares a probe family at the bare
`Sort (max u v)` into a scratch kernel and REQUIRES its recursor to carry two
universe parameters rather than three.

The lesson beyond this lane: this kernel's universe rules are strictly more
permissive than Lean's in at least one place, and the shared-prelude crosscheck
is the only gate that says so.

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

**Gates, with the numbers.** `cargo test -p axeyum-lean-kernel --release --lib`
2062 passed / 0 failed; all 49 kernel integration suites named explicitly
(`--tests` combined with the lib target hits the 24 G ceiling and dies with
SIGTERM, which is not a test failure) 223 passed / 0 failed;
`clippy --workspace --all-targets --all-features -- -D warnings` exit 0;
`cargo fmt --all --check` exit 0; `validate-facts.py` exit 0;
`check-merge-hygiene.sh` PASS; `gen-plan.py`, `gen-adr-index.py`,
`gen-py-prelude-fields.py` regenerated. `shape_search` over a freshly built
binary: declarations 3935 → 3970, exactly the 35 this lane declared, with every
headline name FOUND 1.

`check-absence-claims.py` exits 1 on findings that are NOT this lane's: 205 bare
claims against a budget of 122, and two EXPIRED claims (`Rat.prodRange`,
`Nat.factorization`) in status files this diff never touches. This lane's own
contribution was one bare claim — the matcher read "not blocked on anything
else" as an absence claim — measured at 206 → 205 by rephrasing that one
sentence, so the contribution is now zero and 205 exceeds the budget without it.

**Mutation-verified, one row.** Dropping the negation from
`IntSpace.bundledDist` (so it adds instead of subtracting) is type-correct and
the kernel admits it. Across `intspace::`, `metric::`, `sigma_prelude::` and
`image_group_tests`: 63 passed, **exactly one failed**, and it is
`the_bundled_distance_subtracts_and_the_body_says_so`. Reverted, 64 pass. Run
in this lane's own isolated worktree, never in the shared checkout.

Two definitions had been covered only by their declared types, which are blind
to exactly the defect that matters (`Bundled → Bundled → CReal` is the type of
`|∫b₁ + ∫b₂|` too), and both now have an evaluation test. The distance one reads
the stored body rather than reducing, and says why: refuting `def_eq` between
two open `CReal` terms does not terminate in useful time — the obvious form was
written first and killed after 60 s.

**A live gap found in passing, recorded and NOT fixed.**
`scripts/gen-py-prelude-fields.py`'s field regex excludes `:`, so a
path-qualified field type does not match and the line is **silently skipped** —
the exact amputation ADR-1512 exists to prevent. Measured: a
`pub sigma: crate::SigmaNames` field was dropped and the generator still printed
`logic=86`. Writing it bare fixed it here (`logic=111`), but
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
| 2026-09-04 | sigma-subtype | the real-Lean crosscheck refused `Sort (max u v)`: `PSigma` follows Lean's `Sort (max 1 u v)` and gains both projections |
| 2026-09-04 | sigma-subtype | `Metric.subspace` + `Metric.crealIntervalSpace` (ADR-1602's site) and `IntSpace.Bundled` + `bundledIntegral` (ADR-1612's site) |
| 2026-09-04 | sigma-subtype | `AlgS.Hom.imageGroup` and `AlgS.Hom.firstIsoClassical` — `G/ker f ≅ Im f` between two group objects (ADR-1595's site) |
| 2026-09-04 | sigma-subtype | ADR-1613 proposed: dependent pairs are an ordinary inductive; the deciding count is 3 of 3 |
| 2026-09-05 | sigma-subtype | evaluation tests for the two definitions covered only by their types; mutation-verified at exactly one death |
