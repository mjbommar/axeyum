# ADR-0733: `CReal.supOn` bounds `F` at every point of `[a, b]`, and EVT becomes eligible for the two-axis test

Status: accepted
Date: 2026-08-30
Index-summary: `CReal.supOn_ub` is landed, axiom-free, first-attempt kernel
accept — `∀ x ∈ [a, b], F x ≤ supOn F a b hab u` at an ARBITRARY `x`, which is
the one declaration ADR-0710 named as remaining. With `supOn_approx_lub` this
is the pair that characterizes `supOn` as a supremum. **EVT is now eligible
for the per-statement dominance claim and, on the two axes ADR-0692/0699
settled, passes** — but eligibility is a claim about the STATEMENT and this ADR
is careful about what still differs: our hypothesis is uniform continuity on a
closed interval where Mathlib's is continuity on a compact set, and no argmax
exists here or ever will (`evt_attained_max_decides_sign`).
Index-status: accepted

- **Lane:** `supon-ub-arbitrary`
- **Completes:** [ADR-0710](adr-0710-supon-is-a-supremum-from-below-and-on-a-dense-family-from-above.md),
  which landed the approximate least-upper-bound law and the cell-location
  tool, declined to claim the win, and wrote out the four-step route this lane
  executed.
- **Builds on:** [ADR-0691](adr-0691-supon-lands-evt-gets-a-row-one-but-not-yet-the-lub-laws.md)
  (`CReal.supOn` itself).
- **Bears on:** [ADR-0692](adr-0692-the-dominance-test-has-two-axes-not-a-vote-and-ivt-still-passes-it.md)/[ADR-0699](adr-0699-a-derived-count-is-not-a-defended-one.md)'s
  two-axis dominance test, and
  [ADR-0675](adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md).
- **Files:** `crates/axeyum-lean-kernel/src/creal/sup_laws.rs`,
  `crates/axeyum-lean-kernel/src/creal/inventory/sup_laws.rs`,
  `crates/axeyum-lean-kernel/src/creal.rs`,
  `crates/axeyum-lean-kernel/src/creal/creal_tests.rs`.

## Decision

Land `CReal.supOn_ub`:

```
CReal.supOn_ub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) (x : CReal),
  le a x → le x b → le (F x) (supOn F a b hab u)
```

Admitted through `Kernel::add_declaration` with an empty axiom footprint,
verified by `creal_tests::every_creal_declaration_is_checked_and_axiom_free`,
which enumerates `kernel.environment()` rather than a hand-maintained list.
**First-attempt kernel accept.**

`creal_prelude_builds`: **110.54 s before, 110.00 s after** — flat, so none of
the defeq traps this development has accumulated (a `Definition` forced to
unfold, a concrete witness driving partial evaluation) was tripped.

## Which of ADR-0710's four steps held

ADR-0710 wrote the route out in full, and it was accurate. Three steps held
verbatim and one came out **cheaper than predicted**:

1. **Instantiate `stepFamily_locate` at the mesh — held.** The three interface
   identities it named are exactly what was needed and no more.
   `sample_zero_equiv` (`P 0 ~ a`) and `sample_succ_equiv`
   (`P (i+1) ~ P i + Δ`) are re-derivations of `creal/supremum.rs`'s private
   helpers. `mesh_endpoint_equiv` (`P N + Δ ~ b`) is genuinely new, and the
   ADR's recipe for it — `mesh_count_width`, then the `a + (b − a) ~ b`
   cancellation — is right. Worth recording that
   `creal/monotone.rs`'s `subdivisionPoint_in_bounds` runs those same three
   steps already and lands a `le` rather than an `Equiv`, so it could not be
   reused; the `Equiv` version had to be built.
2. **Pick the level above the schedule — held, and DRIFTED cheaper.** The ADR
   said the refinement depth `dd` "comes from `Nat.le_dest` — an `Exists` into
   a `Prop`, which is permitted". It does not have to. Choosing
   `j := supLevel F a b u kk + (Nat.size c + Nat.size outer2)` makes `dd`
   **concrete**, so the obligation `mesh_level_count_ge_of_size` wants is just
   `Nat.le dd (Nat.add level dd)` and no existential is eliminated anywhere in
   the proof. One summand serves both consumers at once.
3. **Absorb the locate epsilon — held exactly, including the arithmetic.**
   `outer2 := Nat.succ (2·outer)`, `eps := ofRat (natDivSucc 1 outer2)`, fused
   by `Rat.natDivSucc_add` then `Rat.natDivSucc_halve`.
4. **`uc_spec` and close — held.** `creal/supremum.rs`'s
   `declare_mesh_max_le_add_of_modulus_thm` was copied for the shape, as
   instructed, and the rate bookkeeping is `supSeq_abs_diff_le`'s.

## Where the margin comes from, since `supLevel` has none

This is the part worth carrying forward, because ADR-0710 correctly identified
that the schedule has **zero** margin and that is precisely why an off-mesh
point cannot reuse it. `supLevel F a b u k` is exactly fine enough for the
modulus at accuracy `k` — enough where mesh points coincide exactly, and with
nothing left over for a point that is not on the mesh. `stepFamily_locate`
hands back `|x − P i| ≤ Δ + eps`, and the schedule alone pays for `Δ` and not
one bit more.

The margin is bought in **two independent places, and neither is a scheduled
level**. Missing either one sinks the proof, and they are not interchangeable:

- **The level**, for the mesh-maximum side. `j` is an arbitrary level ABOVE a
  scheduled one, which `meshMax_le_supOn_add` makes usable for one epsilon
  because `mesh_max_le_add_of_modulus` is depth-uniform. This is what
  ADR-0710's structural finding 1 already supplies.
- **The accuracy the mesh is asked for**, for the uniform-continuity side, and
  this is the one no amount of extra LEVEL can substitute for. Asking
  `mesh_le_of_ge` for `outer2 := succ (2·outer)` — one halving finer than the
  modulus itself demands — makes the reported width `Δ ≤ 1/(2·outer + 2)`,
  which leaves room for a locate epsilon of the same size. The two halves fuse
  to exactly the `1/(outer + 1)` that `uc_spec` consumes, with nothing spare.
  Ask at `outer` instead and the sum `Δ + eps` overshoots the modulus budget,
  and going deeper in the level does not help, because the schedule's guarantee
  is stated at the accuracy you asked for.

The same halving runs a second time at the outer accuracy (`kk := succ (2·e)`)
to split the final `1/(e+1)` between the uniform-continuity transfer and the
mesh-maximum gap. So the proof spends two halvings, at two different levels of
the argument, for two different reasons.

## The value/argmax distinction is untouched

Nothing here produces a maximiser and nothing here may.
`CReal.evt_attained_max_decides_sign` proves that an attaining maximiser would
decide the sign of an arbitrary real — EVT's row 2, a genuine impossibility
result rather than an unfinished proof. `supOn_ub` bounds `F` above; the
companion `supOn_approx_lub` exhibits a point within `1/(e+1)` of the
supremum, and that point moves as `e` moves. No `argmax`-shaped declaration
was added, and none should be.

## Consequences for the dominance claim

**EVT is now eligible, and on the two axes it passes.** Under
ADR-0692/0699's test, with breadth of statement conceded:

- *Trusted base*: `creal` stays at **0**. One new declaration, axiom-free,
  read from the kernel rather than from source text.
- *Computational content*: `supOn` is now a value with **both** halves of the
  supremum characterization — an upper bound at every point of the interval,
  and approached to any requested accuracy at an exhibited point. Mathlib's
  `IsCompact.exists_isMaxOn` gives the bound at every point of the interval,
  and so do we. The gap ADR-0710 named — "Mathlib bounds `F` at every point of
  the interval, and so must we before the statements are comparable" — is
  closed.

**Two things still separate the statements, and neither is closed by this
lane.** Recording them because eligibility is a claim about what is being
compared, and overstating it would be the failure two previous lanes correctly
declined to commit:

1. **The hypothesis is stronger than Mathlib's.** Ours is
   `UniformlyContinuousOn F a b`; Mathlib's is continuity on a compact set,
   from which uniform continuity follows by Heine–Cantor. *We do not have that
   implication in-tree* — measured, not assumed: the prelude has
   `CReal.continuous_at` and nineteen `uniformly_continuous*` declarations and
   **no** bridge between them (positive control: the same grep returns 19 in
   that family). So our theorem applies to a hypothesis a caller must supply
   rather than derive, and anyone quoting per-statement dominance must quote
   the hypothesis with it.

   This is a real difference and it is also not an oversight. Heine–Cantor is
   not available constructively without extra principles, which is exactly why
   Bishop-style analysis takes uniform continuity on compact intervals as the
   *definition* of a continuous function rather than deriving it. Framing it as
   work someone forgot to do would misrepresent it in the other direction; the
   honest statement is that the two developments quantify over different
   classes of input.
2. **The conclusion is a bound, not an attained maximum.** That is deliberate
   and permanent — see the section above — and it is exactly the trade the
   two-axis test was designed to price. It is not a defect, but it is not the
   same proposition as `exists_isMaxOn` either.

So the honest form of the claim is: **EVT's supremum is now stated and proved
here in a form comparable to Mathlib's, axiom-free, with computational
content Mathlib's does not carry — and with a stronger hypothesis and a
constructive rather than attained conclusion.** That is a per-statement
comparison a referee can check, which is what eligibility means; it is not a
coverage claim and must not be quoted as one.
