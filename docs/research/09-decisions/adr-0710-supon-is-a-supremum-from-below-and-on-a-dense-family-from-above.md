# ADR-0710: `CReal.supOn` is characterized from below, and from above on a family that can be made as fine as wanted

Status: accepted
Date: 2026-08-30
Index-summary: The approximate least-upper-bound law
(`CReal.supOn_approx_lub`) is landed, axiom-free — `supOn` is approached by
values of `F` on `[a, b]` to any requested accuracy, at a point the proof
exhibits, and the exact attaining form stays refuted by
`evt_attained_max_decides_sign`. The upper-bound law is landed at every point
the construction samples and at every mesh level ABOVE the schedule, but NOT
at an arbitrary `x` in `[a, b]`: that needs one composition on top of
`CReal.stepFamily_locate`, which is also landed. **EVT is therefore still not
eligible for the per-statement dominance claim**, and this ADR says exactly
what remains.
Index-status: accepted

- **Lane:** `supon-laws`
- **Answers, in part:** [ADR-0691](adr-0691-supon-lands-evt-gets-a-row-one-but-not-yet-the-lub-laws.md),
  which landed `CReal.supOn` and correctly declined to claim the win, naming
  the two missing laws.
- **Bears on:** [ADR-0692](adr-0692-the-dominance-test-has-two-axes-not-a-vote-and-ivt-still-passes-it.md)/[ADR-0699](adr-0699-a-derived-count-is-not-a-defended-one.md)'s
  two-axis dominance test, and
  [ADR-0675](adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md).
- **Files:** `crates/axeyum-lean-kernel/src/creal/sup_laws.rs` (new),
  `crates/axeyum-lean-kernel/src/creal/inventory/sup_laws.rs` (new),
  `crates/axeyum-lean-kernel/src/creal.rs` (field, name, build-step wiring).

## Decision

Land eight declarations characterizing `CReal.supOn`, and **do not claim EVT
dominance**, because the upper-bound law does not yet hold at an arbitrary
point of `[a, b]`.

All eight are admitted through `Kernel::add_declaration` with an empty axiom
footprint, verified by
`creal_tests::every_creal_declaration_is_checked_and_axiom_free`, which
enumerates `kernel.environment()` rather than a hand-maintained list. Every
one was a first-attempt kernel accept.

### The least-upper-bound half — complete

```
CReal.supOn_approx_lub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) (e : Nat),
  ∃ x, le a x ∧ (le x b ∧ le (supOn F a b hab u) (add (F x) (ofRat (Rat.natDivSucc 1 e))))
```

`supOn` is approached by values of `F` on `[a, b]`, to any requested accuracy,
at a point the proof exhibits. **It must stay approximate.**
`CReal.evt_attained_max_decides_sign` proves that an attaining maximiser would
decide the sign of an arbitrary real; that is EVT's row 2 and a genuine
impossibility result, not an unfinished proof. Nothing here produces an
argmax, and the point exhibited moves as `e` moves.

Two supporting declarations:

- `CReal.maxRange_attained_approx` — a finite maximum is approximately
  attained at one of its samples.
- `CReal.supSeq_le_shift` — every term of the sup sequence is within `1/2^k`
  of the `k`-th, in whichever direction.

### The upper-bound half — partial, and the partiality is precise

```
CReal.supSeq_le_supOn             : le (supSeq F a b u k) (supOn F a b hab u)
CReal.supOn_ub_at_supSeq_point    : i ≤ meshLevelCount (supLevel F a b u k)
                                    → le (F (sample i)) (supOn F a b hab u)
CReal.meshMax_le_supOn_add        : le (meshMax F a b (supLevel F a b u k + dd))
                                       (add (supOn F a b hab u)
                                            (ofRat (natDivSucc 1 (meshLevelCount k))))
CReal.supOn_ub_at_fine_mesh_point : i ≤ meshLevelCount (supLevel F a b u k + dd)
                                    → le (F (sample i))
                                         (add (supOn F a b hab u)
                                              (ofRat (natDivSucc 1 (meshLevelCount k))))
```

The last is the strongest: the refinement depth `dd` is free, so the sampled
points are not confined to the schedule's own levels and can be made as fine
as wanted, while `k` controls the error independently of `dd`.

What is NOT proved is `∀ x, le a x → le x b → le (F x) (supOn F a b hab u)`
for an arbitrary `x`.

## Why the least-upper-bound half is the CHEAP half

This is the finding most worth carrying forward, because it is the opposite of
what the sizing instinct says. "supOn bounds F above" sounds easy and "F
approaches supOn" sounds like attainment, so the second sounds hard.

- The approximate LUB law needs a point at which the FINITE mesh maximum is
  nearly attained. Deciding WHICH sample attains it needs a decidable
  comparison of reals; deciding which attains it *to within eps* needs only
  `lt_cotrans`. Its witness is then a MESH POINT, so
  `riemann_sample_in_bounds` already places it in `[a, b]`. **No mesh geometry
  enters the argument at all.**
- The upper-bound law needs an ARBITRARY `x` placed within one cell of some
  mesh point. `x` is not a mesh point and no computed index locates it, so
  that is a genuine cell-location argument plus a modulus step plus a limit
  passage.

## Two structural findings

**1. `supLevel`'s schedule has ZERO margin, which is why the fine-mesh bound
carries an epsilon.** `supLevel F a b u k = Nat.size (bound (b−a)) +
trueExpOfModulus m k` is exactly fine enough for the modulus at the
corresponding accuracy — enough for the mesh-to-mesh comparison, where points
coincide exactly, and with nothing left over for a point that is not on the
mesh. Consequently:

- `meshMax F a b j ≤ supOn` at an ARBITRARY `j` is not available, because
  nothing proves the schedule is cofinal in the levels: `trueExpOfModulus`
  accumulates `expOfModulus`, which is `0` whenever the modulus is, so a
  modulus that is eventually `0` — legitimate for a locally constant `F` —
  leaves the schedule bounded. `supOn_ub_at_supSeq_point` is therefore stated
  only at the scheduled levels, deliberately.
- The way around it is `meshMax_le_supOn_add`, which buys an arbitrary level
  ABOVE a scheduled one for one epsilon, because
  `mesh_max_le_add_of_modulus` is depth-uniform.

**2. Cell location is much cheaper stated over the ORDER alone.**

```
CReal.stepFamily_locate : ∀ (P : Nat → CReal) (w eps : CReal),
  le zero w → lt zero eps → (∀ i, le (P (Nat.succ i)) (add (P i) w)) →
  ∀ (n : Nat) (t : CReal), le (P Nat.zero) t → le t (add (add (P n) w) eps) →
  ∃ i, Nat.le i n ∧ (le (P i) (add t eps) ∧ le t (add (add (P i) w) eps))
```

Nothing in it mentions `meshDelta`, `meshSamplePoint`, `CReal.mul` or
`CReal.ofNat`. A draft that carried the mesh through the induction had to
re-prove `ofNat (succ i) · Δ ≈ ofNat i · Δ + Δ` inside every branch; this
version has no ring algebra in it at all, and the mesh-specific form becomes an
instantiation with three interface identities.

The non-obvious part of its proof: **the cotransitive split must be at the TOP
of the range under consideration, not at the point the inductive hypothesis
will be applied to.** Splitting at `P j` rather than `P (j+1)` makes the
winning branch's own bound come out at `2w` instead of `w`, because the
hypothesis is stated one step above the index being tested.

## Rejected: `CReal.splitPointApprox`

`creal/integral.rs`'s `splitPointApprox` is the closest existing lemma to cell
location and does not fit, for two independent reasons: its approximating
family is chosen EXISTENTIALLY rather than being the caller's mesh, and it
requires `PosBound (b − a)` — strict positivity of the width — which `le a b`
does not supply. Recorded here because it is exactly the shape a future lane
will find and try first.

## What remains, precisely

One declaration, `CReal.supOn_ub`, and the route is fully determined. In order:

1. **Instantiate `stepFamily_locate` at the mesh.** `P i := meshSamplePoint a Δ i`,
   `w := Δ := meshDelta a b (meshLevelCount j)`. Three interface identities:
   `le zero Δ` (re-derive `supremum.rs`'s private `mesh_delta_nonneg`);
   `Equiv (mul (ofNat (succ i)) Δ) (add (mul (ofNat i) Δ) Δ)` from `of_nat_add`
   at `b := 1`, `right_distrib` and `mul_one` (note `Nat.add i 1` is defeq to
   `succ i`, and `ofNat 1 ≈ one` needs `rat_unit_eq_one`, as
   `supremum.rs`'s private `of_nat_one_equiv` does it); and
   `a + (meshLevelCount j + 1)·Δ ≈ b` from `CReal.mesh_count_width` plus
   `add_neg`/`add_assoc`.
2. **Pick the level ABOVE the schedule.** Take
   `j := supLevel F a b u k + (Nat.size c + Nat.size outer2)` so that `j`
   dominates BOTH a scheduled level (for `meshMax_le_supOn_add`, whose `dd`
   comes from `Nat.le_dest` — an `Exists` into a `Prop`, which is permitted)
   and the threshold `mesh_level_count_ge_of_size` needs for the fineness
   `mesh_le_of_ge` will report.
3. **Absorb the locate epsilon into the modulus budget.** `stepFamily_locate`
   returns `|x − P i| ≤ Δ + eps`, and uniform continuity wants
   `≤ 1/(outer + 1)` exactly, with no slack. Split it: take
   `outer2 := succ (2·outer)` so `Δ ≤ 1/(2·outer + 2)`, and `eps :=
   ofRat (natDivSucc 1 outer2)`; the two halves fuse by `natDivSucc_add` then
   `natDivSucc_halve`. **This step is why the level in (2) must be chosen
   independently of the schedule** — the schedule alone gives exactly
   `Δ ≤ 1/(outer + 1)` and no more, which is not enough once `eps` is added.
4. **Apply `uc_spec` and close.** Copy `supremum.rs`'s
   `declare_mesh_max_le_add_of_modulus_thm` verbatim for the shape:
   `abs_le_of_two_sided` folds the two-sided bound into what `uc_spec`
   consumes, and `le_add_of_abs_sub_le` turns its output into
   `le (F x) (add (F (P i)) eps')`. Then `supOn_ub_at_fine_mesh_point` bounds
   `F (P i)`, and `le_of_forall_le_add_rate` closes over the accuracy index.

The rate bookkeeping at the end: `F x ≤ supOn + 1/(meshLevelCount k + 1) +
1/(n3 + 1)`; take `k := n3 := 2e + 1` and weaken `1/(meshLevelCount k + 1)` to
`1/(k + 1)` through `le_mesh_level_count` and `natDivSucc_antitone`, exactly as
`supSeq_abs_diff_le` does.

## Consequences for the dominance claim

**EVT remains ineligible**, and this ADR does not change ADR-0692/0699's
verdict. Under the two-axis test:

- *Trusted base*: `creal` stays at 0. Eight new declarations, all axiom-free.
- *Computational content*: improved but not sufficient. `supOn` is now a
  characterized supremum from below and an upper bound on a family that can be
  made as fine as wanted — but Mathlib's `IsCompact.exists_isMaxOn` bounds `F`
  at every point of the interval, and so must we before the statements are
  comparable.

The instrument-consistent measurement, `shape_search --include-constructed
--const CReal.supOn --kind theorem`: **6** theorem types now mention
`CReal.supOn`, five of them new in this lane, against a same-instrument control
of **18** for `CReal.integral`. (ADR-0691's "zero against 45" was measured with
a different instrument; the two numbers are not on the same scale and should
not be quoted as a before/after pair.)
