# Lane: supon5 — `CReal.supOn`, rung 5 onward (accuracy-selection scheme)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, supon5, 2026-08-27).** Rung 5 of `supOn`'s route
2 (nested-refinement) landed: `CReal.expOfModulus`/`CReal.trueExpOfModulus`,
the accuracy-selection schedule the module doc's plan called for, all
five declarations kernel-verified first-attempt. `supOn` itself (rungs
6-7: telescope via `sumRange_cauchy_of_dominated` against a concrete
ratio-1/2 geometric dominator, then `regular_of_scaled_cauchy` -> `CReal.mk`)
is **not** landed this pass — see `creal/supremum.rs`'s own module doc,
which now records rung 5 as done and rungs 6-7 as the next concrete task,
same characterization as before this session (unchanged; not re-verified
against rung 5's actual construction).

What landed, precisely:
- `CReal.expOfModulus : (Nat -> Nat) -> Nat -> Nat := fun m k => Nat.size (m
  (meshLevelCount k))` — generic over the modulus `m` rather than tied to a
  specific `UniformlyContinuousOn` witness (callers apply it at `m :=
  UniformlyContinuousOn.modulus F a b u`).
- `CReal.trueExpOfModulus : (Nat -> Nat) -> Nat -> Nat`, `Nat.rec`-structured,
  `trueExpOfModulus m 0 := expOfModulus m 0`, `trueExpOfModulus m (succ k) :=
  add (trueExpOfModulus m k) (expOfModulus m (succ k))` — built with
  `Nat.add` (this kernel's `Nat` prelude has no `Nat.max`), plus its two
  defining equations (`_zero`, `_succ`, both `Eq.refl`).
- `CReal.trueExpOfModulus_step_le` (adjacent step, `Nat.le_add_right`
  directly, defeq to the `_succ` equation's RHS) and `_mono` (general
  monotonicity via `Nat.monotone_of_le_succ`, the `Nat`-level twin of
  `CRealPrelude::mono_of_le_succ`, exactly `meshMax_mono`'s own
  construction one type down).
- `CReal.expOfModulus_le_trueExpOfModulus : forall m k, Nat.le (expOfModulus
  m k) (trueExpOfModulus m k)` — the accumulator is always at least as fine
  as the single level it covers; needed by rung 6. Proved by `NatOps::induct`
  (mirrors `declare_max_range_self_le`); the step case needs `Nat.le_add_right`
  read through `Nat.add_comm` via `rat_prelude::ops::nat_rewrite_prop`, since
  this kernel's `Nat` prelude has no `Nat.le_add_left`.

**The harmonic-vs-summable finding held as characterized, but was not itself
re-derived this pass** — rung 5 builds the SCHEDULE (`expOfModulus`,
`trueExpOfModulus`) and its two structural facts (monotone, `>=` the single
level); it does not yet touch mesh points or the per-level gap bound, which
is rung 6's job. So "does requesting `meshLevelCount k` fix the harmonic
trap" is not yet empirically checked against the actual telescoped sum —
that check happens when rung 6 applies `sumRange_cauchy_of_dominated`.

`geomCauchyBodyOfGap` (mentioned in the brief as new this session) was not
consulted or needed for rung 5 — it's a rung 6 tool (raw ordered-half Cauchy
witness at a general ratio). Not yet evaluated whether it changes the
telescoping route from what the module doc's plan describes.

**What the kernel rejected: nothing.** All five declarations were
kernel-verified on the first attempt (`creal_prelude_builds`: 90.48 s, `full
--lib` this run; within the documented 92-117 s recent range).
`every_creal_declaration_is_checked_and_axiom_free` (`--release`): 13.95 s,
green — all seven new declarations covered, axiom-free.
`steps_table_matches_recorded_extraction` and
`existing_step_order_is_topologically_valid`: both green (94.04 s for the
latter). Clippy `-p axeyum-lean-kernel --lib --all-targets -D warnings`:
clean.

**Honest next rung, with its obstacle named:** rung 6, the telescope. Needs
one piece the module doc flags as not-yet-confirmed-to-exist-by-name: a
constant-multiple corollary scaling a Cauchy bound by a fixed positive
`CReal` constant (to combine `geometric.rs`'s ratio-1/2 tail bound with the
per-level `1/2^k` gap this rung's `exp_of_modulus_le_true_exp_of_modulus`
plus `Nat.lt_pow_size` supply). That corollary is the concrete next task;
everything upstream of it (the accuracy schedule, its monotonicity, its
lower bound) is now landed and kernel-verified.

<!-- plan-section: landed-changes -->

| 2026-08-27 | supon5 | `CReal.expOfModulus`/`trueExpOfModulus` (supOn rung 5, accuracy-selection schedule) — 5 declarations, all kernel-verified, all axiom-free |
