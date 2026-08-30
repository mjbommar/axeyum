# Notes: 161-inverse-fn

Detail moved out of [`../status/161-inverse-fn.md`](../status/161-inverse-fn.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Chosen because (a) it was verifiably NOT yet landed (no `root_at`/`Surjective`
name anywhere in `creal.rs`, checked before starting), (b) it is exactly
`ivt.rs`'s `ivt_exact_root` (which already exists, at `y = 0`) generalized to
an arbitrary target `y` in the image interval, so no new estimate or
bisection argument was needed, and (c) rung 3 (`HasDerivativeOn` for the
inverse) was flagged in the brief as likely the hardest and needing sizing
first — this rung sizes to "a wrapper," which is the accurate size.

**Not a re-derivation of `ivt_exact_root`.** It applies that theorem to the
shifted function `G := fun z => F z − y`, whose zero set is `F`'s
`y`-preimage: `HasDerivativeOn`/`UniformlyContinuousOn` for `G` come from
`hasDerivative_sub`/`uniformly_continuous_sub` composed with
`hasDerivative_const`/`uniformly_continuous_const` at `y` (a constant shift
changes neither continuity nor the derivative), `G a ≤ 0 ≤ G b` is
`add_le_add`/`add_neg` shifting `F a ≤ y ≤ F b`, and the derivative-bound
hypothesis on `F'` transports to `G'` through the ring identity
`F' z ~ F' z − 0` (`add_zero` plus `monotone.rs`'s private `neg_zero_equiv`,
via `le_congr`). `ivt_exact_root`'s result `Equiv (G c) zero` reads back as
`Equiv (F c) y` via `monotone.rs`'s `equiv_of_sub_equiv_zero`, which already
existed there for an unrelated purpose (`declare_inverse_lipschitz_of_pos_deriv`)
and is reused unchanged.

**`inverse_lipschitz_of_pos_deriv`'s `Apart` hypothesis was not needed on
this route at all** — `ivt_exact_root_at` never uses that lemma; it composes
`ivt_exact_root` (which needs the same uniformly-positive-derivative bound
`ivt_exact_root_at` also takes, but no `Apart`) with pure ring/order algebra.

**Kernel result: accepted, `CReal.ivt_exact_root_at` added via
`Kernel::add_declaration` (Theorem)**, confirmed by
`creal::creal_tests::creal_prelude_builds` (the whole prelude, symbolic
throughout — no concrete-`Nat` partial evaluation in this proof, so the
"concrete instantiation can hide a bug a symbolic one exposes" risk from
`CLAUDE.md` does not apply the same way here: the declaration IS the fully
general symbolic statement, and that is what the kernel checked). Also
confirmed by `every_creal_declaration_is_checked_and_axiom_free --release`
(environment-derived coverage, both directions) and `cargo clippy
--all-targets --all-features -- -D warnings` on `axeyum-lean-kernel`, both
green.

**One kernel rejection during development, fixed and recorded in the commit
message**: the first attempt passed `equiv_refl` for `add_le_add`'s second
premise (`le neg_y neg_y`), which needs `le_refl` — `Equiv` and `le` are
different props (the exact `le_congr` family gotcha `CLAUDE.md` already
documents), and the kernel's `TypeMismatch` named the fully unfolded `Equiv`
definition rather than the two propositions directly, which is what made it
take a moment to place. Fixed by swapping in `p.le_refl`; second attempt
accepted.

**Also landed**: promoted `monotone.rs`'s private `cneg`/`czero`/`erefl`/
`esymm`/`echain`/`neg_zero_equiv`/`equiv_of_sub_equiv_zero` to `pub(super)`
so `inverse_fn.rs` reuses them (both files are mine this session) instead of
adding a ninth per-file duplicate of the same ~10-line ring helpers this
repository already has eight copies of. `cexists_ty`/`cexists_intro`/
`cexists_elim` (the `Exists`-over-`CReal` builders) are copied verbatim from
`ivt.rs`'s private originals — `ivt.rs` is out of scope for this lane (an IVT
lane owns it), so promoting them there was not an option; this is the same
per-file-duplicate convention every other `creal/` module already follows for
this exact helper shape.

**Wiring**: `creal.rs` field `ivt_exact_root_at` + name registration +
`BuildStep` (placed after `ivt::declare_ivt`, which declares
`CReal.ivt_exact_root` — the phase-order checker in `creal_tests.rs`
caught a first placement attempt right after `order_reflect_of_pos_deriv`,
before `ivt::declare_ivt` had run, with a precise "move X before/after Y"
message; moved and re-ran clean); `creal_tests.rs` `EXPECTED_STEP_ORDER`
moved to match; `creal/inventory/inverse_fn.rs` shard entry added.

**Timing**: `creal_prelude_builds` 88.34s (debug, within the brief's
documented 55–111s-and-growing range for this point in the chapter).
`every_creal_declaration_is_checked_and_axiom_free --release`: 14.91s.

**What the chapter needs next, sized**:

- **Rung 3, `HasDerivativeOn` for the inverse function** (the
  differentiability half) — NOT started, and still the hardest of the three.
  Needs: a term-level construction of the inverse function itself (this
  session's `ivt_exact_root_at` gives EXISTENCE of a preimage per `y`, via an
  `Exists`, not a `Nat → CReal`-style total FUNCTION term usable as an
  argument elsewhere — the same `Exists`-into-`Type` obstruction
  `ivt_exact_root`'s own module doc records for the forward IVT case would
  need to be worked out again here, likely via the SAME uniqueness-with-a-
  modulus trick `ivt_exact_root` itself uses, since `order_reflect_of_pos_deriv`
  gives uniqueness of the preimage under a given `Apart`), then the
  derivative FORMULA `(F⁻¹)'(y) = 1/F'(F⁻¹(y))` and its Lipschitz-rate proof
  via `inverse_lipschitz_of_pos_deriv` composed with `CReal.inv`
  (`creal/inverse.rs`, the *other* file this session's audit clarified).
  Size this properly (probably multiple sessions) before starting; do not
  force it in one sitting.
- A natural companion, smaller: package `ivt_exact_root_at` +
  `order_reflect_of_pos_deriv` + `strict_injective_of_pos_deriv` into a single
  "F is an order isomorphism `[a,b] → [F a, F b]`" statement, if a downstream
  consumer wants one. Not built this session — no consumer asked for it yet,
  and the three pieces are individually usable as-is.
