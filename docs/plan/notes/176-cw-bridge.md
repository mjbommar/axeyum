# Notes: 176-cw-bridge

Detail moved out of [`../status/176-cw-bridge.md`](../status/176-cw-bridge.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

    CReal.sharedIndexToCanonical : ∀ (X Y : CReal) (bound : Nat → Rat),
      (∀ i, Within (seq (add X (neg Y)) i) (bound i)) → ∀ p q j : Nat,
      Within (Rat.sub (seq X p) (seq Y q))
             ((modulus p (shift j) + bound j) + modulus (shift j) q)

filed in `creal/integral.rs` because `riemannSum_cauchy` needed it first, and
`CReal.cauchy_of_abs_diff_le` (`creal/ivt.rs`, filed there because the exact
IVT root needed it first) already demonstrates the exact composition —
`le_abs_self`/`neg_le_abs` → `within_of_two_sided_le` → `sharedIndexToCanonical`
→ rational fold — for `Cauchy`. Neither is findable by name from
"`close_within` → `Converges`". Both were found by searching for the STEP.

## The construction, and why it is SMALLER than the Cauchy sibling

267 lines, one function, **zero new private helpers**
(`declare_converges_add` is 334 lines *plus* `shift_regular_bound`,
`telescope_le4`, `fuse_bridge_bound`, `regroup_middle_four`). Route:

1. `le_abs_self`/`neg_le_abs` + `le_trans` split the hypothesis at `n` into
   the two one-sided reals `within_of_two_sided_le` wants.
2. `within_of_two_sided_le` gives `∀ i, Within (seq (f n − L) i) (q + 2/(i+1))`
   at an arbitrary SHARED index, `q := natDivSucc K n`.
3. `sharedIndexToCanonical` at `p := q := n`, `j := 3n+2`, `sj := 2j+1`:

       ((1/(n+1) + 1/(sj+1)) + (q + 2/(j+1))) + (1/(sj+1) + 1/(n+1))

   `Rat.natDivSucc_halve j` collapses the two `1/(sj+1)` legs to `1/(j+1)`,
   `Rat.natDivSucc_add` fuses that with the `2/(j+1)` slack to `3/(j+1)`, and
   `Rat.natDivSucc_scale 2 n` makes `3/(j+1)` **exactly** `1/(n+1)`.
4. Three more `Rat.natDivSucc_add` fusions on `q + (A + (A + A))` reach
   `natDivSucc (K+3) n`. Witness `K := Nat.add K 3`, reported raw.

**The whole six-term bound is an EQUALITY.** `cauchy_of_abs_diff_le`'s two
canonical indices `m`/`n` differ, so it ends with a
`Rat.natDivSucc_le_add_left` widening to a shared numerator; there is exactly
one index here, so **this proof contains no inequality anywhere**. The
six-summand rearrangement goes through `rsum_perm` (panics on a
non-permutation) rather than an inline `add_assoc`/`add_comm` chain.

## Was the `n = 0` obligation the crux? No — and that is a real finding

175/174 recorded that an "eventually" bridge would not do, because
`Converges` constrains every index including `n = 0`, and that the
shifted-series route was **blocked** there (re-indexed partial sums satisfy
their identity only for `n ≥ 1`). That is true of the shifted-series route
and **does not transfer to this one**: every step above is an identity in
`n`, so `n = 0` is simply the instance where all four denominators are `1`
and the bound reads `K + 3`. Nothing is chosen eventually, nothing is assumed
about `n`, and no clamp (`Nat.pred`-style or otherwise) appears. The low-index
obligation cost zero.

## What the kernel rejected

**Nothing.** `add_declaration` accepted on the first attempt — no
`TypeMismatch`, no `UnboundFVar`, no `on_a_deep_stack` needed, no `def_eq`
budget trouble. The only rejection in the lane was `clippy`'s
`items_after_statements` on a nested `fn` in the new test (moved above the
statements).

## Non-vacuity: the bridge composes with `UniformConvergesOn.spec`

That the declaration type-checks does not establish that its hypothesis is
the shape a consumer HAS. New test
`creal_tests::the_close_within_bridge_turns_uniform_convergence_into_converges_at_a_point`
builds the composed term outright —

    λ F G a b (u : UniformConvergesOn F G a b) x (hax : le a x) (hxb : le x b),
      converges_of_abs_diff_le (fun n => F n x) (G x)
        (UniformConvergesOn.rate F G a b u)
        (fun n => UniformConvergesOn.spec F G a b u n x hax hxb)

— and asserts `Kernel::infer` of it is EXACTLY `… → Converges (fun n => F n x)
(G x)`, by interned id, never `def_eq`. It passes, so `.spec`'s per-index
`close_within` **is** the hypothesis with no transport at all, and the
family's own `rate` serves as `K` directly. Negative control differs in a
small term (`le a x` transposed) and is asserted non-vacuous both ways.

## What this unblocks

π rung 2 item 3: `alternatingUpperBoundTail`'s remaining `Converges (sumRange
t) L` hypothesis. `riemannSum_cauchy` was separately noted as wanting a lemma
of this family — note it wants the `Cauchy` one, which already exists as
`cauchy_of_abs_diff_le`; both halves of that pair are now public.

## Verification (all foreground, all completed)

- `cargo test -p axeyum-lean-kernel --lib creal::creal_tests::creal_prelude_builds`
  — **96.39 s green**, 1 passed / 921 filtered; inside 175-pi-r2b's own
  94–123 s band. One reading, not isolated from host load.
- `cargo test --release … every_creal_declaration_is_checked_and_axiom_free`
  — **green, 16.86 s**. Environment-derived, both directions.
- `cargo test --release … steps_table_matches_recorded_extraction` — green.
- `cargo test --release … the_close_within_bridge_turns_uniform_convergence_into_converges_at_a_point`
  — green, 14.49 s, 1 passed / 922 filtered (nonzero, and the count moved).
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings`
  — clean.
- NOT run: the full `--lib creal::` sweep, and any workspace gate.
