# Lane: supon6 — `CReal.supOn` rung 6, re-verifying the telescope plan

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, supon6, 2026-08-27).** No new kernel
declarations landed this pass. What landed is a corrected module-doc map of
`creal/supremum.rs`'s rung 6 — the coordinator's brief flagged the existing
sketch as written by a lane that "did not attempt it" and asked to treat it
as a hypothesis; it does not hold up, and the doc now says precisely why,
with two named candidate routes for whoever attempts rung 6 next.

**The "constant-multiple corollary" the old sketch names as the one open
piece is not the bottleneck.** It already exists in substance:
`geometric.rs`/`exponential.rs`/`trig.rs`'s `pub(super)`
`mul_ordered_half_body` + `promote_ordered_half_to_full` +
`telescope_cauchy_pad2` already scale an ordered-half Cauchy bound by a
fixed positive `CReal` constant and promote it past `Nat.le_total`, and
`CReal.cauchy_of_abs_diff_le` (`creal/ivt.rs`) already supplies the general
real-bound-to-canonical-sample bridge `regular_of_scaled_cauchy` needs, with
a RAW `(K, proof)` pair available from its own construction (the body,
before the final `cexists_intro`) — this development's standing convention
is to reproduce a sibling's private helper rather than widen its visibility
for one caller, so this is a reproduction task, not a derivation.

**What actually blocks rung 6, verified against the kernel's own declared
recursion this pass (not yet attempted as a proof): the per-level GAP BOUND
between `f_lambda(k) := meshMax F a b (trueExpOfModulus m k)` and
`f_lambda(k+1)`.** `trueExpOfModulus`'s accumulator
(`trueExpOfModulus m (succ k) := add (trueExpOfModulus m k) (expOfModulus m
(succ k))`, landed at rung 5) can jump the mesh level by an unboundedly
large number of doublings between consecutive `k` — `expOfModulus m (succ
k) := Nat.size (m (meshLevelCount (succ k)))` depends on the continuity
modulus `m`, which this file is generic over and which can grow arbitrarily
fast. So the needed bound is **not** "adjacent mesh levels differ by
`≤ 1/2^k`" (that case is cheap — `mesh_sample_transport`'s exact even-index
coincidence, already landed at rung 3) but a genuine multi-level
nearest-point argument at ANY refinement depth. That is exactly the shape of
problem `uniform_continuity.rs`'s `bucketIndex`/`crossingClose` family
exists for — the module doc's own "route 1", already on record as rejected
for cost. Re-reading `CReal.crossing_close`'s field doc this session shows
it is not even a free reuse on its own terms: its `samplePt ≤ b` domain
hypothesis is recorded there as **still open**, independently discovered
and refuted-by-worked-example across five of `integral.rs`'s own
2026-08-27 module-doc entries. So route 1 would import an open gap, not a
finished lemma, and route 2 (nested-refinement) does not avoid an
index/bucket-style argument after all — it only avoids one for a single
adjacent doubling, not for `trueExpOfModulus`'s necessarily-multi-level
jumps.

**Two candidate routes are now documented in `supremum.rs`'s module doc,
neither attempted:** (1) bound the whole multi-level jump with ONE
continuity application at the coarse level, using that binary-doubling
refinement never leaves its parent cell (still needs a bounded "which
coarse cell" index computation `mesh_sample_transport`'s exact identity
does not supply past one doubling); (2) a double telescope — bound each
single adjacent-level step (cheap, already-landed machinery) by a per-step
accuracy that itself decreases geometrically across the unboundedly-many
intermediate levels within one `k`-to-`k+1` block, sum that inner series,
then sum the outer series as originally planned (needs a finer-grained
intermediate accuracy schedule than `expOfModulus` supplies today). Both
are comparably sized to a rung of their own, not "a short derivation."

**Does the `meshLevelCount k` schedule fix the harmonic-vs-summable trap?**
Mathematically yes, in the sense that matters for summability: the
REQUESTED accuracy `1/2^k` is summable (rung 5's
`expOfModulus_le_trueExpOfModulus` plus `Nat.lt_pow_size` already establish
this against the kernel). What is still unverified against the kernel is
whether that requested accuracy is actually ACHIEVED by `meshMax`'s own
value at the corresponding level — that is exactly the gap bound above, and
it remains unattempted.

**What the kernel rejected: nothing — no new declarations were submitted
this pass.** Rungs 1–5 (all prior sessions' work) are untouched.

**Verification (doc-only change, confirming nothing regressed):**
- `creal_prelude_builds` (`--lib`, debug, `RUST_MIN_STACK` unset): 100.93s —
  within the documented 90–117s recent range.
- `every_creal_declaration_is_checked_and_axiom_free` (`--release`): 26.88s,
  green.
- `steps_table_matches_recorded_extraction`: green (no `BuildStep`/inventory
  changes this pass, so this is expected, not new evidence).
- Clippy `-p axeyum-lean-kernel --lib --all-targets -D warnings`: clean.
- Did NOT run a full `--lib creal::` sweep, per the brief.

<!-- plan-section: landed-changes -->

| 2026-08-27 | supon6 | `creal/supremum.rs` module doc: corrected rung 6's plan — the "constant-multiple corollary" already exists (`mul_ordered_half_body`/`promote_ordered_half_to_full`/`cauchy_of_abs_diff_le`); the real blocker is an unattempted multi-level nearest-mesh-point gap bound, documented with two candidate routes. No new kernel declarations. |
