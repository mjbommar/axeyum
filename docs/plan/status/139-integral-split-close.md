# Lane: split-close — closing `CReal.integral_split` (the assembly)

<!-- plan-section: lane-status -->

**`CReal.integral_split` did NOT close this session (`WIP`, split-close,
2026-08-27), but the one missing prerequisite landed and is kernel-verified.**
Ten-plus lanes have now worked this exact fact; this session confirmed
`riemannSum_split_exact_of_uc` and `riemannSum_integral_close` (the two
estimates the assembly needs) were already landed by prior lanes, built the
one piece that was not — `CReal.uniformlyContinuousOn_restrict` (sub-interval
restriction of a `UniformlyContinuousOn` witness, `uniform_continuity.rs`,
same modulus, `le_trans` composition of the range hypotheses) — and then
characterized precisely why the final estimate assembly still does not close,
recorded as a new dated entry in `creal/integral.rs`'s module documentation
(the file's own established convention for this fact).

**The blocker, in one sentence**: `riemannSum_integral_close`'s bound routes
through `riemannSum_shared_accuracy_close`, whose shared mid-anchor sample
point `l` is baked into the statement rather than exposed as a free
parameter (unlike the more primitive `shared_index_to_canonical`, which
`riemann_sum_deep_cauchy` uses instead) — but `l` still shrinks to zero via
`depth` regardless of `u`'s own modulus, and the other opaque term
(`total_eps_sample_le`) generalizes mechanically to an independent
accuracy/sample-index pair. Full recipe is in `integral.rs`'s own doc (search
"a TENTH lane"); no new mathematics, but roughly the volume of
`bnd_leg_plus_share_le` (~150 lines) done three times and combined, not
attempted here to avoid landing a half-built, currently-unverifiable estimate
chain.

**Verification of what DID land**: `uniformlyContinuousOn_restrict` is in
`creal/inventory/uniform_continuity.rs`'s shard;
`every_creal_declaration_is_checked_and_axiom_free` passes (theorem kind,
empty axiom footprint); `creal_prelude_builds` unaffected (32.5s, within the
32–38s baseline band, both measured this session).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `f9dee8754` | `CReal.uniformlyContinuousOn_restrict` — the sub-interval `UniformlyContinuousOn` restriction `integral_split`'s assembly needs; same modulus, `le_trans`-composed range hypotheses, kernel-checked. |
| 2026-08-27 | `31aea5551` | docs(integral): pin down exactly what estimate work remains to close `integral_split` — the `l`-shrinks-via-`depth` lever and the `total_eps_sample_le` generalization, so the next lane does not re-derive this. |
