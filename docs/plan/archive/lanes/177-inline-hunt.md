# Lane: inline-hunt — census `creal/` for inline reusable proof steps (hiding place 2), extract the real ones

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, inline-hunt, 2026-08-28).** Censused ~426
`declare_*` functions and ranked ~333 private-fn candidates (body_len>=25)
across every in-scope `creal/` file, using: theorem-shaped `///` doc
comments on private (non-`declare_`) fns, "does not exist"/"not landed"
comments, structuring comments ("self-contained", "independently useful"),
and a body-length + call-site ranking script. Result: **every strong hit
this session's signals surfaced (clamp_id, bucketClose,
converges_upper_bound_shift, hasDerivative_closeOfEquiv,
congr_of_uniformly_continuous, uniformly_continuous_mul) was already
extracted by other lanes earlier today** — this campaign has been running
hard enough that the obvious hiding-place-2 instances are largely cleared.

What this lane actually landed instead: `CReal.abs_add_le` has been a
public kernel declaration (`uniform_continuity::declare_abs_add_le`) for a
while, but `series.rs`, `derivative.rs` (7 call sites) and
`deriv_unique.rs` (1 call site) each still carried a private
proof-term-rebuilding copy, and `uniform_continuity.rs` itself re-derived
it twice more beyond its own declaration's proof. All 10 call sites now
cite `d.lemma(p.abs_add_le, &[a, b])`; the 3 now-dead private copies
(`series.rs`'s also took its now-unused `neg_add` with it) are gone.
Also fixed a stale doc comment in `derivative.rs` (`hasDerivative_pow`)
claiming `uniformly_continuous_mul` "does not exist" — it has, publicly,
since `fb2c703a6`.

Verification: clean `cargo check`/`clippy -D warnings`;
`creal_prelude_builds` 94.01s (within the recent 94-123s band, no
regression); `every_creal_declaration_is_checked_and_axiom_free` passes
`--release` (declaration count unchanged — no new declarations, only
duplicate private builders removed).

**No new kernel declaration was extracted.** I did not find a genuinely
general, previously-un-named inline step within budget that clearly
warranted one — several large private fns ranked highly by the body-length
signal (e.g. `integral.rs`'s `bnd_leg_plus_share_le`, 161 lines / 13 call
sites) turned out to be tightly coupled to one declaration's own internal
plumbing (named parameters like `bound_at_idx`, `idx`, `m` specific to that
construction) rather than general facts another module would search for.
Next lane: the census signals that worked are logged in this session's
transcript; the remaining un-swept files are the largest ones
(`integral.rs` 29.5k lines, `derivative.rs`, `monotone.rs`, `ivt.rs`) —
worth another pass with fresh eyes rather than repeating my grep signals,
which are now mostly exhausted against what remains.

<!-- plan-section: landed-changes -->

| 2026-08-28 | `68e0a48d8` | dedup: cite `CReal.abs_add_le` instead of re-deriving it, in 4 `creal/` files; fix a stale "does not exist" doc comment <!-- was-absent: CReal.abs_add_le --> |
