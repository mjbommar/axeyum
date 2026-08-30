# Notes: 168-supon5

Detail moved out of [`../status/168-supon5.md`](../status/168-supon5.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
