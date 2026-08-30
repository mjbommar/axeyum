# Notes: 158-ftc-rung3

Detail moved out of [`../status/158-ftc-rung3.md`](../status/158-ftc-rung3.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The `min x y` common-base-point route worked exactly as characterised, with
one arithmetic correction.** `|A − B| ≤ ε·((y−m) + (x−m))` is bounded by
`2ε·(max x y − m)`, not by `ε·(max x y − m)`: collapsing the sum of the two
widths to `max − min` would need `max x y + min x y ≈ x + y`, which is a
*fifth* absent lemma. Bounding each width by `max − min` separately is free
and costs only a factor of two, so `ε := 1/(2E+2)` and the witness's modulus
is `λ E ↦ modulus F a b u (2E+1)`; the two halves fuse by
`Rat.natDivSucc_halve`, which is exactly what Bishop's shift is for.

**The `PosBound` removal went through, and the file's own cost estimate was
wrong in the cheap direction.** `integral.rs` said the `lt_cotrans` split
"has to be run at EVERY accuracy, so the `PosBound`-hypothesised theorem is
applied inside the split with a `k` that changes per accuracy, and
`integral`'s own value must then be shown independent of that choice",
naming `inv_index_irrelevant` as "the ONLY thing standing between this
theorem and an unconditional one". **`CReal.integral` takes no `k`** — only
the proof does — so the conclusion mentions neither `k` nor the witness, the
positive branch of the cotransitivity split yields the WHOLE `Equiv`, and the
accuracy loop ends there. `inv_index_irrelevant` is unused. The general form,
now recorded in that file: *before pricing a hypothesis-removal, check
whether the hypothesis appears in the CONCLUSION.*

**No endpoint congruence of `integral` was needed** — a real risk the chosen
route avoids. `clamp_id` is used only in the ALGEBRA (`clamp y − clamp x ≈
y − x`), never to move an integration endpoint, so the quantitative
`integralEndpointClose` never has to be promoted to an exact `Equiv`.

**Retrieval, again: everything the assembly needed was already in
`integral.rs`.** `neg_add_local`, `neg_neg_equiv_local` and
`add4_swap_middle` (reachable but unconsumed until now) carry the whole
four-term regrouping; `derivative.rs`'s `mul_neg_equiv` is the right-factor
negation move and was made `pub(super)` rather than copied a sixth time
(`fermat.rs`, `deriv_unique.rs`, `uniform_continuity.rs` and `mvt.rs` each
keep a private copy of the same statement). `crossing.rs`'s
`le_sub_of_le_add` / `le_add_of_le_sub_right` are the `le`-transposition
steps `max_sub_min` needs, likewise shared rather than copied.
`bounded_of_uniformly_continuous` turned out not to be needed at all:
`CReal.BoundedOn` is a transparent `Definition`, so restricting it to a
sub-interval is one lambda.

**What the kernel rejected: nothing.** Six declarations, six first-attempt
accepts. The only build failures were Rust's — one `unused_mut`, two unused
locals, and one `carrier_of` typo.

**Timings** (all foreground, `env -u RUST_MIN_STACK`, load not isolated):
`creal_prelude_builds` 89.0 s after the lattice extras, 99.2 s after
`integralSplitAnywhere`, 95.4 s with FTC-I and the whole lane's work in — no
multiple, so none of this file's documented concrete-witness / lazy-delta
traps applies. `every_creal_declaration_is_checked_and_axiom_free`
(`--release`) 14.6 s, green: all seven new declarations are in
`kernel.environment()`, of the kind claimed, with an empty axiom footprint.
New tests: lattice extras 93.7 s, degenerate-interval split 92.9 s, FTC
statement + modulus 107.4 s. `clippy --all-targets --all-features -D
warnings` green.
