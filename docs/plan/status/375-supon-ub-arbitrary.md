# Lane 375 — `CReal.supOn_ub` at an arbitrary point

<!-- plan-section: lane-status -->

**Status: LANDED.** `CReal.supOn_ub` is admitted, axiom-free, first-attempt
kernel accept. ADR-0733.

```
CReal.supOn_ub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) (x : CReal),
  le a x → le x b → le (F x) (supOn F a b hab u)
```

This is the one declaration ADR-0710 named as remaining between `CReal.supOn`
and comparability with Mathlib's `IsCompact.exists_isMaxOn`. With
`CReal.supOn_approx_lub` it is the pair that characterizes `supOn` as a
supremum: an upper bound at every point of `[a, b]`, and approached to any
requested accuracy at an exhibited point.

## Measured

| check | result |
| --- | --- |
| `creal_prelude_builds` before | **110.54 s** |
| `creal_prelude_builds` after | **110.00 s** (flat) |
| `cargo test -p axeyum-lean-kernel --lib creal::` | **201 passed, 0 failed** |
| `every_creal_declaration_is_checked_and_axiom_free` | passes — reads `kernel.environment()`, so `CReal.supOn_ub` is a `Theorem` with an empty axiom footprint |
| `cargo fmt --all --check`, clippy `-D warnings` on this crate | clean |

The flat prelude build matters: none of the defeq traps this development has
accumulated (a `Definition` forced to unfold, a concrete witness driving
partial evaluation) was tripped.

## ADR-0710's four steps: three held, one drifted CHEAPER

The route in ADR-0710 was accurate and was followed. The one drift is in our
favour:

- **Step 2** predicted the refinement depth `dd` would come from `Nat.le_dest`,
  "an `Exists` into a `Prop`, which is permitted". It does not have to.
  Choosing `j := supLevel F a b u kk + (Nat.size c + Nat.size outer2)` makes
  `dd` **concrete**, so the obligation reduces to
  `Nat.le dd (Nat.add level dd)` and **no existential is eliminated anywhere in
  the proof**. One summand satisfies both consumers at once.
- Steps 1, 3 and 4 held verbatim, including the arithmetic in step 3.
- Step 1's three interface identities were exactly what was needed and no more.
  Two are re-derivations of `creal/supremum.rs` private helpers
  (`sample_zero_equiv`, `sample_succ_equiv`); `mesh_endpoint_equiv`
  (`P N + Δ ~ b`) is new. Worth knowing:
  `creal/monotone.rs`'s `subdivisionPoint_in_bounds` already runs those same
  three steps but lands a `le` rather than an `Equiv`, so it could not be
  reused — only the shape could.

## Where the margin came from, since `supLevel` has none

`supLevel`'s schedule is exactly fine enough for the modulus at the
corresponding accuracy, which is why an off-mesh point cannot reuse it. The
margin is bought in **two independent places, neither of which is a scheduled
level**, and they are not interchangeable:

Detail moved to [`../notes/375-supon-ub-arbitrary.md`](../notes/375-supon-ub-arbitrary.md).

