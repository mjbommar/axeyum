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

1. **The level** — an arbitrary level ABOVE a scheduled one, made usable for
   one epsilon by `meshMax_le_supOn_add` (`mesh_max_le_add_of_modulus` is
   depth-uniform). This handles the mesh-maximum side.
2. **The accuracy the mesh is ASKED for** — `outer2 := succ (2·outer)`, one
   halving finer than the modulus itself demands, so `mesh_le_of_ge` reports
   `Δ ≤ 1/(2·outer + 2)` and the locate epsilon can be the same size. The two
   fuse to exactly the `1/(outer + 1)` `uc_spec` consumes. **No amount of extra
   LEVEL substitutes for this**, because the schedule's guarantee is stated at
   the accuracy you asked for.

The same halving runs a second time at the outer accuracy (`kk := succ (2·e)`)
to split the final `1/(e+1)` between the uniform-continuity transfer and the
mesh-maximum gap.

## The value/argmax distinction is untouched

No `argmax`-shaped declaration was added and none should be.
`CReal.evt_attained_max_decides_sign` proves an attaining maximiser would
decide the sign of an arbitrary real — a genuine impossibility result, not an
unfinished proof.

## EVT comparability — the honest verdict

**EVT is now ELIGIBLE for the per-statement dominance claim, and on the two
axes ADR-0692/0699 settled it passes.** Trusted base: `creal` stays at 0.
Computational content: `supOn` now carries both halves of the supremum
characterization, and the specific gap ADR-0710 named is closed.

**Two things still separate the statements**, and a referee must be told both:

1. **Our hypothesis is stronger.** `UniformlyContinuousOn F a b` versus
   Mathlib's continuity on a compact set. We do **not** have Heine–Cantor
   in-tree — measured, with a positive control, not assumed. This is not an
   oversight: Heine–Cantor is not constructively available, which is why
   Bishop-style analysis takes uniform continuity as the definition. The two
   developments quantify over different classes of input.
2. **Our conclusion is a bound, not an attained maximum**, permanently, by
   `evt_attained_max_decides_sign`.

So: EVT's supremum is now stated and proved here in a form comparable to
Mathlib's, axiom-free, with computational content Mathlib's does not carry —
under a stronger hypothesis and with a constructive rather than attained
conclusion. That is a per-statement comparison a referee can check. **It is not
a coverage claim and must not be quoted as one.**

## Next

The obvious follow-on is not more `supOn` machinery. It is to decide, at the
strategy layer, whether the hypothesis difference in (1) should be recorded as
a permanent axis of the comparison — the way breadth already is — rather than
as an open task, since no amount of work in this kernel removes it.
