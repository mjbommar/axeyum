# IVT has no row-2 theorem; EVT does (2026-08-29)

> **CLOSED the same day.** `CReal.ivt_exact_root_decides_sign` is a kernel
> declaration with axiom footprint 0 (`crates/axeyum-lean-kernel/src/creal/
> ivt_boundary.rs`, `F:creal-ivt-exact-root-decides-sign`): an exact root of the
> plateau family `x ↦ min x (max (x−1) v)` on `[0,1]` yields
> `Or (le v zero) (le zero v)`, the same analytic LLPO EVT's row derives. All
> three of classical IVT's hypotheses are proved beside it
> (`ivtPlateau_uniformly_continuous`, `ivtPlateau_nonpos_at_zero`,
> `ivtPlateau_nonneg_at_one`), which required two new general lemmas,
> `CReal.uniformly_continuous_max`/`_min`. The table below is therefore **stale
> in the row that matters** — IVT's row 2 is a `declaration`, not a Rust test —
> and this note is kept for the distinction it draws between a claim about
> ALGORITHMS and a claim about the STATEMENT, which is still exactly right and
> is why `ivt.rs`'s two counterexamples were left untouched rather than
> superseded. Everything below is the diagnosis as it stood before the fix.
> Lane handoff: `docs/plan/status/249-ivt-row-two.md`.

**Measured, with a positive control, at `fedc6c70b`.**

ADR-0603 says a classical theorem lands as a **graded statement family**: row 1
the general constructive form, **row 2 the boundary/unprovability witness**, row
3 the decidable-fragment exact form, row 4 a labeled import. The
2026-08-28 Pareto review names row 2 as the strongest uncontested axis against
Mathlib — *"Row 2 has no counterpart at all. Mathlib does not carry a
machine-checked statement of where the classical form fails."*

**EVT's row 2 is a kernel theorem. IVT's is not, and the two are different
species.**

| family | row 2 | kind |
| --- | --- | --- |
| EVT | `CReal.evt_attained_max_decides_sign` (`creal.rs:5615`) | **declaration** in `kernel.environment()` |
| IVT | `ivt_bisect_diag_reduces_on_the_identity_bracket_neg_one_two` (`creal_tests.rs:6225`) | **Rust test** |

EVT's says an attained maximum of `t ↦ t·v` on `[0,1]` yields `∀ v, v ≤ 0 ∨ 0 ≤
v` — a decision principle this kernel lacks (`lt_total` is absent from the
environment, confirmed by the same inventory). A referee reads that off the
kernel in one command.

## What IVT actually has, stated precisely

Not a weaker version of the same thing — **a different claim**. `ivt.rs`'s diary
records two kernel-verified counterexamples on `F := id` over `[-1,2]`, and both
close off a *specific construction route*, not the theorem:

1. The shrinking-slack-folded-into-one-recursion diagonal converges to `L = 1/2`
   rather than the true root `0`, because the stationary endpoint keeps whatever
   bound justified its last move and is never retested at a tighter threshold.
2. The fresh-run-at-slack-`k` reading gives brackets that are not nested — at
   `k=3` it is `(1/8, 1/2)`, at `k=4` it is `(-1/16, 1/8)`, disjoint interiors,
   so no shared refinement exists for a limit argument.

That is honest and valuable, and the file is explicit that it *"stops there — no
invariant/exactness theorem is attempted, because none holds."* But "these two
natural algorithms fail" is a claim about **routes**, whereas row 2 is a claim
about the **statement**. The 2026-08-28 review called IVT's a "kernel-computed
reduction test", which is accurate and still flattens this distinction: the two
rows are not the same species and should not be counted as if they were.

## The row-2 statement for IVT is already written, in prose

`ivt.rs:8-15`:

> Classical IVT (`f` continuous on `[a,b]`, `f a ≤ 0 ≤ f b` ⟹ `∃ x, f x = 0`)
> asserts a *computable* root, and no algorithm produces one in general:
> deciding which side of the root a candidate point falls on is exactly as hard
> as deciding the sign of an arbitrary real.

That is the reduction, argued informally. EVT's counterpart used to be prose
too, and was closed on 2026-08-28 when `evtLinear_uniformly_continuous` landed
and stopped the counterexample family resting on the reader knowing an affine
map is Lipschitz. IVT's has not had that treatment.

## Why this is worth doing rather than noting

The headline Pareto claim rests hardest on row 2, because it is the one axis
with **no Mathlib counterpart at all** — not a better version of an existing
row, a capability class. A row 2 that is a passing Rust test is weaker evidence
than one that is a declaration with an axiom footprint a referee can read, and
the difference is exactly the difference this repository insists on everywhere
else: read the metric from the kernel, never from a test having been run.

It is also the cheaper half of the two open Pareto gaps. The other — that
`ivt_exact_root` carries a uniformly-positive-derivative hypothesis Mathlib's
statement does not — is a genuine mathematical boundary, not an engineering
one, and closing it is not on the table.

## Related

- `docs/research/11-design-review/2026-08-28-ivt-evt-pareto-position-measured.md`
- ADR-0603, classical theorems as graded statement families.
