# ADR-0691: `CReal.supOn` lands, so EVT has a row 1 — but not yet the laws that make it a supremum

Status: accepted
Date: 2026-08-30
Index-summary: `CReal.supOn` is in the environment, derived and axiom-free,
with `CReal.supSeq_converges_supOn` tying it to the mesh maxima it is built
from. This answers ADR-0675's "EVT has no row 1". It does NOT yet restore
per-statement dominance: `supOn` is a value with a convergence law and is not
yet characterized as a supremum, so the upper-bound law and the approximate
least-upper-bound law remain open.
Index-status: accepted

- **Lane:** `creal-supon`
- **Answers:** [ADR-0675](adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md),
  which measured EVT as having a row-2 impossibility result
  (`CReal.evt_attained_max_decides_sign`) with nothing constructive behind it,
  because `CReal.supOn` was absent from the kernel.
- **Files:** `crates/axeyum-lean-kernel/src/creal/supremum.rs` (the rungs),
  `crates/axeyum-lean-kernel/src/creal/ivt.rs` (one extraction).

## Decision

Land `CReal.supOn : ∀ F a b, le a b → UniformlyContinuousOn F a b → CReal`
together with `CReal.supSeq_converges_supOn`, and **do not claim EVT
dominance until the two characterizing laws also land.**

Thirteen declarations, all admitted through `Kernel::add_declaration` with an
empty axiom footprint (verified by
`creal_tests::every_creal_declaration_is_checked_and_axiom_free`, which
enumerates `kernel.environment()` rather than a hand-maintained list).

## What this changes about ADR-0675

ADR-0675's measurement was correct on the day it was taken and its framing
survives: **having a boundary row the other library lacks is a trade, not
dominance.** What has changed is only the first half — there is now something
constructive behind EVT's row 2.

What has *not* changed is the verdict. `supOn` is a real number that is the
limit of the mesh maxima, and that is all any machine-checked statement about
it currently says. Two declarations separate that from EVT:

1. **The upper-bound law**, `∀ x, le a x → le x b → le (F x) (supOn F a b hab u)`.
2. **The approximate least-upper-bound law**: for every `eps > 0` there is a
   point of `[a, b]` at which `F` exceeds `supOn − eps`.

The second **must stay approximate**. Its exact form is precisely what
`CReal.evt_attained_max_decides_sign` refutes, and ADR-0603's grading is what
makes an approximate row 1 plus an exact row 2 an honest pair rather than a
gap. Nothing in this lane adds an `argmax`-shaped declaration, and nothing
should.

## Why the construction is shaped the way it is

The value/argmax split is the whole design. Every term of the sequence is a
finite maximum over a mesh — a *height* — so nothing anywhere on the route
names a point at which the height is attained.

Two kernel constraints shape the rest:

- **Kernel fact 1.** `K` and the sequence feed `CReal.speedup`, a `Type`-level
  construction, so neither may come out of an existential. Both are concrete:
  `K` is the literal `3`, the sequence is `CReal.supSeq` applied to the given
  arguments. The interval width, the one quantity that looks like it needs an
  Archimedean existential, is read off `CReal.bound` — a total computable
  projection — inside `CReal.mesh_le_of_ge`. `CReal.archimedean`'s `Exists` is
  never touched.
- **Kernel fact 2.** `Exists.rec` into a `Prop` is fine, and the construction
  uses it twice: once for the coarse mesh index in `meshPoint_near_coarse`,
  once for `Nat.le_dest` in `supSeq_le_add`. The restriction bites only at
  `supOn`'s own `CReal.mk`.

## Consequence: one declaration split in `ivt.rs`

`CReal.cauchy_of_abs_diff_le` built the raw `(K+2, per-pair)` pair and
immediately closed an `Exists` over it. `regular_of_scaled_cauchy` needs that
pair as DATA, and by kernel fact 2 a `Cauchy f` witness can never give it
back — so *every* construction that turns a real-valued Cauchy estimate into an
actual `CReal` needs it before the existential closes.

Split rather than duplicated: `CReal.scaledCauchy_of_abs_diff_le` is the pair,
`cauchy_of_abs_diff_le` is one `cexists_intro` on top of it. No proof content
moved. Duplicating would have left two copies of one 300-line seven-term bound
that must stay in sync while the kernel happily verifies both.

## What the prior plan got wrong, and it was always in the same direction

`supremum.rs`'s module doc carried an unusually precise plan that had already
corrected itself twice. It was right about the route (nested refinement, not
`bucketIndex`) and right that the blocker was the per-level gap bound. It
oversized what remained, three times:

1. **No telescope is needed.** The plan sizes the step after the gap bound as
   "sum the per-level gaps", and contemplates a *double* telescope because
   `trueExpOfModulus` can jump the mesh level by arbitrarily many doublings
   within one block. But `meshMax_le_add_of_step_close` is already
   **depth-uniform** — arbitrary depth `d`, same epsilon — so the estimate at
   `k' ≥ k` is ONE application and the number of intervening doublings never
   enters. The double telescope would have been machinery for a difficulty the
   previous rung had already removed.
2. **The schedule was missing the interval width, and nothing said so.**
   `expOfModulus` schedules the modulus only. The mesh width is `(b−a)/2^j`,
   so without a width term the construction is correct only on intervals of
   width at most one. `CReal.supLevel` adds `Nat.size (CReal.bound (b−a))`.
3. **`CReal.mesh_le_of_ge` already existed** and is exactly the Archimedean
   rescaling needed, with a left-hand side syntactically identical to
   `supremum.rs`'s own `mesh_delta`. It lives in `integral.rs`, filed under the
   consumer that first needed it — hiding place 1 from CLAUDE.md's retrieval
   section. `examples/shape_search` found it in one query; a name search would
   not have.

The general lesson, and it is the one CLAUDE.md's retrieval section already
teaches: **a file that records obstacles accumulates stale ones by
construction, and its precision is exactly what makes them expensive.** Every
rung of that plan whose account of what LANDED was checked proved reliable;
every account of what REMAINED needed re-measuring against the kernel.

## Alternatives considered

- **Route 1, adapting `bucketIndex`.** Rejected, as the module doc already
  had. It would import `crossingClose`'s open domain-membership side
  condition. Nothing in this lane touches that family.
- **Taking the interval-width bound as an explicit `(W, proof)` argument**, on
  the `CReal.inv` house rule that Archimedean data is supplied rather than
  derived. Unnecessary once `mesh_le_of_ge` was found: `CReal.bound` computes
  it, so `supOn` carries no width hypothesis at all.
- **Routing through `CReal.limit` (Bishop completeness).** `RegularSeq` is the
  canonical-sample form at a fixed modulus with no room for a scale factor `K`,
  which is precisely why `regular_of_scaled_cauchy` exists and says so in its
  own documentation. The `speedup` route is the one the development already
  uses for `CReal.integral`, and `supOn` mirrors it.

## Cost

`creal_prelude_builds` 110.4 s before, 114.0 s after — flat. Full `creal::`
sweep 199 passed, 0 failed. Twelve of thirteen declarations were first-attempt
kernel accepts; the thirteenth failed once on a `pi_fv`/`arrow` binder and was
fixed by inspection.
