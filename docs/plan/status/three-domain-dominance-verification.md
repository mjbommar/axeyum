# Lane: three-domain-dominance-verification

**Status:** in progress (started 2026-08-31)

## Mission

Produce ONE referee-checkable verification document for the Pareto-dominance
claim across three domains (real analysis, number theory, linear algebra).
Verification, not advocacy: where the claim does not hold, say so.

## Landed changes

| when | what |
| --- | --- |
| 2026-08-31 | lane opened; kernel examples built `--release`; holdout isolation PASS before work |
| 2026-08-31 | merged local `main` (22 commits ahead of `origin/main`); re-measured everything after |
| 2026-08-31 | full kernel projection captured; per-statement footprints measured for 46 declarations |

## Measurements taken in this worktree

Base after merge: local `main` at `f7adaf7c3`. `origin/main` was `878c285d9`,
**22 commits behind**, which is why my first search reported `lub_decides_em`
and ADR-1010 absent. Both exist. Recorded because it is the exact
"never cite unmerged lane work" hazard read from the other side.

`kernel_declaration_projection --include-constructed`, release build:

- `rows=12049`, `distinct_names=2558`
- kinds (deduped by name): theorem 2100, definition 349, constructor 31,
  **axiom 30**, recursor 24, inductive 24
- **every axiom-bearing name is in `axreal`** — 30 of 30. Every other prelude
  (`logic nat integer rat characterization string creal complex cpoint`)
  reads 0.

Per-statement footprints: 46 headline declarations across all three domains,
**all 0**. 12 expected-absent controls run in the same command; 11 came back
ABSENT as the documents predict, and **one did not** — see below.

## Findings in flight

1. **`Nat.lnp_unrestricted_implies_em` IS BUILT**, `nat`, theorem, footprint 0.
   `graded-statement-families-number-theory-and-linear-algebra.md:366` says it is
   "**Not built, and it is the highest-value unbuilt row in this note**", and
   `:639` lists it as a next target. Both stale. It landed in `b81277a5c`
   (`nat_prelude/least_number.rs`) and is documented by **ADR-0725**, which my
   brief did not cite. So number theory HAS a row 2.
2. It is the only row 2 in the repository **pinned as an exact equivalence**:
   `Nat.lnp_unrestricted_implies_em : L → E` plus `Nat.em_implies_lnp : E → L`,
   both footprint 0. The three `CReal` rows are one-directional.
3. `CReal.UniformlyContinuousOn : (CReal → CReal) → CReal → CReal → Sort (1)`,
   re-measured, against control `CReal.le : CReal → CReal → Prop`. The modulus
   is data.
4. `CReal.evt_approx_max`'s rendered type confirms bound-plus-approximation,
   witness `x` under the `∀ n`. Not an attained argmax.
5. Linear algebra: `matMul`/`matTranspose`/`dotN` are at SYMBOLIC dimension
   over `Nat → Nat → Rat`; only the determinant is fixed-size (`det2`, `det3`).
   No general-`n` determinant, no `rank`.
