# Notes: 132-ledger-trig

Detail moved out of [`../status/132-ledger-trig.md`](../status/132-ledger-trig.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Ch.14 (crossing index):** `F:creal-crossingindex`, `F:creal-crossingupper`,
`F:creal-crossinglower`, `F:creal-crossingsampleupper`,
`F:creal-crossingsamplelower` — recorded as a deliberately SLACK variant, not
the tight bracket `a+i0*eps <= c <= a+(i0+1)*eps`: the tight version is not
constructible because deciding which side of an exact crossing `c` falls on
IS the undecidable comparison (`creal/ivt.rs` refutes the analogous
exact-root construction).

**Ch.25-27 (polynomials over `Complex`):** `F:complex-polyeval`,
`F:complex-polyeval-zero`, `F:complex-polyeval-succ`, `F:complex-polyadd`,
`F:complex-polyeval-polyadd`, `F:complex-polyscale`,
`F:complex-polyeval-polyscale`, `F:complex-polydegreelt` (recorded as a
PROPOSITION, not a computed degree — `Complex.Equiv` is undecidable, so no
coefficient can be tested for zero), `F:complex-polydegreelt-polyadd`,
`F:complex-polydegreelt-polyscale`, `F:complex-polymul`,
`F:complex-polyeval-polymul` (holds ONLY under both `polyDegreeLt`
hypotheses — the naive convolution identity is FALSE, refuted at `n=2` per
`Complex.sumRange_mul_eq_diag_add_corner`'s own doc comment; the corner term
provably vanishes only because every corner index pair `(i,j)` with `i<m,
j<n` forces `i+j>=m+n`, exactly what the two degree bounds carve out).

**NOT registered, per this batch's explicit scope:** `CReal.integral_split`
(open), `Complex.polyDegreeLt_polyMul` / the factor theorem (a sibling lane
is building them now), the Leibniz criterion / `sinOne` (a sibling lane is
building those), anything in `creal/uniform_convergence.rs` (in progress),
Ch.21 `e`-irrational (genuinely open).

**Provenance.** Canonical types were read from
`kernel_declaration_projection`'s own UNFILTERED emit mode (no
`--require-declaration` flag) — the same in-tree tool used for the
`--require-declaration` checks, whose unfiltered output already prints, per
constructed prelude, one TSV row per declaration with
`kernel.render_lean(declaration.ty())` as its last field. No new probe
binary was needed for this batch (the sibling `ledger-euler` lane's probe
covered a gap that `kernel_declaration_projection` itself already closes for
canonical types). Output was piped to a scratchpad file and every
`formal.statement` field was injected programmatically by a Python script
reading that TSV, never hand-transcribed. `depends_on` links only to facts
that exist in this ledger (including the other 27 registered in this same
batch); every prelude dependency `theorem_dependency_inventory` names that
is NOT yet a registered fact is omitted and named in the fact's own `notes`
(e.g. `CReal.geomYBound`, `CReal.geom_pair_within`, `CReal.ratioDecayBound`,
the four `converges_*` helpers under `geomScaledCauchyOfLt`).
`axiom_footprint: []` for all 28, confirmed via `nat_axiom_inventory
--include-constructed --require-axiom-free creal` and `--require-axiom-free
complex` (`creal: axiom=0 opaque=0 quotient=0 total_trusted=0`, `complex:
axiom=0 opaque=0 quotient=0 total_trusted=0`).

**Checker commands, verified on this tree before being written:**
- Definitions (`CReal.cosOne`, `CReal.cosTerm`, `CReal.cosSeriesPartial`,
  `CReal.crossingIndex`, `Complex.polyEval`, `Complex.polyAdd`,
  `Complex.polyScale`, `Complex.polyDegreeLt`, `Complex.polyMul`): the DIRECT
  `kernel_declaration_projection --require-declaration <name> --require-kind
  definition` checker (built by the `ledger-euler` sibling lane earlier this
  session), piped through `grep -cE '^found[[:space:]]<label>[[:space:]]
  definition[[:space:]]<Name>[[:space:]]'`.
- Theorems (the remaining 19): `theorem_dependency_inventory -- <Name>`
  piped through `grep -cE '^<Name>[[:space:]]'`.
- `axiom_footprint`: `nat_axiom_inventory --include-constructed
  --require-axiom-free creal` (or `complex` for the `Complex.*` facts).

**Mutation-tested** in an isolated `/data0` snapshot
(`scripts/lane-snapshot.sh HEAD`, never the shared checkout — removed after
use). Renamed three declarations' display strings in the snapshot's source
(`CReal.cosOne` -> `"cosOne_MUTATED"` at `creal.rs:4541`,
`CReal.sumRangeRatioTest` -> `"sumRangeRatioTest_MUTATED"` at
`creal.rs:4475`, `Complex.polyEval_polyMul` -> `"polyEval_polyMul_MUTATED"`
at `complex.rs:1632`), rebuilt in release, and confirmed:
- `kernel_declaration_projection --require-declaration CReal.cosOne
  --require-kind definition` now exits 1 (`error: no declaration named
  "CReal.cosOne" exists...`) — the mutated-name check correctly disappears.
- `theorem_dependency_inventory -- CReal.sumRangeRatioTest` still exits 0
  (the tool's own substring filter matches `sumRangeRatioTest_MUTATED`), but
  the fact's actual `checker_command` — the anchored `grep -cE
  '^CReal\.sumRangeRatioTest[[:space:]]'` — returns count 0 / exit 1, because
  `_MUTATED` sits immediately after the name with no tab. Same result for
  `Complex.polyEval_polyMul`.
- In the SAME rebuild, two unrelated, unmutated controls
  (`CReal.geomCauchy`, `CReal.crossingIndex`) still return count 1 / exit 0
  through their own checker forms — confirming the checks discriminate on
  the specific declaration's own name, not on the build succeeding globally.

`python3 scripts/validate-facts.py` is green: **750 facts, 0 errors**
(722 before this batch + 28 new).

Nothing under `crates/` was touched in the shared worktree — only
`artifacts/facts/`, this status file, and `PLAN.md` (regenerated). Four
lanes were live in `creal/trig.rs` + `creal/alternating.rs`,
`creal/uniform_convergence.rs`, `complex/poly.rs`, and
`creal/integral.rs`/`crossing.rs` per this lane's brief; all reads only.
