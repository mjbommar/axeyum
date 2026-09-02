# Lane: det-mul-2

<!-- plan-section: lane-status -->

**Status:** landed, **target reached**. `Rat.det_matMul : ∀ n A B,
det (matMul A B n) n = det A n * det B n` is admitted, axiom-free, at a fully
symbolic dimension — the last of the four laws
[ADR-1120](../../research/09-decisions/adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)
named over `Rat.det`. ADR-1440's obligation 1 is closed with it. Decision
recorded in
[ADR-1543](../../research/09-decisions/adr-1543-obligation-1-closes-and-the-substitution-order-is-what-makes-it-close.md).

Twenty-two axiom-free declarations across two new modules, read from
`kernel.environment()` and not from a diff.

## Step 0, and the gap list it produced

`shape_search`, rebuilt from source in this worktree (`declarations=2048`,
`build=3.2s`, so a FRESH index and not a stale prebuilt binary):

| query | verdict |
| --- | --- |
| `--name-like Rat.sumMaps` | **ABSENT** |
| `--name-like Rat.prodRange` | **ABSENT** |
| `--name-like Int.sumMaps` | FOUND 5 (positive control) |
| `--name-like Int.prodRange` | FOUND (positive control) |
| `--name-like Rat.sumRange` | FOUND (positive control, same carrier) |

What `Int.sumMaps` needs from `Int`, and whether `Rat` had it:

| `Int` ingredient | `Rat` counterpart | gap? |
| --- | --- | --- |
| `Int.sumRange`, `sumRange_congr` | `Rat.sumRange`, `Rat.sumRange_congr` | present |
| `Int.sumRange_mul_right` | — | **GAP**, built |
| `Int.sumRange_mul_left` | `Rat.mul_sumRange` states the same content the OTHER WAY ROUND | **GAP in the direction the induction consumes**, built |
| `Int.prodRange` + `_zero`/`_succ` | — | **GAP**, built |
| `Int.prodRange_shiftFront` | — | **GAP**, built (the front peel is what `cons` reindexes at) |
| `Int.prodRange_congr` | — | **GAP**, built |
| `Int.add_mul` (right distributivity) | `Rat.right_distrib` | present, different name |
| `Int.one_mul`, `Int.zero_mul` | **neither exists over `Rat`** (only `mul_one`, `mul_zero`) | derived inline from `mul_comm`, not declared |
| `Nat.rec` with a higher-order motive | same | present |

Three further gaps the expansion itself needed and step 0 did not predict:
a row-replacement operation (`Rat.matSetRow`), the cursor's substitution
(`Rat.matSubstRows`), and a `sumMaps` congruence restricted to maps into the
range (`Rat.sumMaps_congr_mapsInto`) — the last because
`Rat.det_row_selection` carries `MapsInto` and `sumMaps_congr`'s unrestricted
hypothesis cannot discharge it.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/sum_maps.rs` (new):

| declaration | what it is |
| --- | --- |
| `Rat.prodRange` | finite product over `[0,n)`, `Nat.rec` on the bound |
| `Rat.prodRange_zero` / `_succ` | the defining equations, `Eq.refl` |
| `Rat.prodRange_shiftFront` | peels the FRONT factor (`_succ` peels the back) |
| `Rat.prodRange_congr` | pointwise factors give equal products |
| `Rat.sumRange_mul_right` / `_mul_left` | pull a constant out of a `sumRange`, in `Int`'s orientation |
| `Rat.sumMaps` | a sum indexed by the FUNCTION SPACE `[0,m) → [0,n)` |
| `Rat.sumMaps_zero` / `_succ` | the defining equations, `Eq.refl` |
| `Rat.sumMaps_congr` | pointwise summands give equal sums |
| `Rat.sumMaps_mul_left` / `_mul_right` | pull a constant out of either side |

`crates/axeyum-lean-kernel/src/rat_prelude/det_mul.rs` (new):

| declaration | what it is |
| --- | --- |
| `Rat.matSetRow` | `M` with row `t` replaced, by `matId`'s `bool_select_rat` |
| `Rat.matSetRow_at` / `_off` | its two equations, one rewrite each |
| `Rat.matSubstRows` | rows `[s, s+m)` of `M` taken from `B` through `g` |
| `Rat.matSubstRows_below` | rows below the window survive |
| `Rat.matSubstRows_at` | inside the window the row is the one `g` selects |
| `Rat.sumMaps_congr_mapsInto` | the congruence restricted to maps into `[0,n)` |
| `Rat.det_matMul_expand` | **ADR-1440's obligation 1**, the Cauchy–Binet expansion |
| `Rat.det_matMul` | **`det (A·B) n = det A n · det B n` at symbolic `n`** |

Facts: `F:rat-det-mat-mul`, `F:rat-det-mat-mul-expand`. Both
`formal.statement`s are `Kernel::render_lean` of the admitted type, read from
`kernel_declaration_projection`'s `canonical_type` column. Both checkers count
FOUR rows (`rat`, `creal`, `complex`, `cpoint`) and require exactly four, so a
deletion, a rename, a demotion to `Definition`, a nonzero footprint, or a
failure to survive into a downstream prelude each move the count and exit 1;
`scripts/new-fact.py` verified both patterns fail on mutated output before the
files were written.

## The one design decision that mattered

`Rat.matSubstRows` peels the **outermost** row first:

```text
matSubstRows B (m+1) s g M
  = matSubstRows B m (s+1) (g ∘ succ) (matSetRow s (B (g 0)) M)
```

`Rat.sumMaps`'s `cons` extends a map at the FRONT, so with that order
`matSubstRows B (succ j) s (cons k g) M` and
`matSubstRows B j (succ s) g (matSetRow s (B k) M)` are the SAME TERM up to ι
and η, and the induction step needs no commutation lemma between "set row `s`"
and "substitute the rows above `s`". The default order — substitute the rest,
then fix this row — needs exactly that lemma, with its own induction and a case
split on the row index. Full reasoning in ADR-1543, including the two secondary
choices (`matSetRow` selects rather than recurses; the cursor's row is
`Nat.add s i`, offset LEFT, so the peeled row ι-reduces to `s`).

## Evidence beyond "the kernel accepted it"

The trusted gate cannot tell you a `Definition` is wrong, and it cannot tell
you a `Theorem` says something weaker than its name. Three kinds of check:

- **Evaluation, `sum_maps_tests.rs`.** `sumMaps m n (fun _ => 1) = n^m` at
  seven `(m,n)` including both empty cases; `sumMaps 2 3 (fun g => g 0 * g 1)`
  is `9` and is asserted NOT to be the diagonal-only `5`; `prodRange` visits
  exactly `[0,n)`, separated from the inclusive answer (`6` vs `24`) and from
  one term short (`6` vs `2`); the empty product is `one`, not `zero`.
- **Evaluation, `det_mul_tests.rs`.** `matSetRow` writes one row and nothing
  else, over a 3×3 with nine pairwise distinct entries; `matSubstRows B 2 1 g M`
  with `g 0 = 2`, `g 1 = 0` — non-monotone and non-identity on purpose — is
  checked entry by entry with the two plausible index defects (absolute index,
  copy row `s+i`) asserted apart.
- **Statement and instantiation.** `Rat.det_matMul`'s declared type is
  `def_eq`-compared against a statement built independently in the test, with
  the dimension bumped by one and the two matrices swapped both asserted NOT to
  be it. It is then instantiated at `1×1` and at `2×2` with
  `A = [[1,2],[3,4]]`, `B = [[5,6],[7,8]]`, where both determinants are `−2`
  and the product is `4` — the SIGN is what makes that discriminating, and
  `det A = +2` is asserted false. `Rat.det_matMul_expand` is instantiated at
  `n = 2`, where the sum runs over all four maps: the total is `4`, and the
  identity-map-only total `−8` is asserted apart, so the ENUMERATION is
  exercised and not just the arithmetic.

One negative control had to be replaced because it was VACUOUS and said so on
its first run: asserting `sumMaps_mul_left` and `sumMaps_mul_right` apart at a
concrete instance FAILS, because both sides evaluate to `12 = 12` there and the
two instantiated propositions are `def_eq`. The check now separates the two
theorems' GENERAL types, read from the environment.

## Verification run in this lane

Every command foreground, through `scripts/cargo-serialized.sh`.

- `cargo test --release -p axeyum-lean-kernel --lib -- rat_prelude:: --test-threads=4`
  — **169 passed, 0 failed**, 110.18 s (156 at lane start, 163 after the
  `sumMaps` commit).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/validate-facts.py` — exit 0, zero `ERROR` lines.
  `depends_on` completed by `check-fact-depends-derived.py --fix` (19 edges
  read out of the proof terms).
- `kernel_declaration_projection --require-declaration Rat.det_matMul
  --require-kind theorem` — four `found … theorem Rat.det_matMul 0` rows, which
  is also the confirmation that `creal`, `complex` and `cpoint` still build on
  top of the enlarged `rat` prelude.
- `python3 scripts/gen-adr-index.py --check` — exit 0.
- **Build cost, measured with `prelude_build_timing` on the same host against a
  clean snapshot of the merge base:** `rat` 1.68 / 1.66 / 1.64 s after,
  1.66 / 1.63 / 1.65 s before. Within noise; every numeral these declarations
  form is an index, not a magnitude.

## Nothing did not run

No check in this lane was deferred, backgrounded or left unfinished.

## What this does NOT establish

No `rank`, no invertibility criterion, no Leibniz formula and no permutation
type — `Rat.sumMaps` is a summation schedule and the non-injective maps are
killed by `Rat.det_row_selection`, not inside the expansion. Cauchy–Binet for
NON-square products is not proved, though `det_matMul_expand` leaves
`matMul`'s inner bound independent of the dimension and is the right starting
point for it. `Rat.prodRange` deliberately carries no algebra beyond its front
peel and a congruence: the expansion's coefficient is never evaluated.

The dominance document's §4.3 determinant row said "fixed size only" and the
paragraph under it said "it is specifically the determinant that is
fixed-size". Both were true when written and are now false, so both were
corrected in place rather than left to accumulate — `rank` is what remains
absent in that family.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `rat_prelude/sum_maps.rs` | `Rat.prodRange` and `Rat.sumMaps` — the finite product over a range and the sum indexed by the FUNCTION SPACE `[0,m) → [0,n)`, both measured absent over ℚ by `shape_search` against a fresh 2,048-declaration index with three same-kind positive controls. Ported from `int_prelude/prod.rs` and `int_prelude/sum_maps.rs`; three things differ and each cost a base case — this prelude has no `Rat.one_mul` and no `Rat.zero_mul`, so the left identity and the left absorbing zero are derived inline from `mul_comm`; right distributivity is `Rat.right_distrib`, not `Int.add_mul`; and `Rat.mul_sumRange` states the left pull the wrong way round for the induction. `Rat.sumMaps_mul_right` has no `Int` counterpart and is not a convenience: `Rat.det_row_selection` puts `det B n` on the RIGHT of every summand. Thirteen declarations, all axiom-free, with an evaluation-test module (cardinality `n^m` at seven `(m,n)` including both empty cases; the full product separated from its diagonal; `prodRange`'s exclusive bound separated in both directions). One negative control was replaced because it was vacuous: the two `mul` pulls are `def_eq` at any concrete instance and had to be separated at their general types. ADR-1543. |
| 2026-09-02 | `rat_prelude/det_mul.rs` | `Rat.matSetRow` and `Rat.matSubstRows` plus their four equations — the row surgery the Cauchy–Binet cursor substitutes with, needed as TERMS because `Rat.det_row_smul`/`det_row_replaced` take the reference matrix as an argument rather than a hypothesis. `matSubstRows` peels the OUTERMOST row first, which is what makes `matSubstRows B (succ j) s (cons k g) M` and `matSubstRows B j (succ s) g (matSetRow s (B k) M)` the same term up to ι and η and removes the commutation lemma the default order would need; `matSetRow` selects on `Nat.beq` (`Rat.matId`'s encoding) rather than recursing, turning both of its equations from inductions into single rewrites; the cursor's row is `Nat.add s i`, offset LEFT, so `add s 0` ι-reduces and the whole arithmetic cost is one `Nat.succ_add`. Evaluation tests over a 3×3 with pairwise distinct entries and a non-monotone `g`, with the absolute-index and copy-row-`s+i` defects both asserted apart. ADR-1543. |
| 2026-09-02 | `rat_prelude/det_mul.rs` | **`Rat.det_matMul : ∀ n A B, det (matMul A B n) n = det A n * det B n`** — ADR-1120's last open law, axiom-free at symbolic `n`, together with `Rat.det_matMul_expand` (ADR-1440's **obligation 1**, the expansion over the function space of index maps) and `Rat.sumMaps_congr_mapsInto` (the congruence restricted to maps into the range, which is what carries `Rat.det_row_selection`'s `MapsInto` hypothesis through the sum; its successor step needs `sumRange_congr_lt`, not `sumRange_congr`, and its base case needs no `0 < n`). The assembly uses the expansion TWICE — at `B` and at `matId` — so the coefficient `prodRange (fun i => A i (g i)) n` is never evaluated. `rat_prelude::` 169 passed / 0 failed; `rat` prelude build 1.68/1.66/1.64 s against 1.66/1.63/1.65 s at the merge base, within noise. Facts `F:rat-det-mat-mul`, `F:rat-det-mat-mul-expand`. The dominance document's §4.3 determinant row is corrected in place. ADR-1543. |
