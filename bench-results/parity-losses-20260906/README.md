# QF_NRA loss census, 2026-09-06

The QF_NRA entry slice (`docs/plan/families/smt-quantifier-free/qf-nra.md`).
Population is `QF_NRA.txt`, the 77 reference-only files from the parity sweep
recorded in `bench-results/PARITY.md` (`## QF_NRA — 2026-09-07T01:33:46Z`,
solver commit `00373a7d42`): reference (cvc5 1.3.4) decided `sat`/`unsat`,
axeyum's **front door** (`smtcomp_cli`, i.e. `solve_smtlib`) returned
`unsolved`. Extracted with the same `awk` recipe as the 2026-09-05 S3
census's `<DIV>.txt` files:

```
awk -F'\t' 'NR>1 && $2=="unsolved" && ($3=="sat"||$3=="unsat") {print $1}' \
  bench-results/parity-details/QF_NRA.tsv
```

`QF_NRA.census.tsv` (`file, axeyum_front_door, reference, declared,
explain_corpus_flat_verdict, class_vs_front_door, cause_class,
top_route_elapsed_ms, cause_detail`) classifies every one of the 77 rows.

## Method, stated explicitly (see the note below on why)

1. **The loss population is front-door.** `axeyum_front_door` on every row
   comes from the scored parity sweep's sidecar, i.e. `smtcomp_cli` /
   `solve_smtlib` — never from `explain_corpus`.
2. **The cause class is the route that spent the budget, not the last
   route's message.** For each file, `explain_corpus --list <file> 24000
   --json --timed-trace` (one file per invocation, each wrapped in an
   external `timeout -k 5 45`, `taskset -c 0-7` on s5) was parsed for its
   `trace.attempts` array; the `probe` fragment-detection pseudo-attempt is
   excluded, and the class is derived from whichever remaining attempt has
   the largest `elapsed_ns` — the route that actually consumed the wall
   time, not whichever route happened to run last or print last.
3. A file whose `explain_corpus` invocation itself errored or was killed by
   the external 45 s bound is classed `diagnostic-instrument-inconclusive`
   and NOT folded into any capability bucket — 5 of the 77 rows (6.5%). Their
   front-door loss is still solid (`axeyum_front_door=unsolved`, confirmed by
   the scored sweep); only the *causal* attribution is unavailable from this
   instrument on these five.

## Why this is stated this explicitly

The 2026-09-05 S3 loss census (`bench-results/parity-losses-20260905/`,
`docs/research/11-design-review/2026-09-05-parity-loss-census.md`) had TWO
defects: its `class` column was derived from the **last** route's message
rather than the route that spent the budget, and it was refuted on 67 of 70
files across QF_UF and UF (correction block added in
`b57800c06`/`f3ce8ef58`). This census does not share the first defect — see
point 2 above.

The second defect is more subtle and applies to any census built this way,
this one included: `explain_corpus` runs `check_auto_explained` on the
**flat assertion view**, not `solve_smtlib` (the shipped front door) — its
own banner says so, and it is measured to disagree with the front door on
134 of 397 committed benchmarks elsewhere in this repo. The loss
*population* here is front-door (point 1), but the *cause class* for each
file still comes from `explain_corpus`'s own execution. If the flat view
took a different route than the front door on a given file, "the route that
spent the budget" describes an execution that is not the one that actually
lost — the class would be correct about `explain_corpus`, not about
`solve_smtlib`.

**This is checked, not assumed**, via `explain_corpus_flat_verdict` /
`class_vs_front_door`:

- `explain_corpus_flat_verdict` records the flat view's own decision
  (`flat-sat` / `flat-unsat` / `flat-unknown`) for every `decided`-status row,
  `n/a` where the instrument produced no verdict at all (the same 5 rows as
  point 3).
- `class_vs_front_door` is `consistent` when the flat verdict is
  `flat-unknown` (matching the front door's `unsolved` — the only value
  possible without a live contradiction), `UNCONFIRMED-divergent` when the
  flat view reached a `flat-sat`/`flat-unsat` decision the front door did
  not, and `no-verdict` for the 5 instrument-failure rows.

**Result: 0 of the 72 classified rows are `UNCONFIRMED-divergent`.** Every
row that `explain_corpus` decided at all decided `flat-unknown`, so on this
population the flat view never resolved a query the front door could not —
there is no measured case here of the flat view reaching a *decisive* answer
via a different path. This does not *prove* route identity (a query can
reach `unknown` through two different internal paths), but it rules out the
concrete failure mode this check targets — a class attributed from an
execution that actually decided differently — for all 72 rows. The dominant
class figures (`nra-cross-product-admission-bound` +
`nra-refinement-incomplete` = 69/77 = 89.6%) carry that qualifier: confirmed
against zero flat/front-door verdict divergence, not confirmed to be the
exact front-door dispatch path on every file.

## Class breakdown

| `cause_class` | files | share |
|---|---:|---:|
| `nra-cross-product-admission-bound` | 62 | 80.5% |
| `nra-refinement-incomplete` | 7 | 9.1% |
| `diagnostic-instrument-inconclusive` | 5 | 6.5% |
| `cas-ideal-refuter-incomplete` | 1 | 1.3% |
| `nra-real-root-not-applicable` | 1 | 1.3% |
| `wide-int-admission-incomplete` | 1 | 1.3% |

`nra-cross-product-admission-bound` + `nra-refinement-incomplete` = 69/77
(89.6%): the generic multi-variable nonlinear-abstraction route (`nra`)
either refuses admission outright (its deterministic cross-product
admission bound is 2; every one of the 62 files exceeded it, several by
orders of magnitude — `mbo_E13E18.smt2` alone carries 7,874 cross-products)
or runs its refinement to a fixpoint without deciding. Both are the named,
expected boundary from `crates/axeyum-solver/src/capabilities.rs`'s QF_NRA
entry: "sound-incomplete only on the hard coupled/high-degree tail" —
confirmed by measurement rather than assumed. The instrument's own message
for the dominant class: "nonlinear abstraction: N cross-products exceed the
deterministic admission bound of 2 ... this needs a nlsat/CAD engine."

The three singleton classes are a Geogebra geometry file where the CAS
ideal-refuter could not find a combining sign, a `kissing`-packing file for
which the single-variable real-root route does not apply (multivariate), and
one `meti-tarski` file carrying an integer literal outside the i128
reference range (`wide-int-admission`, ADR-1702 slice 2 — an already-named,
separately tracked gap, not new).
