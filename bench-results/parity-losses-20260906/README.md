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
cause_class, top_route_elapsed_ms, cause_detail`) classifies every one of the
77 rows.

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
`docs/research/11-design-review/2026-09-05-parity-loss-census.md`) used a
`class` column derived from the **last** route's message rather than the
route that spent the budget, and was refuted on 67 of 70 files across QF_UF
and UF (correction block added in `b57800c06`/`f3ce8ef58`). This census does
not share that method — see point 2 above — so its classes do not inherit
that defect. It is, however, a fresh measurement in its own right and
carries no claim beyond what is stated here.

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
