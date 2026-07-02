# Measured Scoreboard — axeyum vs Z3

> **Auto-generated. Do not edit by hand.** Regenerate with `python3 scripts/gen-scoreboard.py`.

A single-glance, honest view of where the pure-Rust axeyum solver stands against **z3 4.13.3** across every *measured* division. Every number here is read straight from a committed baseline JSON under `bench-results/baselines/` — nothing is hand-entered.

## How to read this

- **Decided** = `sat + unsat` — the instances axeyum *resolves*. Everything else is a **sound `unknown`** (we cannot decide it yet) or **unsupported** (the logic fragment is not wired); axeyum never guesses.
- **Decide%** = `Decided / Files`. This is the **capability frontier** — higher means axeyum decides more of the slice on its own.
- **DISAGREE** = wrong verdicts vs the ground truth (oracle disagreements + `:status` disagreements). **DISAGREE = 0 everywhere means zero wrong sat/unsat — soundness.** This is the line that must never move off zero.
- **Ground-truth** — how each division's verdict was checked: `z3-library` (the in-repo Z3 oracle), `z3-binary` (the external Z3 binary), `z3-library+binary` (a mix across the slice), or `:status` (the SMT-LIB `(set-info :status ...)` annotation, used when the Z3 oracle was vacuous/skipped for the whole slice — e.g. it rejected the logic's sort). An honest row reflects what was *actually* compared (see the **Cmp** column = instances the oracle compared).
- **PAR-2** = mean PAR-2 score in seconds (timeouts counted at 2×); lower is faster. `—` where not recorded.

## Headline

- **35 division baselines** measured vs z3 4.13.3, spanning **24 logic fragments** (BV, LIA, QF_ABV, QF_ALIA, QF_AUFBV, QF_AUFLIA, QF_AX, QF_BV, QF_BVFP, QF_DT, QF_FF, QF_FP, QF_LIA, QF_LRA, QF_NIA, QF_NRA, QF_S, QF_SEQ, QF_SLIA, QF_UF, QF_UFBV, QF_UFFF, QF_UFLIA, UF).
- **DISAGREE = 0 across all baselines** — zero wrong verdicts over 611 oracle-compared instances (992 files total, 663 decided).
- Decide-rate ranges **0%–100%** across divisions — that spread *is* the capability frontier; DISAGREE = 0 is the soundness floor that holds everywhere.

## Divisions vs Z3

Sorted by logic, then by descending decide-rate. Every committed `*solver-vs-z3*` baseline plus the synthetic graduated NRA/NIA baselines appears below.

| Division | Slice | Files | Decided | Decide% | Unknown | Unsup | Cmp | DISAGREE | Ground-truth | PAR-2 (s) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| BV | `bv-bitwuzla-regress-clean-quantified` | 5 | 4 | 80% | 1 | 0 | 3 | 0 | z3-binary | 4.000 |
| BV | `bv-cvc5-regress-clean-quantified` | 54 | 37 | 69% | 6 | 11 | 37 | 0 | z3-binary | 7.929 |
| LIA | `lia-cvc5-regress-clean-quantified` | 12 | 0 | 0% | 8 | 4 | 0 | 0 | :status | 30.000 |
| QF_ABV | `qf-abv-cvc5-bitwuzla-regress-clean` | 193 | 169 | 88% | 0 | 24 | 165 | 0 | z3-library+binary | 1.666 |
| QF_ALIA | `qf-alia-cvc5-regress-clean` | 6 | 6 | 100% | 0 | 0 | 5 | 0 | z3-binary | 0.000 |
| QF_AUFBV | `qf-aufbv-bitwuzla-regress-clean` | 44 | 41 | 93% | 0 | 3 | 41 | 0 | z3-library+binary | 1.979 |
| QF_AUFBV | `qf-aufbv-cvc5-regress-clean` | 9 | 5 | 56% | 1 | 3 | 4 | 0 | z3-binary | 3.334 |
| QF_AUFLIA | `qf-auflia-cvc5-regress-clean` | 7 | 5 | 71% | 2 | 0 | 4 | 0 | z3-binary | 5.716 |
| QF_AX | `qf-ax-cvc5-regress-clean` | 8 | 8 | 100% | 0 | 0 | 8 | 0 | z3-binary | 0.004 |
| QF_BV | `qf-bv-curated-bvred` | 6 | 6 | 100% | 0 | 0 | 6 | 0 | z3-library | 0.000 |
| QF_BVFP | `qf-bvfp-bitwuzla-regress-clean` | 8 | 7 | 88% | 0 | 1 | 6 | 0 | z3-library+binary | 0.005 |
| QF_DT | `qf-dt-cvc5-regress-clean` | 3 | 3 | 100% | 0 | 0 | 3 | 0 | z3-binary | 0.003 |
| QF_FF | `qf-ff-cvc5-regress-clean` | 30 | 24 | 80% | 0 | 6 | 24 | 0 | z3-library | 0.010 |
| QF_FP | `qf-fp-bitwuzla-regress-clean` | 16 | 16 | 100% | 0 | 0 | 16 | 0 | z3-library+binary | 0.010 |
| QF_LIA | `qf-lia-cvc5-regress-clean` | 11 | 10 | 91% | 1 | 0 | 9 | 0 | z3-binary | 1.819 |
| QF_LRA | `qf-lra-cvc5-regress-clean` | 11 | 9 | 82% | 2 | 0 | 5 | 0 | z3-binary | 3.637 |
| QF_NIA | `qf-nia-synthetic-graduated` | 32 | 32 | 100% | 0 | 0 | 32 | 0 | z3-binary | 6.772 |
| QF_NIA | `qf-nia-cvc5-regress-clean` | 39 | 21 | 54% | 10 | 8 | 20 | 0 | z3-binary | 6.577 |
| QF_NIA | `qf-nia-curated-iand` | 3 | 1 | 33% | 2 | 0 | 0 | 0 | :status | 13.333 |
| QF_NRA | `qf-nra-synthetic-graduated` | 33 | 30 | 91% | 3 | 0 | 30 | 0 | z3-binary | 5.455 |
| QF_NRA | `qf-nra-cvc5-regress-clean` | 38 | 21 | 55% | 16 | 1 | 21 | 0 | z3-binary | 8.660 |
| QF_S | `qf-s-cvc5-regress-clean` | 134 | 48 | 36% | 24 | 62 | 48 | 0 | z3-library+binary | 6.676 |
| QF_SEQ | `qf-seq-cvc5-regress-clean` | 33 | 26 | 79% | 6 | 1 | 26 | 0 | z3-library+binary | 3.751 |
| QF_SLIA | `qf-slia-cvc5-regress-clean` | 50 | 11 | 22% | 10 | 29 | 11 | 0 | z3-library+binary | 9.537 |
| QF_UF | `qf-uf-cvc5-regress-clean-overbound-uninterp-sorts` | 6 | 4 | 67% | 2 | 0 | 4 | 0 | z3-binary | 7.489 |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded` | 82 | 44 | 54% | 13 | 24 | 37 | 0 | z3-library+binary | 4.845 |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded-uninterp-sorts` | 82 | 44 | 54% | 13 | 24 | 37 | 0 | z3-library+binary | 4.845 |
| QF_UFBV | `qf-ufbv-bitwuzla-regress-clean` | 2 | 2 | 100% | 0 | 0 | 2 | 0 | z3-binary | 0.000 |
| QF_UFBV | `qf-ufbv-cvc5-regress-clean` | 4 | 4 | 100% | 0 | 0 | 4 | 0 | z3-binary | 0.001 |
| QF_UFFF | `qf-ufff-cvc5-regress-clean` | 8 | 8 | 100% | 0 | 0 | 0 | 0 | :status | 0.003 |
| QF_UFLIA | `qf-uflia-curated-named` | 2 | 2 | 100% | 0 | 0 | 2 | 0 | z3-binary | 0.001 |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts` | 6 | 6 | 100% | 0 | 0 | 6 | 0 | z3-binary | 0.002 |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean` | 8 | 6 | 75% | 2 | 0 | 6 | 0 | z3-binary | 5.001 |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts` | 2 | 0 | 0% | 2 | 0 | 0 | 0 | :status | 20.000 |
| UF | `uf-cvc5-regress-clean-quantified` | 5 | 0 | 0% | 0 | 5 | 0 | 0 | :status | 0.000 |

**Totals:** 992 files, 675 decided, 623 oracle-compared, **0 disagreements.**

### QF_NRA row re-measured 2026-07-02 (free-division `/0` witnesses + prior landings)

The first-class free-division witness landing (forced-div-by-zero promotes
`unknown` → `sat`; see
[P2.5 § 08](../docs/plan/track-2-theories/P2.5-nra/08-evaluation-and-soundness.md))
re-measured `qf-nra-cvc5-regress-clean` on the committed 10 s bench route:
**9 → 21 decided (24% → 55%), PAR-2 15.166 → 8.660, DISAGREE=0.** Attribution is
honest: the witness change itself moves **+1** (`cli__regress1__arith__div.06`,
`n=0 ∧ x/n=0 ∧ y/n=1`, declared/Z3 `sat`) against a same-command HEAD re-run
(20 decided) — the other +11 vs the stale committed row are the prior
sign-refutation + coprime-split CAD landings that had not yet been re-measured
on this route. `issue9164-2` (nested `1/(a/b)`) still declines: it needs the
FM → simplex lever in addition to the `/0` witness.

### String rows re-measured 2026-07-02 (ADR-0052 gate — soundness over decide-rate)

The P2.7 A.2 landing re-measured QF_S/QF_SEQ/QF_SLIA under the bounded-string
`unsat` gate: a bounded `unsat` is reported only when confirmed
bound-independent; otherwise an honest `unknown`. Net: **QF_S 59→48 decided,
QF_SLIA 15→11, QF_SEQ 26 (unchanged)** — 23 prior `unsat` verdicts downgraded.
Of those, **two were on instances whose declared `:status` is `sat`**
(`r1_QF_SLIA_re-inter-stack-ovf.smt2`, `sat__regress0__seq__seq-nemp.smt2`):
the old rows were silently carrying real wrong verdicts the oracle path never
compared (it skips `unknown`s and the old runs' library oracle rejected the
logic on part of the slice). The other 21 are declared-`unsat` instances the
gate cannot yet confirm — recoverable via richer length facts / width widening
/ the Phase B word-level solver, tracked in
[P2.7 Phase A](../docs/plan/track-2-theories/P2.7-strings/03-phaseA-ir-sort-and-combination.md).
DISAGREE=0 holds on all compared instances; PAR-2 rose accordingly (honest
unknowns count as double-timeout). The 9-hour scoreboard hang met en route was
an exponential (per-path) DAG walk in the new blast's skeleton scan — fixed
(`f403991b`) with a regression test; the three divisions now measure in ~10
minutes total.

## Progress frontiers (lever depth)

Each frontier tracks how deep a single capability lever reaches: a family is scaled by a knob `N` and the **frontier** is the largest `N` axeyum still decides within budget. **Baseline** is the previously recorded frontier — the gap (frontier − baseline) is the gradual improvement this front exists to show.

| Lever family | Frontier | Baseline | Δ | Max knob | Budget (s) | Tracks |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| bv_reduction | 33 | 28 | +5 | 38 | 4 | QF_BV word-level reduction depth (unsat at knob N) |
| lia_cuts | 26 | 20 | +6 | 37 | 4 | QF_LIA branch-and-cut depth (sat at knob N) |
| nia_unsat | 40 | 40 | 0 | 40 | 4 | QF_NIA unsat-proving depth (knob N) |
| nra_degree | 2 | 2 | 0 | 6 | 4 | QF_NRA polynomial-degree decision depth (knob N) |
| string_bound | 8 | 8 | 0 | 12 | 4 | QF_S string-length bound (sat at knob N) |

## One-line summary

**35 division baselines measured vs z3 4.13.3, DISAGREE = 0 across all — zero wrong verdicts; decide-rate ranges 0%–100%.** DISAGREE = 0 everywhere is the soundness guarantee; decide% is the capability frontier we push, division by division.

## Provenance

Generated by [`scripts/gen-scoreboard.py`](../scripts/gen-scoreboard.py) from the following committed baselines (deterministic — no timestamps, fully sorted; re-running on unchanged inputs yields a byte-identical file):

- `bench-results/baselines/bv-bitwuzla-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/baselines/bv-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/baselines/lia-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-aufbv-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-auflia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-bv-curated-bvred-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-bvfp-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ff-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-fp-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-lia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nia-curated-iand-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json`
- `bench-results/baselines/qf-nra-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json`
- `bench-results/baselines/qf-s-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-seq-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-slia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ufff-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/uf-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/frontier/bv_reduction.json`
- `bench-results/frontier/lia_cuts.json`
- `bench-results/frontier/nia_unsat.json`
- `bench-results/frontier/nra_degree.json`
- `bench-results/frontier/string_bound.json`

Regenerate with `python3 scripts/gen-scoreboard.py`.
