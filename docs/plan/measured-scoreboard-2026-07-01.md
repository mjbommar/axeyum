# Measured per-division scoreboard vs Z3 — 2026-07-01

Fresh head-to-head of axeyum `check_auto` vs the `z3` 4.13.3 binary
(`measure_corpus`, curated non-incremental corpus, 3 s cap unless noted, via
`scripts/mem-run.sh`). **`DISAGREE = 0` on every division measured** — soundness
holds across the board. "considered" excludes files z3 rejects (cvc5-specific
syntax) or that don't flat-parse.

## The table (axeyum decided / z3 decided / gap)

| Division | axeyum | z3 | gap | note |
|---|---|---|---|---|
| **QF_NRA** | **10 / 36** | 36 / 36 | **−26** | the frontier; Boolean structure + CAD reach ([P2.5](track-2-theories/P2.5-nra/)) |
| **QF_NIA** | **20 / 28** | 28 / 28 | **−8** | second frontier; UNSAT-side (incr. linearization, [P2.5 Phase E](track-2-theories/P2.5-nra/07-phaseE-nia.md)) |
| QF_ABV | 175 / 177 | 177 / 177 | −2 | very strong |
| QF_AUFLIA | 4 / 6 | 6 / 6 | −2 | `bug330` deadline hang (#63) |
| QF_LRA | 5 / 7 | 6 / 7 | −1 | |
| QF_LIA | 9 / 10 | 10 / 10 | −1 | |
| QF_S (strings) | 56 / 69 | 57 / 69 | −1 | bounded encoder near parity on curated |
| QF_SLIA | 14 / 18 | 15 / 18 | −1 | |
| QF_FP | 16 / 16 | 16 / 16 | 0 | parity |
| QF_DT | 3 / 3 | 3 / 3 | 0 | parity |
| QF_AX | 8 / 8 | 8 / 8 | 0 | parity |
| QF_ALIA | 5 / 5 | 5 / 5 | 0 | parity |
| QF_UFLIA | 8 / 8 | 8 / 8 | 0 | parity |
| QF_UFBV | 6 / 6 | 6 / 6 | 0 | parity |
| **QF_UF** | **42 / 48** | 41 / 48 | **+1** | axeyum ahead |
| **QF_BVFP** | **7 / 7** | 6 / 7 | **+1** | axeyum ahead |
| **QF_SEQ** | **16 / 21** | 14 / 21 | **+2** | axeyum ahead |
| QF_FF | 0 / 0 | 0 / 0 | — | z3 can't parse (finite fields); not adjudicable here |
| QF_UFFF | 0 / 0 | 0 / 0 | — | same |

## Reading

- **The frontier is NRA and NIA, by a wide margin.** Every other measured
  division is within −2 of z3, and axeyum is *ahead* on QF_UF, QF_BVFP, QF_SEQ.
  This validates the plan's Track-2 focus on [P2.5 nonlinear](track-2-theories/P2.5-nra-cad.md).
- **Strings are near-parity on the curated subset** (QF_S 56/57, QF_SLIA 14/15).
  The large string gap the P2.7 program targets is **unbounded** strings / the
  full SMT-LIB corpus, not this curated slice — so P2.7 is a *reach/coverage*
  investment, not a curated-decide-rate emergency. Prioritize NRA/NIA first.
- **The −1/−2 divisions** (ABV, AUFLIA, LRA, LIA, S, SLIA) are individual hard
  instances: QF_AUFLIA's −2 is the `bug330` deadline hang (#63); QF_ABV's −2 is
  the deep residual noted in prior sessions. Scattered single-instance work, lower
  ROI than the NRA/NIA frontier.

## Soundness footnote (2026-07-01)

An eq-recombination experiment on the NRA case-split surfaced a **div-by-zero
congruence gap** in `eliminate_real_div` (fresh `r` per division occurrence loses
`x=y ⟹ (/x 0)=(/y 0)`); it is **not reachable by the shipped solver** (the landed
case-split feeds split-form cubes that decline these) and is tracked as #69 with a
guardrail. `DISAGREE=0` holds on the shipped solver across all divisions above,
including the division instances (`div.04`/`div.07`).

## How to reproduce

```sh
for D in QF_NRA QF_NIA QF_UF QF_ABV QF_S ... ; do
  cargo run --release -p axeyum-bench --example measure_corpus -- \
    corpus/public-curated/non-incremental/$D 3000
done
```
Re-run and update this file when a decider changes; no decide-rate claim without
it (the standing "measure don't seed" rule).
