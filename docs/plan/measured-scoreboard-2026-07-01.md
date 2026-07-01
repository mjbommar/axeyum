# Measured per-division scoreboard vs Z3 — 2026-07-01

Fresh head-to-head of axeyum `check_auto` vs the `z3` 4.13.3 binary
(`measure_corpus`, curated non-incremental corpus, 3 s cap unless noted, via
`scripts/mem-run.sh`). **`DISAGREE = 0` on every division measured** — soundness
holds across the board. "considered" excludes files z3 rejects (cvc5-specific
syntax) or that don't flat-parse.

## The table (axeyum decided / z3 decided / gap)

| Division | axeyum | z3 | gap | note |
|---|---|---|---|---|
| **QF_NRA** | **11 / 36** | 36 / 36 | **−25** | the frontier; Boolean structure + CAD reach ([P2.5](track-2-theories/P2.5-nra/)) |
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

## Soundness finding + fix (2026-07-01)

Adding **division coverage to `nra_differential_fuzz`** (previously it generated
none) caught a **pre-existing wrong-sat** in the NRA division path: the internal
engine replays candidates against the div-*eliminated* form (`x/y → r`,
`(y=0) ∨ (x=r·y)`), so a `y=0`/free-`r` candidate satisfies the eliminated form
while the original `x/0` evaluates (in the ground evaluator) to a fixed value that
does not — e.g. `1/w < 0` returned `sat` with `w=0`. Fixed (commits `0761bf8e`
division congruence + `b38c0439` a final replay guard: every `sat` re-checked
against the *original* assertions, declining to `unknown` on violation). Verified
`DISAGREE=0` + no wrong-sat on the enhanced division fuzz, `nia` fuzz, and lib
613/613. This is why the frontier work is worth the fuzz-hardening discipline —
extending the adversarial gate found a real latent bug. Follow-up #70 recovers the
genuine division sats (replay against the true original *in-engine*).

## Frontier bottom-line (root-caused 2026-07-01)

Both frontier gaps bottom out at the **same** missing capability, not at surface
features:

- **QF_NRA** — the CAD only decides flat conjunctions; the Boolean case-split
  ([`5ede57f4`](../..)) routes cubes to it, but most remaining cubes exceed the
  CAD's degree/variable reach or the ≤2-cross-product relaxation cap.
- **QF_NIA** — the 8 undecided cluster (integer div/mod by *variable* divisor,
  `iand`, nonlinear-int) does **not** bottom out at div/mod elimination: even the
  *manually* Euclidean-eliminated `div.03` is undecided, because it is unsat over ℤ
  but **sat over ℝ** (so `int_real_relax` can't transfer), and the unsat needs
  integer tightening (`q<1 ⟹ q≤0`) plus a sign lemma (`q≤0 ∧ n>0 ⟹ q·n≤0`).

Both need **integer-aware incremental linearization** (a CEGAR loop: tighten
integer bounds on abstracted product vars + sign/zero/monotonicity/tangent lemmas,
solved over LIA keeping integrality) — [P2.5 Phase B](track-2-theories/P2.5-nra/04-phaseB-incremental-linearization.md)
for reals, [Phase E](track-2-theories/P2.5-nra/07-phaseE-nia.md) for integers
(task #71). This is the substantial next engine investment; there are **no
remaining quick frontier wins** (measured, not assumed).

**Phase E foundation landed (`815ce074`):** `refute_nia_by_sign_lemmas` — an
integer nonlinear UNSAT refuter (abstract products + valid sign lemmas, solved
over the integer DPLL(T), unsat-only, sound-by-construction). It decides the
*eliminated* `div.03` (unsat) that was previously undecided — validating the
approach. It is +0 on the curated corpus itself because the div/mod declines need
**E.0c** (variable-divisor Euclidean axioms, task #71) to *reach* it; that is the
next corpus-impacting step (refutation-sound; prerequisite = extend the NIA fuzz's
already-present div/mod coverage from constant to *variable* divisors).

### Session outcome (2026-06-30 → 07-01)

- **QF_NRA 9 → 11** — Boolean case-split into the CAD (`5ede57f4`) + division
  congruence (`0761bf8e`).
- **A pre-existing div-by-zero WRONG-SAT found & fixed** (`b38c0439` + `a06dc46a`)
  — by extending `nra_differential_fuzz` with division coverage, then guarding /
  threading sat-replay against the true original. Real soundness win.
- Robustness: LRA-replay + `finish_sat` i128 overflow → graceful `unknown`.
- **Phase E foundation** (`815ce074`) + this measured frontier map. Every change
  gated `DISAGREE=0`.

## How to reproduce

```sh
for D in QF_NRA QF_NIA QF_UF QF_ABV QF_S ... ; do
  cargo run --release -p axeyum-bench --example measure_corpus -- \
    corpus/public-curated/non-incremental/$D 3000
done
```
Re-run and update this file when a decider changes; no decide-rate claim without
it (the standing "measure don't seed" rule).
