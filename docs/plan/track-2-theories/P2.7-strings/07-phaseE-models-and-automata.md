# P2.7 · Phase E — Unbounded model construction + automata/stabilization fallback

**Size:** L–XL · **Depends on:** Phases B–D · **Makes `sat` models real for
unbounded strings, and adds a complementary second arm.**

> Two pieces: (1) **model construction** — how to produce a concrete satisfying
> string when lengths are symbolic and unbounded (length bucketing + cardinality);
> (2) the **automata/stabilization fallback arm** — a Z3-Noodler-style second
> decision procedure for regex/equation-heavy instances where the word-equation
> core stalls, built on a **pure-Rust** automata substrate (the no-C/C++ rule
> forbids MATA).

## Part 1 — Unbounded model construction (length bucketing + cardinality)

The cvc5 CAV-2014 approach, which produces a SAT witness **without a global length
bound**:
1. Collect all string-like terms; **separate by length** — partition equivalence
   classes into buckets that *could* share a length.
2. On saturation, give each bucket a **unique concrete length**.
3. A **cardinality (`Card`) rule** guarantees there are enough distinct alphabet
   constants of that length to assign each class a **distinct** witness (this is
   where the **total order on the Unicode alphabet** is load-bearing).
4. **Skeleton construction:** for a class with unknown length, build
   `seq.unit(k₀) ++ … ++ seq.unit(k_{n-1})` with fresh per-position skolems, then
   read the model values off the assignment.

Every constructed model must **replay** through the ground evaluator against the
original term (the hard rule).

| exit | unbounded SAT instances produce a concrete, replay-checked string model |

## Part 2 — The automata / stabilization fallback arm

The word-equation core and the automata approach are **highly complementary** —
Z3-Noodler won 2024 precisely because stabilization dominates regex/equation-heavy
sets where normalization stalls. We add it as a **second arm**, dispatched when the
core budget is hit.

- **Stabilization-based procedure** (*Solving String Constraints with Lengths by
  Stabilization*, OOPSLA 2023): represent constraints as automata, iteratively
  refine ("stabilize") under length constraints; **Nielsen transformation** for
  quadratic equations.
- **Pure-Rust substrate** — build the automata on `regex-automata` /
  `aws-smt-strings` (NOT MATA). This is the larger lift; it is explicitly the
  *second* arm, landed after the core + regex + extended functions work.

| exit | a stabilization arm decides regex/equation-heavy instances the core leaves `unknown`; first sound verdict across arms wins |

## Tasks

| id | task | key refs | size | exit |
|---|---|---|---|---|
| T-E.1 | length bucketing + `Card` rule + skeleton model construction | cvc5 `model_cons` (CAV 2014) | L | unbounded SAT models built + replayed |
| T-E.2 | cardinality conflicts on finite-alphabet over-population | cvc5 `base_solver::checkCardinality` | M | no false SAT on alphabet exhaustion |
| T-E.3 | (2nd arm) automata representation on pure-Rust substrate | regex-automata / aws-smt-strings | XL | constraints → automata, emptiness, length-aware |
| T-E.4 | (2nd arm) stabilization loop + Nielsen transformation | OOPSLA 2023 | XL | regex/equation-heavy instances decided |
| T-E.5 | portfolio dispatch core ↔ stabilization arm; first **sound** verdict wins | Z3-Noodler 1.3 orchestration (TACAS 2025) | M | measured decide-rate up; DISAGREE=0 |

## Soundness

- Model construction: every witness replays; cardinality rule prevents false SAT on
  finite-alphabet exhaustion.
- Two arms must **agree or one says `unknown`** — never two different verdicts; the
  dispatcher takes the first **sound** (replay-checked / certified) verdict.
- Remember the SMT-COMP 2021 soundness incidents — fuzz the arm independently.

## Exit criteria

- Unbounded SAT instances yield concrete, replay-checked models.
- The stabilization arm decides regex/equation-heavy residual the core can't;
  portfolio dispatch is sound.
- Measured decide-rate on public QF_S/QF_SLIA approaches cvc5/Z3-Noodler;
  `str_differential_fuzz` DISAGREE=0.
