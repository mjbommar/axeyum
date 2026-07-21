# What “Z3 / Lean parity” currently means — evidence audit, 2026-07-21

Status: **current correction to the parity trajectory**

## Verdict

The evidence does **not** support one claim that Axeyum is simply “far from Z3
and Lean.” It supports three different readings:

1. Axeyum is already close to, or tied with, reference solvers in some bounded
   fragment/workload cells. That is real but narrow.
2. Axeyum is far from being a drop-in Z3 replacement. The largest demonstrated
   gap is protocol, compatibility, robustness, and portfolio depth—not a
   measured universal decision-rate deficit.
3. Axeyum has a substantial solver-to-Lean proof bridge, but only partial
   Lean-core compatibility. Replacing the whole Lean language/toolchain is a
   non-goal. The current mandatory external-Lean CI claim is also not yet backed by
   a successful recorded run.

The operational mistake would be to turn either “8 versus 8” or “not Z3/Lean
parity” into a project-wide percentage. The roadmap must name the target and its
denominator every time.

## Evidence recomputed from committed artifacts

### Public-inventory adjudication

The frozen inventory scorer reports 82 decided-correct results out of 228. Its
implementation treats any definitive answer on a benchmark with no known
status as `decided_correct`. A direct projection over `inventory_raw.json`
separates the result into:

- **145 benchmarks with a known status** and 83 without one;
- **78 known-status agreements** and zero known-status disagreements;
- **4 unadjudicated decisions** on benchmarks without a known status;
- 144 explicit declines and two no-answer outcomes.

Therefore, 82/228 remains the exact legacy *scoring* result, but “82 answers
matching `:status`” and “82 independently correct answers” are false. The
soundness-bearing statement is 78 known-status agreements, zero contradictions
of known statuses, and four decisions awaiting an independent oracle or
certificate. `scripts/parity_evidence.py` and `just parity-docs` now enforce
that partition while preserving the frozen artifact.

### Exact p4dfa overlap

The same-population 20-second artifacts each contain eight decisions, but equal
counts hide different solved sets. Direct instance matching gives:

- **6 jointly decided** benchmarks, with zero joint verdict disagreements;
- **2 Axeyum-only** decisions;
- **2 Z3-only** decisions; and
- 103 decided by neither solver.

This is evidence of a bounded tie in decision count and complementary behavior,
not decision-set parity and not general QF_BV parity.

### What has and has not measured Z3 distance

The committed 35-row regression scoreboard is useful evidence: 753/992 decided,
680 oracle-compared decisions, and zero recorded disagreements. It is not a
representative SMT-LIB population. The 228-file public inventory is harder but
partial and source-skewed, and its three-solver 24-file QF_BV cell contains no
Z3 result. The attempted 64,345-file full-tree candidate produced no admissible
result.

Consequently, the **general solving-power distance to Z3 is not measured**. It
may be large, but the current repository evidence cannot quantify it. By
contrast, the production-compatibility distance is directly demonstrated: the
30-row SMT-LIB/API audit has six absent command families, seven accepted no-ops,
and zero ordered interactive textual-session rows. Z3 exposes a wide portfolio
of logics and tactics; matching that product surface is plainly a long program,
independent of any single solver benchmark. See the official
[Z3 logic overview](https://microsoft.github.io/z3guide/docs/logic/intro/) and
[tactic catalog](https://microsoft.github.io/z3guide/docs/strategies/summary/).

## Lean evidence, including the failed gate

The in-tree evidence is not superficial:

- `axeyum-lean-kernel` has a substantial dependent-term kernel and its focused
  local tests pass;
- `lean_crosscheck.rs` registers **71 proof-family builders** and can generate
  a representative official-Lean module per family; and
- supported proof routes already produce self-contained Lean source.

But the validation boundary is narrower than “Lean accepts it all”:

- the local real-Lean inductive integration test skips when no Lean binary is
  installed;
- the latest inspected CI job installed Lean 4.30, then failed inside
  `leanprover/lean-action` because no `lake-manifest.json` existed, before either
  repository external-Lean test ran ([job
  log](https://github.com/mjbommar/axeyum/actions/runs/29871224467/job/88771536340));
- the kernel audit lists projections, literal/bignum handling, quotient
  computation, generalized recursive/indexed/mutual inductives, positivity,
  and an export/import reader as residual work; and
- the LRA/LIA reconstruction preludes assert 64 arithmetic axioms. Official
  Lean can check the generated theorem relative to those axioms, but that does
  not prove the axioms true or discharge them against mathlib.

Lean itself includes parsing, macro expansion, elaboration, compilation, module
handling, and much more around the kernel, as documented in the official
[elaboration and compilation pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/).
That full-system comparison is both far and irrelevant to Axeyum's product.
The meaningful targets are a checked certificate bridge, a versioned kernel
profile, and a fail-closed Lean tactic/import path.

## Target-by-target distance

| Target | Evidence-backed status | Strategic consequence |
|---|---|---|
| Selected fragment correctness | Strong on measured cells; four public decisions remain unadjudicated | Keep multi-oracle fuzzing and certificate checks; stop converting missing status into correctness credit |
| Selected p4dfa decision count | Tied 8/113, but only 6 jointly decided and two unique decisions each | Study complementary solved sets; do not claim solver parity |
| General Z3 solving power | **Not measured** on a representative matched population | Finish durable official-style selection and run matched Z3/cvc5/Bitwuzla/Axeyum cells before assigning distance |
| Z3-compatible product surface | Far: command/session/API and portfolio gaps are directly inventoried | Prioritize the ordered session contract and conformance, not another isolated theory seed |
| Solver-proof export to Lean | Substantial implementation; external gate intended but not currently demonstrated green | Repair and record the non-skippable official-Lean gate before publication credit |
| Declared Lean-core profile | Partial, with explicit kernel and axiom gaps | Build a differential profile and discharge the 64 arithmetic axioms |
| Full Lean system | Far and out of scope | Remove it from parity language and roadmap exit criteria |

## Roadmap changes implied by the audit

1. Treat “parity” as a vector of named targets, never a percentage.
2. Preserve 82/228 only as a legacy scorer field; publish 78 adjudicated
   agreements plus four unadjudicated decisions.
3. Require exact decided-set overlap, not equal solved counts, in paired cells.
4. Label general Z3 solving-power distance **unknown/unmeasured**, not “far,”
   until a representative matched run exists.
5. Keep production Z3 replacement **far** and attach that label to the measured
   command/session, robustness, and portfolio gaps.
6. Restore a demonstrably non-skippable external-Lean job and archive its Lean
   version, checked-family count, duration, RSS, and axiom inventory.
7. Separate official-Lean source acceptance from validation of asserted prelude
   mathematics; discharge the 64 arithmetic axioms independently.
8. Make a versioned Lean-core compatibility profile the kernel target.
9. Make the fail-closed tactic/import bridge the user-facing Lean target.
10. Keep full Lean language/toolchain parity explicitly out of scope.

The near-term trajectory therefore remains correctness, deployability,
compatibility, and representative measurement. This audit narrows the work; it
does not lower the north star or promote bounded wins into a universal claim.
