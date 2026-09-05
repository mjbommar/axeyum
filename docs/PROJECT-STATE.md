# Axeyum project state

**As of 2026-08-07:** Axeyum is a working, research-grade automated-reasoning
stack with competitive results on selected fragments and substantial checked
proof coverage. It is not a drop-in Z3 replacement or a replacement for the
Lean system.

The single current engineering tracker is [`PLAN.md`](../PLAN.md). This page is
the shorter public account of what exists, what has been measured, and what is
not claimed.

## What exists

- A pure-Rust default solver path from typed terms through rewriting,
  bit-blasting, CNF, and SAT. Native solvers are feature-gated differential
  oracles and benchmark references.
- Solver routes for bit-vectors, arrays, uninterpreted functions, linear and
  selected nonlinear arithmetic, floating point, datatypes, bounded
  strings/sequences, quantifiers, and several combinations. Maturity and
  evidence coverage vary by route.
- Original-term replay for SAT models plus DRAT, Farkas, Alethe, specialized
  certificates, an independent in-tree Lean-style kernel, and self-contained
  Lean module generation for supported UNSAT families.
- A fail-closed `lean4export` format-3.1 importer with transactional publication
  and selected projection, Nat, recursive-indexed, mutual, and nested-inductive
  compatibility.
- Rust, WASM, symbolic-execution, bounded-verification, EVM, property, and
  reflection consumers over the solver's typed core, plus a proof-carrying CAS
  in the same workspace with route-specific IRs, certificates, and trust
  boundaries.

These are real implementations, not roadmap placeholders. They are not equally
complete, certified, fast, or exposed through conformant SMT-LIB text.

## What has been measured

The generated regression [`scoreboard`](../bench-results/SCOREBOARD.md) contains
35 baselines over 24 logic fragments:

- **762 / 992** files decided;
- **674 oracle-compared** decisions;
- **0 recorded disagreements**;
- decide rate from 0% to 100% depending on the selected slice.

Those are bounded convenience and regression populations, not an SMT-LIB-wide
score. Exact-content aliases and synthetic rows mean the totals must not be
treated as independent population samples.

The retained audit denominators make that limitation concrete:

- **25 / 35** rows meet the decide-strong threshold and **20 / 35** meet the
  complete dominance definition. That second figure *fell* from 23 since the
  2026-07-21 snapshot, and two of the four losses are the audit getting stricter
  rather than the solver getting worse — see the
  [gap analysis](plan/gap-analysis-z3-lean-2026-07-21.md) for the instance-level
  account. Two rows counted in the 20 audited **zero** decisions, so "fully
  dominant" and "decided nothing" are not distinguished by this ratio.
- The file-backed rows contain **927 occurrences**, **837 unique normalized paths**,
  and **778 unique byte contents**. **58 exact-alias groups** remove
  **59 additional path** identities.
- The separate public convenience inventory reports **82 / 228** decisions:
  **78 known-status agreements**, **4 unadjudicated decisions**,
  **144 explicit declines**, **2 no-answer outcomes**, and **0 wrong verdicts** against known
  statuses.
- That inventory overlaps the scoreboard by **99 exact contents**, so the two
  decide rates must not be averaged.

The public runner suppressed a parsed response when its watchdog fired, while
the competition protocol can retain a response after timeout or abnormal
termination. Because the committed raw artifact lacks the necessary stdout and
termination evidence, the two no-answer rows **cannot be retroactively classified**.
This reproduction path is therefore not claimed to be **fully competition-faithful**.

The append-only [`parity ledger`](../bench-results/PARITY.md) contains
head-to-head entries for nine divisions against division-appropriate reference
binaries on identical committed 200-file lists and a 24-second/8-GiB protocol.
The latest credited weak arithmetic and combination edges are:

| Division | Axeyum | Reference | Ratio | Disagreements |
|---|---:|---:|---:|---:|
| QF_NIA | 39/200 | 83/200 | 47.0% | 0 |
| QF_UFLIA | 113/200 | 180/200 | 62.8% | 0 |
| QF_IDL | 66/200 | 118/200 | 55.9% | 0 |
| QF_LRA | 88/200 | 134/200 | 65.7% | 0 |
| QF_RDL | 102/200 | 148/200 | 68.9% | 0 |

The stronger selected cells include QF_SLIA, QF_BV, UF, and QF_LIA.
`bench-results/parity-lists/` also carries committed QF_ABV and QF_UF lists that
have never been run, so neither is a parity cell; a benchmark list is not a
result, and this sentence named QF_ABV as one until 2026-08-21.
Read the latest entry per division for exact solver revisions, reference
configurations, load observations, and overlap; an older entry can have a higher
score without being the current credited result.

## Evidence and Lean

The newest QF_BV evidence run has 130 UNSAT decisions:

- 92 certified;
- 78 rechecked from serialized text alone;
- all 92 certified rows independently revalidated against a fresh parse and
  fresh term arena;
- zero failed checks;
- 38 bare UNSAT results because the evidence-producing route did not decide
  within 60 seconds.

These are deliberately different assurance claims. Fresh-arena checking must
not be described as serialized proof replay.

The broader audit records 42 uncertified occurrences, ten independently
checked results without Lean reconstruction, and four evidence-audit **timeouts**
(not proof-production refusals — the earlier reading of that line as a QF_NIA
`IntPow2` rejection was wrong). The current official-source proof-family
population has a retained local Lean 4.30 result of **78/78 accepted**. That
number is modules Lean READ, not propositions Lean PROVED: measured 2026-08-21,
40 of the 78 families emit a structural attestation — an axiom pair Lean cannot
fail on the merits — and 38 carry a theory reconstruction, the newest being
`qf_s_string_length`. The 75th is `qf_rdl_difference`, added
2026-08-17: real difference logic scans into the same `Lra` fragment as QF_LRA,
so it reconstructs rather than attests, and the family slice had never contained
a module from that logic. `scripts/check-lean-gate.sh` now reports
the two halves separately and floors the reasoning one. **And the reasoning half is
an upper bound, not a count.** `LeanModuleContent::of_module_source` classifies
by the PRESENCE of a structural-attestation marker, so a shim that simply does
not carry one is counted as theory reconstruction by default. Measured
2026-08-18: family `qf_nra_sos_plus_constant` reported `modules=2 theory=2
structural=0` while both of its modules said nothing whatever about their
queries — a `prop._0` wrapper had fired in place of the real SOS reconstructor.
The Lean split cannot see that class of shim; the instrument that can is the
transcription binding gate (`scripts/check-lra-hypothesis-binding.py`), which
classified exactly those instances as `attested`. Read the two together, and
treat a rise in `theory_families` unaccompanied by a rise in `bound`/`structural`
as unexplained rather than as progress. Corrected remote attestation
and exhaustive execution remain open.

Across the retained broad UNSAT denominator, **269 / 326** outcomes satisfy the
full certified, independently checked, trust-hole-free, Lean-reconstructed
conjunction; **42 uncertified** outcomes carry no certificate at all;
**10 certified** and independently checked outcomes lack Lean reconstruction;
and **3 proof-production errors** remain. All 35 audits were re-run at
`496288979` on 2026-08-21 and four rows moved: **+5 of the +7 dominant outcomes
are capability** (two `RealProduct` and one `MonomialBound` reconstruction in
QF_NRA, two `StringLength` in QF_S) and **+2 are the instrument** — two QF_NRA
synthetic instances that had been billed for a process-wide 32 s `CReal` prelude
build inside a 10 s per-instance cap, and which a directory-backed row drops
without recording a timeout. The A/B that separates the two is in the
[gap analysis](plan/gap-analysis-z3-lean-2026-07-21.md). All three of those errors are evidence-audit
**timeouts**, not rejections — three quantified-BV instances — so they are a
budget the audit did not fit inside, and the earlier reading of this line as a
proof-production *refusal* was wrong. `QF_FP/solver__fp__fp_misc.smt2` was a
fourth and is not: `4032bd660` found an unmemoized DAG walk in the classifier,
not a budget, and the QF_FP and QF_BVFP rows were re-run at `a3799dca2`. It is
now certified and independently checked in 314 ms; it is still not dominant,
because `887b52e64` deliberately withdrew the term-level FP route pending a
certified `Fpa2Bv` reduction, so it carries a `bit-blast` trust hole instead.

Two small performance controls remain useful but bounded: Axeyum and the Z3
crate each decide **8 / 113** at 20 seconds on p4dfa, on partially different
sets, while Axeyum, cvc5, and Bitwuzla each decide **19 / 24** in the separate
QF_BV three-solver control. Neither is a general solving-power result.

Lean-core compatibility is substantial but partial. The checker/importer has
selected dependent-core, projection, Nat-literal, recursive-indexed, mutual, and
nested-inductive coverage, plus the canonical quotient package and its checked
computation rules. String literals, native source elaboration, tactics, Lake,
LSP, compiler/runtime, `.olean`, `Init`/`Std`, and
mathlib compatibility remain separate unsatisfied layers.

"Lean compatible" means what the compatibility matrix measures: K0 1/1 and
K1 6/6 (an independent checker and a versioned import route), K2 through K6
at 0 — no native source, tactics, workflow, runtime, or ecosystem yet. Two
pins are distinct and every claim names which: `lean-toolchain`, the
cross-check pin (currently 4.34.0-rc1, ADR-1594/1660), and the Mathlib
corpus pin (Lean 4.30.0, mathlib4 `c5ea0035`, lean4export `a3e35a58`).
Independent checkability is measured by replay in pinned Lean: `creal`
only, 1,972 of 2,045 theorems, 48 `Type`-valued theorems Lean refuses, 25
blocked behind them (ADR-0760). Imports are a labeled tier, never the
axiom-free headline (ADR-0601, ADR-1664). `by axeyum` lets Lean check
axeyum-produced terms as a tactic (ADR-1666). Cross-library statement
identity runs through the carrier correspondence ledger (ADR-1665). Full
detail: [`docs/math-department/14-lean-lang.md`](math-department/14-lean-lang.md).

## Reliability state

Recent repairs matter as much as new solving power:

- deep recursive scans were converted to worklists after stack-overflow aborts;
- previously inert or silently empty gates now require nonzero test counts;
- the capability frontier tolerates isolated timing-edge gaps and reports host
  load instead of treating one knife-edge case as the frontier;
- arithmetic timeouts now use one query-global absolute deadline across the
  sequential exact-real, NRA, relaxation, NIA, bounded-blast, and width-ladder
  routes, with cancellation checks inside CAD and exact-arithmetic loops;
- online LRA normalization has deterministic node, coefficient-work, and cache
  ceilings: the retained high-memory case now declines around 13 MiB instead of
  reproducing its historical 8-GiB abort; and
- difference-logic probing reserves fallback time only for its measured bounded
  gate. A global split that lost controls was rejected rather than shipped.

These closures are backed by the retained A1 result and its exact gates; they do
not imply that every arithmetic query is fast or complete. Integration evidence
is revision-scoped. For current integration, compare local `HEAD`,
`origin/main`, and `git ls-remote`, then inspect hosted runs for that exact SHA.

## What is not claimed

- No universal soundness conclusion follows from zero observed disagreement.
- General solving-power distance to Z3/cvc5/competition portfolios remains
  unmeasured. The failed 64,345-file candidate produced no admissible result.
- High ratios on selected divisions do not imply broad dominance; reference
  options and solved-set overlap matter.
- Readiness artifacts, schemas, fixtures, and process-free captures are not
  live execution or launch authorization.
- The SMT-LIB/API audit still has six absent command families, seven accepted
  no-ops, and zero interactive textual-session rows.
- Independent kernel checking and bounded official-source acceptance do not
  make Axeyum a Lean distribution or establish full language/ecosystem parity.

## Where to go next

Read [`PLAN.md`](../PLAN.md). Its **Next Actions** section is the only ordered
project queue. A1 resource correctness and A2 process-free full-library
readiness are closed. The bounded A3 QF_NIA and A4 QF_UFLIA mechanisms yielded
without authorizing speculative cap increases. The next solver slice is the A5
cross-division LRA/IDL/RDL residual census, followed by proof-gap closure, route
observability, ordered SMT-LIB session semantics, official-Lean trust reduction,
the textual product surface, and routine worktree/build-cache retirement.

The pre-consolidation long-form project-state document is preserved at Git
revision `803c08439` as blob `2323ffc33fcd0f057e44064a7e45488fe91d1fe4`.
