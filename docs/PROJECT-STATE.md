# Axeyum project state

**As of 2026-08-05:** Axeyum is a working, research-grade automated-reasoning
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
- Rust, WASM, symbolic-execution, bounded-verification, EVM, property,
  reflection, and proof-carrying-CAS consumers over the shared typed core.

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

- **25 / 35** rows meet the decide-strong threshold and **23 / 35** meet the
  complete dominance definition.
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

The append-only [`parity ledger`](../bench-results/PARITY.md) now contains
head-to-head entries for eleven divisions against division-appropriate reference
binaries on identical committed 200-file lists and a 24-second/8-GiB protocol.
The current weak edge is arithmetic and combination depth:

| Division | Latest credited Axeyum/reference | Ratio |
|---|---:|---:|
| QF_NIA | 21/85 | 24.7% |
| QF_UFLIA | 94/180 | 52.2% |
| QF_IDL | 66/123 | 53.7% |
| QF_LRA | 86/147 | 58.5% |
| QF_RDL | 105/153 | 68.6% |

All five entries record zero disagreements. Later QF_NIA code reports two gains
but has not yet earned a clean full-list ledger entry. The stronger selected
cells include QF_SLIA, QF_BV, UF, QF_ABV, and QF_LIA; exact latest values and
reference configurations must be read from the append-only ledger rather than
hand-copied here.

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

The broader audit still records 58 uncertified occurrences, eight independently
checked results without Lean reconstruction, and two QF_NIA `IntPow2`
proof-production errors. The current official-source proof-family population has
a retained local Lean 4.30 result of 70/70 accepted. Corrected remote attestation
and exhaustive execution remain open.

Across the retained broad UNSAT denominator, **259 / 327** outcomes satisfy the
full certified, independently checked, trust-hole-free, Lean-reconstructed
conjunction; **8 certified** and independently checked outcomes lack Lean
reconstruction; and **2 proof-production errors** remain.

Two small performance controls remain useful but bounded: Axeyum and the Z3
crate each decide **8 / 113** at 20 seconds on p4dfa, on partially different
sets, while Axeyum, cvc5, and Bitwuzla each decide **19 / 24** in the separate
QF_BV three-solver control. Neither is a general solving-power result.

Lean-core compatibility is substantial but partial. The checker/importer has
selected dependent-core, projection, Nat-literal, recursive-indexed, mutual, and
nested-inductive coverage, plus the canonical quotient package and its checked
computation rules. String literals, native source elaboration, tactics, Lake,
LSP, compiler/runtime, `.olean`, `Init`/`Std`, and
mathlib compatibility remain separate unsatisfied layers. Bounded K0/K1 results
do not imply complete Lean compatibility.

## Reliability state

Recent repairs matter as much as new solving power:

- deep recursive scans were converted to worklists after stack-overflow aborts;
- previously inert or silently empty gates now require nonzero test counts;
- the capability frontier tolerates isolated timing-edge gaps and reports host
  load instead of treating one knife-edge case as the frontier;
- one lazy-LIA operation that ran 109.6 seconds against a 200 ms request now
  shares an absolute deadline;
- remaining NRA interior overruns and a QF_LRA 8-GiB normalization abort are
  open P0 reliability work.

Current `main`/`origin/main` at `803c08439` was clean during the consolidation
audit. Its GitHub CI and docs workflows completed successfully on 2026-08-05.

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
project queue. The immediate priorities are arithmetic deadline/resource
correctness, current-main full-library readiness, clean QF_NIA remeasurement,
QF_UFLIA/linear-arithmetic depth, evidence closure, complete route telemetry,
SMT-LIB session semantics, and bounded official-Lean trust reduction.

The pre-consolidation long-form project-state document is preserved at Git
revision `803c08439` as blob `2323ffc33fcd0f057e44064a7e45488fe91d1fe4`.
