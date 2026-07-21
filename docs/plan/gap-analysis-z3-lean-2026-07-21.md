# Scoped Z3 and Lean gap analysis — 2026-07-21

Status: **current evidence map and research queue**

This document replaces monolithic “Z3 + Lean parity” as an operational status
label. The north star is unchanged, but progress is reported on separate axes:
solver surface, measured decision/performance depth, certified-result coverage,
Lean-kernel compatibility, and proof-assistant workflow integration. A project
can be strong on one axis and far away on another.

The generated [solver scoreboard](../../bench-results/SCOREBOARD.md), generated
[dominance audit](../../bench-results/DOMINANCE.md), and their committed JSON
inputs are authoritative for numbers. `scripts/check-parity-docs.py` derives the
snapshot below from those artifacts and rejects known stale claims in live docs.

## Executive verdict

Axeyum is not one scalar distance from Z3 or Lean:

- It is already **decision- and assurance-competitive on selected measured
  fragments**, with several rows fully certified rather than merely oracle-
  compared.
- It has **broad seed-level theory coverage**, but production depth, complete
  SMT-LIB behavior, robustness on wide public corpora, and mature heuristic
  portfolios remain materially behind Z3.
- It has a **real proof-producing Lean lane**, including an in-tree kernel and
  external-Lean module generation. It is not a complete Lean kernel, elaborator,
  tactic environment, compiler, or ecosystem replacement.
- “Full Lean-system parity” is not a useful solver milestone. The actionable
  targets are certificate coverage, kernel compatibility, and a fail-closed
  Lean tactic bridge.

The paper-level thesis should therefore remain: **correctness + deployability +
a rigorously characterized performance regime**, not universal replacement or
unqualified speed leadership.

## Current measured snapshot

The division scoreboard contains 35 rows across 24 logic labels:

- **753 / 992** files decided; **680 oracle-compared**; zero recorded
  disagreements.
- **25 / 35 rows** meet the scoreboard's `>= 80%` decide-strong threshold.
- All 35 dominance audits are complete. **23 / 35 audited rows** are fully
  dominant under the registered row definition; **616 / 753 decisions** are
  dominant candidates.
- Lean reconstruction checks **261 / 327 measured `unsat`** decisions. This is
  substantial coverage, but it is uneven: selected QF_ABV/AUFBV/LIA/LRA/UF
  rows are complete while general nonlinear, strings/sequences, AUFLIA, and
  some UFLIA rows retain large proof gaps.

These denominators are measurements of the committed slices, not estimates of
the entire SMT-LIB population and not proof of universal soundness.

### Corrected public QF_BV control

The old universal-sweep claim for p4dfa was an unmeasured premise and is false
for the committed control. At the registered
20-second, same-corpus cell:

- Axeyum's authoritative paired artifact decides **8 / 113**.
- The standalone Z3 crate artifact decides **8 / 113**.
- The separately recorded Z3 CLI control decides 9/113; the decided sets are
  not identical.

This is **bounded corpus parity**, not general QF_BV parity. Both systems time
out on most of this deliberately hard corpus. The residual still motivates SAT
search work, but it does not support a “Z3 sweeps; Axeyum cannot solve” framing.

### Correctness and downstream controls

- The independent QF_BV campaign records 4,000 / 4,000 four-way
  Z3/cvc5/Bitwuzla/Axeyum agreements over widths 1, 4, 8, 16, and 32, with
  1,538 SAT model replays. This is strong generated-profile evidence, not a
  substitute for broader public-corpus coverage.
- The preregistered Glaurung six-cell study has all six cold/warm solver cells
  agree on every check. Warm Axeyum beats warm Z3 on three of four drivers and
  loses on DptfDevGen; warm Bitwuzla wins all four. Performance leadership is
  workload-dependent.
- Authoritative finding parity is closed for the bounded four-driver campaign,
  but broader labeled recall and harder-driver resource behavior remain
  separate questions.

## What each parity label must mean

| Label | Required evidence | Current reading |
|---|---|---|
| Fragment decision parity | Same supported query class; matched corpus, budget, hardware, and verdict directions; comparable decided set/PAR-2 | Achieved on selected rows and bounded controls; unmeasured or incomplete elsewhere |
| Production Z3 replacement | Broad SMT-LIB surface, incremental robustness, portfolio depth, full-corpus measurements, stable API/tooling | Far; this is the main engineering-depth gap |
| Certified-result parity | Every definitive result in the claimed fragment has independently rechecked evidence with an empty trust-hole set | Achieved on 23 complete measured rows; partial globally |
| Lean-kernel compatibility | Accept/reject the same core proof terms and declarations as official Lean for a stated format/profile | Partial; useful solver-proof subset exists, full kernel compatibility does not |
| Lean workflow integration | Fail-closed tactic/import path that discharges real Lean goals and reports axioms/trust | Not shipped; out-of-band modules exist |
| Full Lean-system parity | Parser, macros, elaborator, unification, tactics, compiler, modules, language server, ecosystem | Out of scope as a solver milestone |

## Ranked gap program

### G0 — Stop documentation from overruling measurements

**Why first:** stale prose reversed the p4dfa conclusion and simultaneously
understated current proof coverage. That is a publication-integrity defect.

**Prototype:** `scripts/check-parity-docs.py` reads the committed division,
dominance, and p4dfa JSON artifacts; reports the current denominators; rejects
the known stale phrases; and checks this document's evidence markers.

**Exit:** the gate runs in `just check`; generated artifacts and live prose
cannot disagree on the guarded claims.

### G1 — Replace aggregate decide-rate with a coverage-weighted parity matrix

The 992-file aggregate mixes synthetic, curated, duplicated, small, and public
regression slices. It is useful for regression tracking but not a population
claim.

**Research:** classify every row by provenance, difficulty, theory/operators,
SAT/UNSAT direction, duplication, and oracle source. Add SMT-COMP-style scoring
and coverage weights without hiding unsupported or timeout outcomes.

**Exit:** one generated matrix reports both raw and deduplicated denominators,
per-division PAR-2, coverage class, and neutral-oracle status. No global parity
percentage is published without those partitions.

### G2 — Measure production depth, not isolated wins

p4dfa establishes one hard SAT-search control, while Glaurung establishes a
small-formula embedded regime. Neither predicts the other.

**Research:** maintain matched 3/20/60-second curves on arithmetic-heavy and
bit-logic QF_BV; add memory/RSS and warm/cold partitions; classify every unknown
by encoding, search, theory, resource, or unsupported cause.

**Exit:** at least three independently sourced QF_BV families and the four
Glaurung drivers have matched Z3/Bitwuzla curves with fixed manifests and
decision-set overlap, not only solved counts.

### G3 — Broaden neutral correctness evidence

Z3 must not be both sole performance baseline and sole oracle. The current
four-oracle fuzz and Bitwuzla Glaurung controls are the right pattern.

**Research:** extend four-oracle generation to arrays/UF, LIA/LRA, FP, strings,
and quantified finite fragments. Record three-way/four-way disagreement triage,
model replay, and proof-route coverage separately.

**Exit:** each paper-claimed fragment has at least two independent external
oracles where available, both SAT and UNSAT directions, and a committed
adversarial profile.

### G4 — Close the weak decide-rate frontiers before polishing their proofs

The largest measured decision gaps remain quantified LIA/UF rows, QF_SLIA,
QF_UF coverage, strings, and selected mixed-theory rows. Seeded capabilities do
not imply practical completeness.

**Research:** derive residual-shape censuses from the exact unsupported/unknown
instances; rank mechanisms only after the census names a repeated missing
primitive. Preserve `unknown` rather than generalizing from a single benchmark.

**Exit:** every targeted mechanism moves a preregistered public row and survives
an adversarial differential gate; rejected mechanisms remain documented.

### G5 — Make proof coverage a first-class denominator

The dominance audits now provide the correct base: 261/327 measured UNSATs are
Lean-checked, not “approximately 15 rows have a route.” Remaining holes cluster
by reduction and theory.

**Research:** generate an operator/reduction trust matrix per unsat; separate
missing evidence, evidence-check failure, Lean reconstruction absence, external-
Lean rejection, and explicit trust holes. Prioritize high-prevalence reductions,
not bespoke one-row proof modules.

**Exit:** every definitive result in a claimed dominant fragment has a serialized
certificate, independent recheck, zero implicit reductions, and a recorded
second-pass cost.

### G6 — Turn external Lean checking into a required tiered gate

The solver proof harness registers 71 proof families and can send representative
or exhaustive modules to official Lean. The exhaustive test is intentionally
ignored, and current CI hard-requires official Lean only for the separate
inductive cross-check.

**Prototype plan:** add a required representative solver-proof job with one
module per family and no time-budget skips; run the exhaustive sweep on a
scheduled/release cadence; archive checked/declined counts and `#print axioms`.

**Exit:** representative external-Lean coverage is required on every change to
reconstruction/kernel code; the exhaustive campaign is reproducible and has no
silent skips or `sorryAx`.

### G7 — Separate Lean certificate goals from kernel-compatibility research

The in-tree kernel already implements dependent core terms, declarations,
reduction, proof irrelevance, and useful inductives. Explicit gaps include
projections, arbitrary-precision/literal typing, quotient reduction, recursive
indexed families, and nested/mutual inductives.

**Research order:** bignum literals before literal typing; projections and
structure eta; recursive-indexed/positivity spine; quotient computation; import
format. Keep arithmetic-prelude axioms separately enumerated and discharged.

**Exit:** a versioned Lean-core compatibility profile and differential kernel
corpus replace the ambiguous phrase “Lean parity.”

### G8 — Measure the SMT-LIB and API compatibility surface

Theory engines are only one part of a Z3-class replacement. Remaining command,
option, recursive-definition, model/value/proof, incremental, optimization, and
error-semantics differences need an explicit conformance suite.

**Exit:** a generated SMT-LIB/API matrix distinguishes parsed, semantically
implemented, round-tripped, incrementally correct, and deliberately unsupported
features. Unsupported commands fail visibly rather than being ignored.

### G9 — Prove deployability claims with real consumer profiles

Track minimal-feature linkage, WASM build/runtime size and latency, cold/warm
latency, RSS, proof size/check time, and fallback rate. Tie every headline to a
real consumer configuration rather than a buildable-but-unused feature set.

**Exit:** one reproducible Pareto table covers time, memory, artifact size,
certificate coverage, and decided rate for native and WASM consumers.

### G10 — Reduce reviewer and contributor risk

The flat solver API, monolithic reconstruction/theory files, duplicated policy
machinery, and battle-log documentation make correct work difficult to audit.
Treat modularization as research-infrastructure work: it must preserve generated
artifacts and public behavior byte-for-byte before enabling new mechanisms.

**Exit:** a short contributor entry point maps each measured gap to its owning
module, corpus, checker, and ADR; public namespaces expose the product surface
rather than the internal scenario catalog.

## Execution order

1. Land G0 and correct live claims.
2. Build G1's generated coverage-weighted matrix from existing artifacts.
3. Run G2/G3 as the measurement lane while G5/G6 harden proof evidence.
4. Select G4 mechanisms only from measured residual shapes.
5. Advance G7/G8 compatibility work independently of performance claims.
6. Use G9/G10 to make the resulting artifact reproducible and reviewable.

This order deliberately separates cheap measurement/configuration work from
architectural projects. It also prevents a new capability seed from being
reported as parity before it climbs the measured and certifying rungs.

## Immediate next actions

1. Add the parity-doc consistency gate to `just check`.
2. Correct p4dfa and dominance statements in PLAN, STATUS, and SCOREBOARD.
3. Generate the first provenance/deduplication inventory for all 35 rows.
4. Reconcile the current SMT-COMP scoring prototype with G1's matrix.
5. Add the required representative official-Lean solver-proof CI job.
6. Generate the per-reduction proof-gap matrix from dominance audits.
7. Freeze the next multi-oracle profiles for ABV/UF and LIA/LRA.
8. Define the SMT-LIB/API conformance schema before adding commands.
9. Measure the actual minimal native/WASM consumer profiles.
10. Publish a one-page contributor map backed by these generated artifacts.
