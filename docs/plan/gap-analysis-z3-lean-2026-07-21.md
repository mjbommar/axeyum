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
  dominant under the registered row definition; **594 / 753 decisions** are
  dominant candidates.
- The rows contain **327 baseline `unsat` decisions**. The evidence audit
  reproduces **325 evidence-audit `unsat` outcomes**; **267 certified outcomes**
  have **267 independently checked outcomes**, and Lean reconstruction checks
  **260 Lean-checked outcomes**. The affected v1 rows historically contained 28
  structurally accepted but uncertified checks; the v2 refresh now records
  **0 vacuous `bare-unsat` check results** and gates checking on certification.
  The two-case 327→325 difference is explicit:
  QF_NIA proof production rejects `IntPow2` before producing evidence. Coverage
  is substantial but uneven, not 260 fully audited outcomes out of 327:
  selected QF_ABV/AUFBV/LIA/LRA/UF rows are complete while general nonlinear,
  strings/sequences, AUFLIA, and some UFLIA rows retain large proof gaps.
- The generated [proof-gap matrix](generated/proof-gap-matrix.md) applies the
  full conjunction rather than treating Lean acceptance as sufficient:
  **259 / 327 baseline UNSATs** are certified, independently checked,
  trust-hole-free, and Lean-reconstructed. The residual is 58 uncertified
  audit-row occurrences, eight trust-free Lean-reconstruction gaps, zero
  declared trust holes, and two proof-production errors. The 58
  occurrences reduce to **56 paths / 51 unique exact contents** after
  provenance deduplication.
- Its 33 file-backed baseline rows contain **927 file-backed occurrences** but
  only **837 unique normalized benchmark paths**: **90 repeated occurrences**
  come from overlapping row variants. The two synthetic rows contribute
  **65 aggregate-only synthetic cases** whose per-instance identities are
  absent.

These denominators are measurements of the committed slices, not estimates of
the entire SMT-LIB population and not proof of universal soundness.

### Harder partial public inventory

The branch's in-tree SMT-COMP scoring reproduction supplies a second,
non-combinable view. At a 120-second ceiling over all 228 public SMT-LIB files
currently present on the NAS, Axeyum records:

- **82 / 228** decided-correct, 144 explicit declines, two no-answer outcomes,
  and **0 wrong verdicts** against known `:status` values;
- 22/23 QF_UF, 14/17 QF_UFLIA, 10/12 QF_LRA, but only 6/113 on the hard p4dfa
  QF_BV family; and
- a separate 24-file QF_BV head-to-head where Axeyum, cvc5, and Bitwuzla each
  decide **19 / 24**, with Axeyum a close third on PAR-2.

This public inventory is stronger evidence of difficulty than the regression
scoreboard, but it is still a **partial convenience set**, not the official
SMT-COMP selection: p4dfa contributes 113/228 files, source families are not
population-weighted, and the three-solver head-to-head contains no Z3 cell. The
new exact-content provenance artifact finds **7 source families**, 228 unique
SHA-256 values, and **0 exact byte-duplicate groups**. That closes exact-byte
deduplication only; it does not detect renamed, option-edited, generated-family,
or semantic near duplicates. Report the 36% inventory rate and 75.9% regression-
row rate side by side with their provenance; never average them or use either
as a global solver-completeness percentage.

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

### Categorical-engine correction

The [source- and test-backed categorical-engine audit](categorical-engine-depth-audit-2026-07-21.md)
rejects another monolithic gap claim. Six interpolation families, a substantial
multi-predicate CHC/Horn direct API, and bounded verified abduction already
exist; 125/125 focused tests pass under a hard 4 GiB cap. Their correct maturity
labels are selected-fragment `decides` or `seeded`, not `absent`. The open work
is textual conformance, representative Z3/cvc5/Spacer measurement, Horn
theory/nonlinear depth, portable certification, and production hardening.
General `synth-fun`/SyGuS remains absent and must not inherit abduction's credit.

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

**Shared-schema prototype landed:** `scripts/smtcomp_repro/` implements the 2026
scoring rules, and the committed 228-file inventory establishes a harder public
view. The new machine-readable
[measurement contract](measurement-provenance-v1.json) and generated
[53-row matrix](generated/measurement-provenance-matrix.md) put both regimes on
one raw/path/content/selection/scoring/oracle vocabulary without merging their
scores. Exact inspection contracts the scoreboard's 927 file-backed
occurrences to 837 normalized paths and **778 unique byte contents**, with
**58 exact-alias groups** and 65 aggregate-only synthetic cases. The public
inventory remains 228/228 unique by exact bytes, but **99 contents overlap the
scoreboard**: 43.4% of the public view. It is a harder weighting, not independent
replication. All 53 rows record row-local PAR-2 and **0 neutral-oracle rows
on the exact populations**. Proposed ADR-0343 freezes that interpretation.

**Full-library follow-on in progress:** commit `d9e71e21` adds explicit-file
execution, a full-tree cap/family sampler, and a 52-shard s4-s7 distributor. Its
external 2024 manifest records 438,631 pool files, 64,345 selected candidates,
and 84 logics. The first 52-shard 300-second inventory terminated after 2,041
logged progress rows, with zero raw shard JSON, no live workers, no traceback,
and no structured footer. Remote `dmesg` is permission-denied, so OOM is unverified. It
is frozen incomplete with zero result credit. End-of-shard-only raw
serialization makes it non-resumable; an atomic
checkpoint/resume protocol and terminal shard manifest are prerequisites to a
rerun. Proposed ADR-0344 and the generated v2 contract now close the E0 design
slice with 18 invariants and 28 executable scenarios, including byte-identical
deterministic interruption/restart scoring projection. V2 supersedes v1 before
integration because the runner audit exposed missing process/attempt evidence.
E1a further passes 8/8 real local
`SIGKILL` recovery cells over tmpfs and ext-family storage. Production
durability remains open: E1b-E3 must integrate the writer/solver/lifecycle,
strict duplicate rejection, leases, aggregate enforcement, and multi-host recovery before a
rerun. This is not yet a third measured regime or an official selection. No result is committed,
and the selector does not yet bind the complete eligibility/status/difficulty
filters, official release and seed, corpus-tree digest, or per-selected-file
hashes. Preserve the run, but grant no matrix or representativeness credit until
those facts are archived and validated. See the
[failed-run handoff](smtcomp-full-library-candidate-run-handoff-2026-07-21.md).

The [E1b source audit](smtcomp-runner-e1b-audit-2026-07-21.md) additionally
finds that the local executor suppresses a parsed response on wall timeout,
contrary to SMT-COMP 2026 section 7.1.2, and heuristically labels every other
signal as memory exhaustion. The 228-file artifact lacks output/termination
evidence, so its two no-answer rows remain unreclassifiable rather than silently
corrected. V2 makes both facts explicit for future runs.

**Research:** classify every row/file by source hash, source family, provenance,
difficulty, theory/operators, SAT/UNSAT direction, exact/near duplication,
selection policy, and oracle source. Add SMT-COMP-style scoring and coverage
partitions without hiding unsupported or timeout outcomes. Keep raw,
deduplicated, source-balanced, and official-selection scores separate; do not
invent a subjective weighted aggregate.

**Remaining research:** v1 closes exact-byte denominators but not semantic or
near-duplicate grouping, operator profiles, a complete official-selection
manifest, matched neutral solvers on the exact populations, or a
representative-selection rule for deduplicated PAR-2. Source-balanced strata
remain reporting categories, not invented statistical weights.

**Exit:** the generated matrix reports raw and deduplicated denominators,
per-division PAR-2, coverage class, and neutral-oracle status. Full G1 exit also
requires an official-style selected population, matched non-Z3 results on that
exact population, and a preregistered deduplicated/source-stratified view. No
global parity percentage is published without those partitions.

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

The dominance audits provide five necessary denominators: 327 baseline UNSAT
decisions, 325 evidence-audit UNSAT outcomes, 267 certified and independently
checked outcomes, and 260 Lean-checked outcomes. The v1 audit's historical 28
vacuous bare-UNSAT check results are now corrected to zero in the refreshed
artifacts; the two QF_NIA proof-production errors remain visible rather than
being folded into nominal audit denominators. Remaining holes cluster by
reduction and theory.

**Research:** generate an operator/reduction trust matrix per unsat; separate
missing evidence, evidence-check failure, Lean reconstruction absence, external-
Lean rejection, and explicit trust holes. Prioritize high-prevalence reductions,
not bespoke one-row proof modules.

**Prototype landed:** `scripts/gen-proof-gap-matrix.py` deterministically emits
the checked [Markdown matrix](generated/proof-gap-matrix.md) and its
[machine-readable JSON](generated/proof-gap-matrix.json). It shows that the
largest gap is not Lean kernel expressiveness: 58 audit-row occurrences remain
uncertified and independently unchecked, all `bare-unsat`. Eight instances
already have certified, checked,
trust-free evidence and are direct reconstruction work; zero current rows retain
declared trust holes; two QF_NIA `IntPow2` rows fail evidence production. The
schema-v2 refresh corrected a stale QF_SEQ artifact: four rows created before
the string evidence soundness fix formerly reported DRAT over the bounded/flat
lowering with a declared `bit-blast` trust hole. The sound text front door now
returns bare UNSAT because that DRAT does not certify source-level sequence
semantics. Their verdicts remain unchanged, but the honest refresh enlarges the
uncertified denominator. `just parity-docs` rejects stale generated outputs.

The generated matrix also lists the eight reconstruction-only rows explicitly.
They split into two implementation mechanisms: five quantified-BV rows already
carry checked closed-universal, alternation, conjunctive-instance, or paired-
existential certificates, but the query-only Lean facade re-searches and
declines; three QF_NIA rows carry checked Alethe evidence, while query-only
reconstruction selects `la_generic` and rejects their non-conjunctive shape.
Prototype reconstruction from the selected `Evidence` object before writing any
new theorem family. This is a measured plumbing/re-derivation hypothesis, not
yet a claim that all eight will close.

The bounded [selected-evidence prototype](lean-selected-evidence-prototype-2026-07-21.md)
tests all eight rows. Existing certificate consumers reconstruct five directly:
15,174-byte closed-universal and 18,551,050-byte paired-existential modules, plus
all three QF_NIA Alethe proofs as 2,916--8,082-byte modules through the existing
EUF consumer. The QF_NIA proofs contain only congruence and resolution rules and
finish in about 0.10 seconds each below 9.5 MiB peak RSS; source-syntax routing
had incorrectly selected `la_generic`. Both BV alternation rows enter existing
reconstruction and build 8,524/13,824-command tails, but phase telemetry
separates their failures: `bug802` exceeds a hard 4 GiB cap during scoped kernel
closure, whereas `small-pipeline-fixpoint-3` closes in 7.744 seconds below
600 MiB and then misses the 30-second bound before module spooling. The
conjunctive row emits a 15,705-command residual by 2.607 seconds but does not
finish CPS tail reconstruction inside 30 seconds, below 525 MiB RSS. The
measured split is therefore five dispatch/plumbing wins and three
mechanism-specific quantified-BV export-cost cases, not eight missing Lean
fragments or one common renderer defect. The dominance denominator remains
unchanged until a production evidence-aware path and the required official-Lean
tier consume these artifacts.

The follow-on [uncertified shape census](generated/proof-gap-shape-census.md)
is produced from source hashes plus Axeyum's exact SMT-LIB parser/reachable IR,
not filenames. It contracts 58 audit occurrences to 56 paths and 51 unique
contents (five exact duplicate groups), split into 25 arithmetic and 26
string/sequence contents. Decision-backend attribution is complete: 31
occurrences return through `smtlib-string-front-door`, 15 through `auto-solve`,
and 12 through `nra-linear-abstraction`. These are coarse seams, not yet causal
certificate failures. All 26 string/sequence contents use bounded lowering and
three use word-only fallback, so a proof over the flat lowered arena alone does
not certify their source-level semantics. The leading non-exclusive structural
families are
real nonlinear multiplication (12 contents), string concatenation (nine), and
string regex (seven). Three unique string contents have zero reachable parsed-
IR terms because front-end handling discharges them before the ordinary
assertion DAG. This rejects a single “add Lean reconstruction” response: the
next prerequisite is stable route/reduction provenance at evidence production,
including the early-fold seam.

Direct code tracing is captured in the
[evidence-route provenance design](evidence-route-provenance-design-2026-07-21.md).
It identifies four distinct bare-UNSAT exits and lands dominance-audit schema v2:
certification-gated checking, existing decision-backend attribution, and an
explicit check mode. The next causal prototype is a non-breaking explained
evidence API with stable attempt dispositions and obligation fingerprints;
syntax prevalence alone does not authorize proof work.

**Exit:** every definitive result in a claimed dominant fragment has a serialized
certificate, independent recheck, zero implicit reductions, and a recorded
second-pass cost.

### G6 — Turn external Lean checking into a required tiered gate

The solver proof harness registers 71 proof families and can send representative
or exhaustive modules to official Lean. The exhaustive test is intentionally
ignored. Before this increment, CI hard-required official Lean only for the
separate inductive cross-check, so the solver-proof sweep could take its optional
local-development skip.

**Prototype landed:** the official-Lean CI job now runs the inductive cross-check
and `lean_crosscheck_representative` with one module from every registered
solver-proof family, an explicit Lean binary, two workers, and no time-budget
skip. The docs-consistency gate asserts that this command remains present.

**Remaining research:** record the first remote duration/RSS and checked-family
count, then add the exhaustive sweep on a scheduled/release cadence with an
archived checked/declined manifest and `#print axioms` summary.

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

The categorical-engine audit supplies three high-value negative controls:
`get-interpolant`, `declare-rel`/`rule`/`query`, and `get-abduct` are not parser
capabilities merely because their direct Rust engines exist. Conversely, their
missing textual commands must not be reported as missing engines. Full SyGuS is
the separate absent surface.

**Prototype landed:** the machine-readable
[conformance manifest](smtlib-api-conformance-v1.json) and generated
[30-row matrix](generated/smtlib-api-conformance.md) classify parse state,
execution mode, output representation, assurance, scope, exact tests, and
residual work independently. Source-marker validation covers both positive and
negative claims, so a newly added command makes the checked artifact stale. The
snapshot finds six absent command families, seven accepted no-ops, eight
globally recorded surfaces, five command-point surfaces, three semantic
definitions, one explicit rejection, and zero interactive textual-session
outputs. This changes the implementation priority: build one ordered session
runner before adding more isolated command helpers.

**Contract prototype landed:** the
[ordered-session design](smtlib-session-contract-design-2026-07-21.md),
[machine-readable contract](smtlib-session-contract-v1.json), and generated
[20-fixture/107-command transcript matrix](generated/smtlib-session-contract.md)
pin the control plane to SMT-LIB 2.7. The standard/source audit found that the
gap is not merely rendering: declarations and definitions are scope-local by
default, `reset-assertions` conditionally removes them,
`:global-declarations` is start-mode state, output options apply immediately,
query inspection binds to the exact most-recent check, and continued errors
must be state-atomic. Axeyum's current single arena, global parser environments,
final option maps, output no-ops, and silent pop underflow cannot express that
contract. Proposed ADR-0342 therefore stages complete command/event capture,
query snapshots, scoped external-name environments, reset epochs, and only then
canonical textual rendering.

**Exit:** a generated SMT-LIB/API matrix distinguishes parsed, semantically
implemented, round-tripped, incrementally correct, and deliberately unsupported
features. One textual runner emits every response at the exact command point,
honors scoped signatures plus option/lifecycle state, and makes errors atomic
and unsupported commands visible rather than ignored.

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

**Public-state entry point landed:** [`docs/PROJECT-STATE.md`](../PROJECT-STATE.md)
now separates built surface, measured results, partial compatibility, and
explicit non-claims without requiring readers to decode PLAN/STATUS. The parity
docs gate derives its key solver/proof denominators from committed artifacts and
checks this page plus the README, docs hub, benchmarks, and limitations for the
stale claims that previously survived measurement corrections.

**Contributor routing landed:** the machine-readable
[ownership manifest](gap-ownership-v1.json) and generated
[G0-G10 map](../contributor-guide/gap-ownership.md) name each gap's first code
owners, evidence artifacts, executable gates, ADR anchors, and next safe action.
The generator validates all repository paths and title/order identity against
this gap program; three gaps with no specific ADR expose that decision debt
rather than inventing a reference.

**Exit:** the contributor entry point is landed. Complete the structural half:
public namespaces expose the product surface rather than the internal scenario
catalog, and monolithic implementation files split only behind behavior-
preserving gates.

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

1. Review proposed ADR-0343 and retain the landed shared provenance generator;
   never merge the two current scores or describe the 228-file view as an
   independent sample.
2. Review proposed ADR-0344 and retain its landed E0/E1a contract and local
   filesystem result and v2 runner audit. Implement E1b-E3: one-solver active-
   runner/fake-solver integration, typed termination, timeout-response
   preservation, output sidecars, attempt/completion manifests, strict
   duplicate rejection, single-owner
   leases, aggregate resource enforcement, and multi-host loss recovery before
   rerunning the 64,345-file candidate.
3. Extend the selector registration with the complete eligibility/status/
   difficulty exclusions, official release and seed, corpus-tree digest, and
   per-selected-file hashes before publishing an official-style view.
4. Prototype syntax-normalized identity as an additional, mutation-tested layer
   over exact bytes; then run cvc5 and Bitwuzla on the exact admitted population
   before changing any neutral-oracle row.
5. Observe and archive the required representative official-Lean solver-proof
   CI result; size the scheduled exhaustive tier from that measurement.
6. Instrument the now-refreshed 51-content bare-UNSAT population with stable
   attempt IDs, source-to-lowered obligation maps, checker identity, and first
   uncertified reduction before selecting a shared proof mechanism. Investigate
   the four stale QF_SEQ source-invalid DRAT credits as the first bounded
   `source-side-channel-not-serialized` case. Independently prototype direct
   Lean reconstruction from selected evidence. The prototype already routes
   five of eight rows through existing consumers. Treat the remaining three as
   separate kernel-closure, compact-spooling, and CPS-reconstruction cost lanes
   under the existing 4 GiB/30-second bounds before choosing a production
   evidence-aware dispatch boundary. Add no theorem family unless selected-
   certificate reuse demonstrably declines.
7. Freeze the next multi-oracle profiles for ABV/UF and LIA/LRA.
8. Design the ordered SMT-LIB session event/result IR and transcript invariants
   from the landed conformance matrix before adding commands.
9. Measure the actual minimal native/WASM consumer profiles.
10. Use the generated ownership map to select the next bounded G10 namespace or
    module split; preserve public behavior and generated artifacts byte-for-byte.
