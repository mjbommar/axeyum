## Next Actions

Work in this order unless new evidence reveals a wrong verdict, crash, data-loss
risk, or invalid gate. Those are P0 and preempt the queue.

The accepted library programme below is the new cross-cutting focus. It does
not erase the retained A1–A11 solver programme: P0 safety work
preempts it, P1 graph/artifact authority may run beside A5/A6, and production
pilots begin only after their authorities land. A3 remains incomplete but
yielded, A4 yielded, and A5 remains the first active solver-depth item.

<!-- plan-generated: lane-status -->

### L0–L4 — Graph-directed trusted library programme (`TODO`, P0–P2)

Run the accepted [ADR-0717](docs/research/09-decisions/adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md)
programme in this order:

1. **L0, P0 — theorem credit:** exact statement and closure identity, forbidden
   trust/target checks, nonzero coverage, semantic controls, and independently
   graded replay for every changed settled fact. See the
   [safety roadmap](docs/plan/trusted-library-safety-roadmap-2026-08-30.md).
2. **L1, P1 — graph authority:** freeze the pinned source/extractor and emit
   complete, sealed declaration edge layers; proof/value edges remain forbidden
   producer input. See the [artifact](docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md)
   and [graph](docs/plan/graph-directed-library-roadmap-2026-08-30.md) roadmaps.
3. **L2, P1 — infrastructure frontier:** join exact Axeyum identities,
   representability, destinations, obstructions, producers, and provenance;
   expose every score component and preserve `fact-frontier.py` legality.
4. **L3, P2 — discovery pilots:** after L0–L2, run one substrate, one reusable
   producer, and one destination pilot with falsification before search and a
   frozen local-ready comparison. See the
   [efficiency roadmap](docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md).
5. **L4, P2 — Lean adapter:** complete artifact replay, then an elaborated-goal
   adapter whose result Lean checks. Source/elaboration features remain blocked
   until a preregistered population measures demand.

Each phase's roadmap exit is mandatory. Zero-yield pilots remain results; raw
degree never authorizes work; broad Lean-source compatibility is not an exit.

### A1 and A2 — `DONE`, archived

Both completed. Moved to
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md)
so this file carries actions that are next.
### A3 — Re-certify and deepen QF_NIA (`WIP`, P1)

**Why now.** The current clean ledger entry is 39/200 versus 83/200 = 47.0%
(`bench-results/PARITY.md`, 2026-08-21T22:17:23Z, solver commit `cb4a391c9`;
zero disagreements), the weakest retained division on the board. Twelve
Axeyum-only decisions also make replay and causal classification important,
not just score growth.

**Completed checkpoint.** The exact 67-row causal census and 13-row diagnostic
are retained. Giant `distinct` expansion is bounded and typed. Model
reconstruction no longer erases oracle declines or fabricates a default model.
Probe-model reuse failed its seven-target retention gate and its temporary code
was removed. Focused SMT-LIB, solver, explanation, DPLL, NIA-linearization,
route-trace, integration, Clippy, docs, and link gates are green. One aggregate attempt found the
load-sensitive coupling deadline; the repaired attempt passed all code, solver,
frontier, CAS, rustdoc, resource, policy, resume, and Lean suites but found a
one-field stale generated CI-workflow identity at final parity-docs. Both defects
are repaired. Exact topic `3586c41d9` passed one uninterrupted external-frontier
`CARGO_BUILD_JOBS=2 just check` with exit 0 and a clean tracked tree. Topic push,
merge `0c31baf97`, and combined-main `just check` are complete and green.
Exact-SHA docs run `31190516093` and CI run `31190517748` are terminal failures
at the registered-`just` path lookup, while every non-doc CI job is green.
Repair `259797459` is integrated at `bd413357c`; exact-SHA docs run
`31192792512` and CI run `31192792245` are terminal green. This remote gate is
separate from the green solver gates.
The reconstruction-deadline diagnostic then measured both targets with
size-inadmissible dense Gomory and zero B&B nodes after deadline expiry. Its
follow-up root-repair discriminator was route-unstable under host contention,
so the cluster was rejected and every temporary solver edit removed. See the
[`v1 result`](docs/plan/qf-nia-a3-reconstruction-deadline-cluster-v1-result-2026-08-07.md).
The next cluster confirmed repeated size-admission broad cores on `SAT14/1051`
(3/3) and `SAT14/1280` (2/3). Its preregistered four-group deletion mechanism
made clauses narrower but spent up to four extra exact-theory calls per
conflict, moved both budget stops earlier, and decided neither target. The
implementation was rejected and fully removed. See the
[`large-core v1 result`](docs/plan/qf-nia-a3-large-core-cluster-v1-result-2026-08-07.md)
and
[`group-deletion v2 result`](docs/plan/qf-nia-a3-large-core-group-deletion-v2-result-2026-08-07.md).

The cheaper
[`relevance-activated bound-ladder experiment`](docs/plan/qf-nia-a3-relevant-bound-ladders-v1-result-2026-08-07.md)
then activated hundreds of checked adjacent implications without an additional
theory-oracle call, but all six target observations remained `unknown`. Its
target gate failed, controls and aggregate runs were not authorized, and all
temporary solver code was removed. The resulting
[`typed-budget partition`](docs/plan/qf-nia-a3-budget-partition-v1-result-2026-08-07.md)
classifies all 52 deferred rows as 37 mixed width timeouts, 11 all-SAT
pre-lowering estimate refusals, three UNSAT combined-theory timeouts, and one
UNSAT replay-detected model overflow. Fresh current-baseline traces show the
four-row UNSAT tail is downstream of the owning exact-search stop and cannot be
recovered soundly by the SAT-only width ladder.

The v1/v2
[`clause-estimate result`](docs/plan/qf-nia-a3-clause-estimate-attribution-v2-result-2026-08-07.md)
closed the final selected route at its complete-record gate without changing
production code, and then the [2026-08-21 diagnosis](docs/research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md)
(gap analysis §9 row 4; `docs/plan/status/118-nia-diagnosis.md`) closed the
question of whether a cheap mechanism exists: it does not, and three were
measured to prove it. "Multi-year catch-up" for the search is confirmed, but
the sizing was wrong three ways — cvc5 1.3.4 is reachable on this host
(`/nas3/data/axeyum/harness/bin/cvc5`, not on `$PATH`; two prior documents
recorded it absent); z3 is not a stand-in for cvc5 outside the linear
divisions (same run, z3 136/200 vs cvc5 76/200, cvc5's decided set a strict
subset of z3's); and the deficit is concentrated in one benchmark family —
`20170427-VeryMax/ITS` is 134 of the 200 pinned files and 74 of the 104
misses, and excluding it the same run gives 29/39 = 74.4% of cvc5, around
QF_RDL's rate. Every specialised nonlinear-integer route declines, so the
generic `int-blast-ladder` is decisive on 158/161 undecided files; its width
ladder admits a rung only if every integer literal fits, so a `2^30` Farkas
coefficient leaves 32 files with one live rung, of which zero are decided.
Three candidate fixes were built and measured, and refuted: lifting the
projected-clause ceiling by the measured 9.4x over-approximation gave 0 of 49;
admitting `nia-linearize` past the `dpll_lia` pre-SAT envelope gave +1 of 200;
4x the wall clock gave 0 of 20 `Timeout` files. z3 decides 74 of the 104
misses in under 5s — a different algorithm, not lost time.

**Next slice.** None is currently evidence-authorized. Preserve the 39/200
ledger, every negative control above (including the 2026-08-21 diagnosis's
three refuted fixes), the 64,000,000 pre-allocation ceiling, and original-term
replay, then move to A4. Resume A3 only when independent new evidence
identifies a bounded mechanism — the diagnosis names one unpriced residual
hypothesis, an eager small-domain product split reached without the lazy
refinement loop that fails (`nia_linearize.rs:750-777`); do not revive
probe-model reuse, reconstruction reservation, group deletion, relevance
ladders, fresh-parse clause attribution, the projected-clause ceiling lift, the
`nia-linearize` pre-SAT admission, or a flat wall-clock increase, and do not
raise general caps.

**Exit.** One preregistered cluster improves a fresh whole-list result without
losing any of the 39 decisions; all SAT answers replay on the original terms
and the ledger remains disagreement-free.

**Stop.** Do not optimize on the 12 Axeyum-only cases as if they were reference
failures, and do not raise general caps to convert time into apparent breadth.

### A4 — Deepen QF_UFLIA combination (`WIP`, P1)

**Why now.** QF_UFLIA was 94/180 (52.2%) with zero Axeyum-only decisions and 86
reference-only cases, making it the clearest combined-theory depth gap. The
theory-model reuse result had stopped negatively.

**Completed checkpoint.** The theory-core-minimisation fix
([ADR-0538](docs/research/09-decisions/adr-0538-theory-core-minimisation-is-rationed-by-oracle-calls-not-by-core-width.md),
`40a1ab969`, `docs/plan/status/agent-lia-core-minimisation.md`) closed the
gap's confirmed cause: `dpll_lia.rs` used one constant to decide both whether a
theory conflict core was minimised at all and whether it was charged against
the wide-clause retention budget, so cores too wide to minimise were exactly
the cores whose width then exhausted retention. Minimisation is now rationed
by `MINIMIZATION_ORACLE_CALL_BUDGET`, a deterministic oracle-call count, while
`WIDE_THEORY_CORE_ATOMS` (128, unchanged) only decides retention by retained
width. Current clean ledger entry: **113/180 = 62.8%**
(`bench-results/PARITY.md`, 2026-08-21T19:56:23Z, solver commit `cb4a391c9`;
zero disagreements against z3 and against declared `:status`), up from 94/180
— a net +19 on the ledger (measured directly against the pre-fix same-day
sweep at 95/180, +18; the diagnosis lane's private A/B measured +22 from a
92-file baseline on a snapshot build). QF_LIA, QF_LRA, QF_IDL each moved 0 from
this fix; QF_RDL +1; QF_SLIA (not this division) +2 — see
`bench-results/PARITY.md`'s 2026-08-21 note for the full six-division
re-sweep this fix required.

**Next slice.** None is evidence-authorized as an immediate solver-code slice.
The 26 wide-integer rows (13% of the division) never reach the solver at all —
rejected at the parser for `Int` literals beyond `i128` (2^256 EVM words);
cvc5 decides 6 of them, z3 decides 12 (gap analysis §9 row 4b). This is
ADR-sized, not a parser fix: `Value::Int(i128)` underlies every arithmetic
route (performance review recommendation 5, `Rational` at
`crates/axeyum-ir/src/rational.rs:12` has the same `i128` shape; `wide.rs` and
`poly_big.rs` are the existing bignum precedent). Do not revive the theory-
model reuse route; the 26 wide-integer rows remain ADR-0376 controls until an
`i128`-fast-path/bignum-slow-path ADR authorizes touching `Value::Int`.

**Exit.** One preregistered, replay-checked cluster improves the clean full-list
result without losing any of the 113 decisions or weakening retained controls.

**Stop.** No general cap increase, speculative recursive MBQI, or unchecked SAT
model credit.

### A5 — Consolidate linear arithmetic after warm simplex and DL (`WIP`, P1)

**Why now.** QF_LRA 88/134 = 65.7%, QF_IDL 66/118 = 55.9%, and QF_RDL
102/148 = 68.9% (`bench-results/PARITY.md`, 2026-08-21, solver commit
`cb4a391c9`; zero disagreements in all three) remain strict subsets of their
references. The
[`v2 cross-division census preregistration`](docs/plan/qf-linear-a5-cross-division-census-v2-preregistration-2026-08-09.md)
froze the three populations as monotonicity controls; the 2026-08-21 diagnosis
below is that census's answer.

**Completed checkpoint.** [Gap #1's diagnosis](docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
(`docs/plan/status/agent-lra-diagnosis.md`, gap analysis §9 row 1) refuted the
"one shared cause" hypothesis: 278 misses across the four pinned 200-file lists
split into **three** causes — `dl-online` running out of clock (QF_IDL 64/65
and QF_RDL 51/55 misses, the one genuinely shared pair), the LRA route's
1,024-atom refusal plus its slow CDCL(T) search (QF_LRA + QF_RDL's tail), and
the lazy UF/arith CEGAR (QF_UFLIA, 82/82 — closed separately, see A4) — plus 26
QF_UFLIA files rejected at the parser (A4's wide-integer control). Three
candidate fixes were then built and measured (gap analysis §9.0.1); **all
three are refuted**: dropping the LRA atom cap's terminality gave 0 new
decides and 54 of 71 turned into memory aborts past 12GiB — the cap is
load-bearing protection, not a tuning knob; 5x the wall clock converted only 1
of 10 QF_IDL timeout files (QF_NIA's same experiment: 3 of 35, 0 of 20
`Timeout` files); reallocating the `dl_probe_budget` reserve (`min(t/4, 6s)`)
caps the achievable gain at 1.33x against the 5x experiment's 10% conversion
rate, and the reserve is independently load-bearing (`QF_IDL/sal/lpsat/lpsat-
goal-18` needs it). Treat the repaired high-memory LRA normalization case and
the rejected global 12/12 DL split as permanent controls before adding new DL
syntax.

**Next slice.** None is production-authorized; the cheap axis is closed. What
remains is algorithmic, not tuning: a faster difference-logic search for
`dl-online`, and an LRA route that does not have to choose between a size
refusal and a timeout — i.e. the theory-interface work the
[2026-09-05 performance review](docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
§3.2 D2 names as the structural cause (`TheorySolver` has no final-check hook,
so `lra_online.rs` re-decides feasibility on the warm simplex on every
`assert`) and recommendation 4 authorizes as the direction: widen the theory
trait (final check, lazy explain, a driver-owned propagation queue, dynamic
atom registration) and unify `CdclT` onto the `proof_sat` clause arena or make
the native core its search engine. That widening is Track 1's P1.5 keystone
under a new name. Do not revive the LRA atom-cap drop, a flat wall-clock
increase, or the `dl_probe_budget` reallocation without new evidence.

**Exit.** A/B measurement is monotone across all three divisions, exact
Farkas/DL evidence checks pass, deep input returns without recursion abort, and
the retained arithmetic fuzz suites execute nonzero cases.

### A6 — Close proof-production errors and evidence gaps (`TODO`, P1)

**Why now.** Definitive answers without checkable evidence violate the product's
core direction even when verdicts are sound. QF_BV evidence mode
(`bench-results/PARITY.md`, 2026-08-17T20:21:52Z) decides 130 UNSAT rows: 93
certified (71.5%), 79 re-checked from serialized text alone (60.8%), 0
certificates failed to re-check, and 37 remain bare UNSAT because the
evidence-producing route could not decide them within the 60s evidence budget.

**Completed checkpoint.** [ADR-0613](docs/research/09-decisions/adr-0613-unsat-is-certified-by-following-hints-not-by-searching-for-them.md)
(`docs/plan/status/187-drat-evidence-route.md`, 2026-08-28) routed the
certificate path off the quadratic forward DRAT checker: the fast backward
engine (`elaborate_drat_to_lrat_backward`) now runs as an **untrusted** hint
producer and the small, search-free, linear `check_lrat` verifies those hints
directly — a `Certified` is discharged by `check_lrat` alone, so the trusted
base shrinks rather than grows, and checking throughput rose ~106x on the
measured case (fp16: 82.302s checking 827,048 steps at 10,048.8 steps/s,
versus never observed to finish on the prior forward checker). Gap #6
(checkers that re-run their producer) converted three more families off
producer-equality checking — `nra-even-power` (10 certified `unsat`),
`finite-array-extensionality` (4), and `finite-domain-pigeonhole` (3) —
joining `array-axiom` (85); 102 of 281 certified `unsat` (36.3%) are now
decided independently (`docs/plan/status/120-checker-independence.md`). Of the
28 remaining re-run checkers: 3 families / 16 instances are a complete
decision procedure re-run and were never the defect; ~19 are convertible; 6
families / 15 instances need a certificate change, not a checker change
(gap analysis §6.2). Gap #5 (portable evidence) found the rule vocabulary was
never the binding constraint: Carcara 1.1.0 (built at `references/carcara`,
`6624ea80`) does have array rules and the emitter now validates against it,
but the figure stays **44 of 281 certified `unsat` (15.7%) carry an artifact
an external checker can read** (`docs/plan/status/121-portable-evidence.md`;
gap analysis §6.2) — 84% still re-validates only inside axeyum's own Rust.
Separately, of 269 baseline `unsat` satisfying the full conjunction (certified
+ independently checked + trust-hole-free + Lean-reconstructed), only **142
(52.8%) carry theory reasoning — a term built from the query**; the other 127
(47.2%) are structural attestation only (a 21-line `axiom P; axiom Not P;
theorem _ : False := …` shim, `sorry`-free but containing none of the
reasoning). Seven logics — QF_NIA, QF_FP, QF_UFLIA, QF_FF, QF_UFFF, QF_DT,
QF_BVFP — are at **0% reasoning**: every Lean module for them is the shim
(gap analysis §6.2). 142, not 269, is the number to quote for "propositions
Lean proved about the query."

**Next slice.** Fix the two QF_NIA `IntPow2` production errors first. Then use
route provenance—not query syntax alone—to split the 37 QF_BV bare UNSAT rows
and the broader arithmetic/string-sequence proof gaps. Close the cheapest (C)
gap-#6 instance, `bv-abstraction` (4 instances): it already builds, proves and
self-checks a QF_BV refutation and discards it, keeping only
`abstracted_terms: Vec<TermId>` — carrying that proof moves 4 instances from
axeyum-internal-only into the external DRAT column.

**Exit.** Zero production errors; every newly credited certificate passes its
own independent checker; text-only recheck, arena-backed check, Lean
reconstruction, and bare-result counts remain separate fields.

**Stop.** Never relabel arena-backed checking as serialized proof replay or
generate proof credit through query-only re-derivation. Never quote 269 as
"Lean proved the query" without the reasoning/attestation split.

### A7 — Finish route observability before searched policy (`TODO`, P1)

**Why now.** `RouteTrace::to_json` landed, but the bench path and quantifier
preamble are incomplete. The proposed exploration tracker also incorrectly
placed T3.5 before its own G1 phase-3 gate. The
[2026-09-05 performance review](docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
§2.2 item 3 measured the specific gap directly: `route_trace.rs` has no
elapsed or duration field, so **a declined route's cost is invisible** — part
of what the 2026-08-21 linear-arithmetic diagnosis paid for by hand-classifying
800 files from per-file TSVs because no instrument said where the time went
(`auto.rs`'s 52 hand-ordered routes each discard a declined route's encoding;
§3.2 D3).

**Required order.** Accept or revise the blocking ADRs; complete T0.2 route
registry; complete T0.6 recorder sites and `solve_explained`; finish T0.1 bench
persistence; add T2.5 public-corpus coverage; run T2.3/G1; only then consider
T3.5 policy-v0 equivalence. Fold the performance review's recommendation 7
(elapsed time per route in `RouteTrace`, stage attribution for the arithmetic/
EUF/string routes analogous to the BV path's `BvLayerStats`) into T0.6's
recorder-site work rather than as a separate later slice — it is the same
instrumentation point.

**Exit.** Every registered route has a stable ID, the representative corpus
covers the catalogue or records explicit gaps, legacy dispatch replays exactly,
`RouteTrace` carries elapsed time per route, and G1 — not enthusiasm — decides
whether searched policy proceeds.

**Stop.** The exploration track remains proposed and may not preempt A2–A6.
See [`docs/plan/exploration-track/`](docs/plan/exploration-track/README.md).

### A8 — Implement SMT-LIB ordered command/event capture (`TODO`, P2)

**Why now.** The checked conformance matrix had six absent command families,
seven accepted no-ops, and zero interactive textual-session rows.

**Completed checkpoint.** [ADR-0541](docs/research/09-decisions/adr-0541-the-smt-lib-front-door-answers-commands-or-says-unsupported.md)
(accepted, 2026-08-21) closed the "command accepted, never answered" half of
this gap: `solve_smtlib_session` walks a `ScriptCommand` stream and answers
multi-query `check-sat`, `get-model`, `get-value`, `get-unsat-core`, and
`get-proof` per command rather than deciding a whole script at once, and
`set-option` now honors a closed set of five options
(`:produce-models`, `:produce-unsat-cores`, `:produce-proofs`,
`:print-success`, `:timeout`) and returns `unsupported` for everything else per
SMT-LIB §4.1.7. `set-logic` is recognized (a name shaped like an SMT-LIB logic
is accepted, else `unsupported`) but deliberately **not enforced** — logic
conformance needs a complete logic-to-theory table and a table with a hole
turns a correct file into a false refusal; measured cost of not enforcing it is
1 corpus file. `solve_smtlib_incremental` reuses the same walk with output
commands switched off, so it cannot report a different verdict from the
session path. 29 tests in `smtlib_session.rs`, each guard deletion killing
exactly one test.

**Next slice.** ADR-0342 remains `proposed` and is not superseded: it scopes
declarations/definitions by `push`/`pop`, `reset-assertions` removing
non-global declarations, and atomic continued-error semantics, none of which
ADR-0541 touched (ADR-0541 itself declines full `(reset)`, requiring a fresh
declaration/option environment boundary that does not exist yet). Per the
generated conformance matrix
([`docs/plan/generated/smtlib-api-conformance.md`](docs/plan/generated/smtlib-api-conformance.md)),
still absent: `define-fun-rec`/`define-funs-rec` (keywords recognized by the
command scanner, no `parse_command` arm); full `(reset)` (explicitly rejected,
not silently ignored); `declare-sort` with arity ≥ 1 and
`declare-sort-parameter` (arity-zero uninterpreted sorts are first-class,
parametric sort constructors are not); parametric datatypes (0 of 2,200 pinned
competition files use them — gap analysis §9 row 9, deprioritised, not
authorized for this slice). Accept or revise ADR-0342 against what ADR-0541
already delivered before implementing the remaining session-state boundary
(scoped declarations, reset epochs, atomic continued errors).

**Exit.** The registered 14 invariants and 20 fixtures/107 commands pass through
the product path; malformed commands cannot partially mutate session state.

**Stop.** Do not add isolated output helpers and call them textual conformance.
Do not build parametric datatypes or `define-fun-rec` from A8 — they are
capability zeros in the scored population (gap analysis §9 row 9), not part of
this session-semantics slice.

### A9 — Extend the Lean replay census and close the remaining Next Ten items (`TODO`, P2)

**Why now.** "The local host currently has neither `lean` nor `elan`" is
false and was corrected 2026-09-05: both Lean 4.30.0 (the Mathlib corpus pin)
and 4.34.0-rc1 (the cross-check pin, ADR-1594/ADR-1660) are installed under
`~/.elan/toolchains/` on the fleet; `command -v lean` is empty only because
`elan` does not touch `PATH` — resolve with
`scripts/check-lean-gate.sh --print-toolchain`. What "Lean compatible" means
here is now written once
([`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md),
[ADR-1668](docs/research/09-decisions/adr-1668-the-lean-claim-surface-says-one-thing.md)):
K0 1/1, K1 6/6, K2-K6 0; the replay census, the two pins, the import tier,
and the Lean-side tactic are all measured, not aspirational.

**Next slice.** `14-lean-lang.md`'s Next Ten still has four open items, in
priority order: **2** (replay every proved theorem in pinned Lean or name the
reason — extend the `creal`-only census, `missing=0` enforced, `Type`-valued
theorems as a typed class); **3** (publish the constructive analysis as a
Lean library — render the `creal` prelude as `.lean` source Lean elaborates,
packaged for Lake); **7** (the public conformance corpus and a divergence
ledger against Lean 4's own kernel test cases); **9** (a native reader for
the kernel-core statement rendering, render→parse→same-term gated). Item 2 is
the precondition for the chair's headline number meaning anything to a Lean
user and should go first.

**Exit.** Each item closes with its own ADR and the evidence `14-lean-lang.md`
already asks for (a run, not a projection); the progress-log row and the
matrix regenerate (`gen-lean-compatibility.py --check`,
`gen-lean-complete-parity.py --check`).

**Stop.** Do not widen into K4-K6 (workflow, runtime, ecosystem) — the C5 gate
says those wait until the C2/C3 adapter has real use; no chair asked for them.
Do not claim an item done from a projection or a plan; each needs a run.

### A10 — Build the SMT-LIB product surface after S1 (`TODO`, P2)

**Why now.** Production replacement requires more than solver depth. Once A8
freezes session semantics, add canonical response rendering and the missing
command families in dependency order.

**Next slice.** Use the generated conformance matrix to choose the first absent
family whose semantics and reset/scoping behavior are already representable.

**Exit.** End-to-end textual fixtures compare ordered outputs and state changes,
errors remain atomic, and API helpers and text mode share one semantic core.

### A11 — Make worktree and build-cache retirement routine (`WIP`, P2)

**Why now.** Accumulated per-worktree Cargo targets and the agent-target cache
filled the filesystem until a valid post-merge build failed at 585 MiB free.
The bounded cleanup recovered about 885 GiB without deleting dirty or unmerged
work, but the same failure will recur without a documented retention loop.

**Next slice.** Add a read-only inventory command or script that reports each
worktree's branch, dirty/merged state, target size, last activity, and safe
cleanup classification. Document an operator procedure that uses `cargo clean`
before worktree removal and requires explicit review for every dirty, unmerged,
detached, or cache-tag-missing path.

**Completed checkpoint.** The manual bounded cleanup and post-A3 retirement
proved the safety procedure for clean merged worktrees and reproducible Cargo
targets. The later authorized cleanup salvaged inactive dirty deltas, removed
the inactive checkouts, and retired the merged A3 targets. On 2026-08-12 all
refs were captured in a verified external Git bundle before old local/remote
branches and salvage stashes were removed. Only clean `main` is registered and
published. Automation and fixture coverage remain open.

**Exit.** The inventory is deterministic and tested against dirty, merged,
unmerged, detached, missing-target, and malformed-cache fixtures. A dry run
identifies disposable bytes without mutation; cleanup requires explicit exact
targets and preserves branches and live work.

**Stop.** Never recursively delete a worktree root, infer safety from age alone,
or remove dirty/unmerged state to meet a free-space target.

### A12 — Solver performance instruments (`TODO`, P1)

**Why now.** The
[2026-09-05 performance review](docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
measured that solver-crate activity dropped from 129 commits (2026-W34) to 2
(2026-W36) while every other part of the repository kept moving, that no
committed timing number fails a gate when it regresses, that no crate has a
`benches/` directory, and that the least engineered of three Boolean search
engines (`CdclT` in `cdclt.rs`, a bare `Vec<Vec<Lit>>` with no clause arena, no
blocking literals, no in-search simplification) sits under every division
below 70% in the parity ledger. Full source-and-measurement detail is in that
review; this block is the queue entry, not a restatement.

**Next slice — the review's recommendations, ordered by measured leverage, all
`TODO`, no lane currently open on any of them:**

1. **Turn PAR-2 into a ratchet.** Reuse `progress_frontier.rs`'s machine
   calibration and comparable/advisory verdict to fail a committed baseline
   whose `par2_mean_s` worsens beyond the calibrated noise band. Until this
   exists, every timing number in `bench-results/` is advisory.
2. **Measure gate (b) of the CDCL-priority decision** (see
   [benchmarking-and-performance-methodology.md](docs/research/08-planning/benchmarking-and-performance-methodology.md)):
   dump axeyum CNF from the p4dfa and Noetzli QF_BV families (measured SAT
   share 0.974 and ~0.95) and run BatSat, the native `proof_sat` core, CaDiCaL,
   and Kissat on identical DIMACS. About a day of work; decides whether the
   native core becomes the default and whether D1's third engine (`CdclT`)
   should be replaced rather than tuned. No CaDiCaL or Kissat run exists under
   `bench-results/` today.
3. **Micro-benchmarks for six hot paths**, bound to the same calibration
   scheme so they can gate: `CdclT::propagate`, `proof_sat` propagate,
   `tseitin_encode`, `AndUniqueTable` insert, simplex pivot, e-graph merge with
   explain.
4. **Widen the theory trait and unify the engines** — final check, lazy
   explain, a driver-owned propagation queue, dynamic atom registration; then
   move `CdclT` onto the `proof_sat` clause arena or make the native core the
   CDCL(T) driver's search. This is Track 1's P1.5 keystone and is the same
   structural cause A5 names for the QF_IDL/QF_RDL/QF_LRA deficit.
5. **Bignum fallback for `Rational`.** One ADR, then `simplex.rs` and the
   parser. Unblocks the 26 QF_UFLIA files A4 names (`Value::Int(i128)`) and
   lets the LRA atom cap (A5) become a memory bound instead of partly an
   overflow guard.
6. **Swap the hasher** — a seeded fast hasher (`rustc-hash`/`ahash`) plus
   `indexmap` where iteration order is observable; measure on the term intern
   table (`arena.rs:43`, currently `std::collections::HashMap` with SipHash)
   first.
7. **Stage attribution for theory routes and elapsed time per route in
   `RouteTrace`.** Folded into A7's T0.6 recorder-site work (see A7); listed
   here too because it is a performance instrument, not only an observability
   one.
8. **Profiling recipes in the `justfile`** (`samply` or `perf record` plus
   `flamegraph`), pinned-core advice per
   [frontier-ratchet-reference-frame.md](docs/research/08-planning/frontier-ratchet-reference-frame.md).

**Exit.** Recommendation 1 fails a CI-visible gate on a real PAR-2 regression;
recommendation 2 has a committed CaDiCaL/Kissat-vs-BatSat-vs-native-core
artifact on identical CNF; recommendations 3, 6, and 8 have at least one
committed measurement each.

**Stop.** Do not build recommendation 4 (the theory-trait widening) before
recommendation 2 is measured — it decides whether `CdclT` should be replaced
rather than incrementally widened, and building the wider trait first risks
widening the wrong engine. Do not treat any number produced here as a parity
ledger entry; this is instrumentation, not a `PARITY.md` sweep.
