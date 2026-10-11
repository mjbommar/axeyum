# Axeyum plan, status, and next actions

> **Generated; do not edit by hand.** Sources: project-wide sections in
> [`docs/plan/global/`](docs/plan/global/README.md), one file per lane in
> [`docs/plan/status/`](docs/plan/status/README.md). Edit **your lane's file**
> and run `python3 scripts/gen-plan.py`; `--check` is a gate. This file was
> touched 67 times in 24 hours by concurrent lanes on 2026-08-13/14 and one
> lane's edit was swept into another's commit — that is what the split fixes.

**Canonical project tracker.** This is the repository's single mutable source
for current project status, ordered work, blockers, and resume guidance. Read it
first; a lane updates its own file under `docs/plan/status/`, never this one.

- Last consolidated: **2026-10-05**, against `main` at `a38d5f5da`
  (2026-09-17). All work has been paused since that commit; nothing is in
  flight, and every lane file was archived the same day.
- Status vocabulary: `TODO` · `WIP` · `BLOCKED` · `DONE` · `PAUSED`.
- History moved out of this file. The 770 lane files of the August–September
  campaigns are in [`docs/plan/archive/lanes/`](docs/plan/archive/README.md);
  the global sections this rewrite replaced (A1–A13, L0–L4) are preserved
  verbatim in `docs/plan/archive/global-2026-09-17/`; the index of every dated
  plan note and what superseded it is [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md).

`STATUS.md` is a compatibility pointer and there is no root `TODO.md`. Dated
notes under [`docs/plan/`](docs/plan/README.md),
[`docs/research/`](docs/research/README.md) and
[`bench-results/`](bench-results/README.md) are evidence and task detail; they
do not set order or current state. This file does.

## Status

Axeyum is a working research-grade reasoning stack: a pure-Rust default path,
replay-checked SAT models, several independently checked UNSAT evidence routes,
broad but uneven theory support, an independent Lean-core checker and importer,
a kernel-checked fact library, a CAS, and three external consumers. It is not
yet a drop-in Z3 replacement or a replacement for Lean.

Every number below names its source. "(not re-run)" means it was copied from
the cited file on 2026-10-05, not re-measured.

### Solver — the parity ledger

Latest entry per division by **solver commit** in
[`bench-results/PARITY.md`](bench-results/PARITY.md): all sixteen were taken on
2026-09-11, fifteen at `c1d6db6fe` against cvc5 1.3.4 (Bitwuzla 0.9.1 for QF_ABV, QF_BV and QF_FP), QF_UFLRA at
`14712b1f4` against z3 4.13.3. **0 disagreements in every division.** Axeyum /
reference on identical 200-file lists, 24 s:

| ≥ 95 % | 85–95 % | < 85 % |
|---|---|---|
| QF_UF 200/200 · QF_FP 199/200 · QF_SLIA 193/194 · QF_RDL 152/154 · UF 90/93 · QF_BV 186/194 | QF_ABV 186/197 · QF_S 186/197 · QF_IDL 113/123 · QF_UFLIA 161/180 · QF_LIA 119/139 | QF_LRA 107/145 · QF_UFLRA 142/198 · QF_NRA 117/186 · QF_DT 114/192 · QF_NIA 41/87 |

The ledger frame is old: `c1d6db6fe` is 976 commits behind `a38d5f5da`. Gains
measured after it are **not ledger entries** and are listed separately:

- **2026-09-17 board A/B** ([README](bench-results/board-ab-20260917-adr2142/README.md)):
  Axeyum alone, 16 × 200 files, `60e23fa39` decides **2,432 of 3,200** (+8 over
  its parent, 0 losses, 0 of 4,380 `:status` disagreements). Where that board
  differs most from the ledger: QF_NIA **87** (ledger 41), QF_DT **171** (114),
  QF_NRA 124 (117), QF_UFLIA 167 (161), QF_UFLRA 149 (142). No reference ran.
- **Shipped after that board** (ADR A/Bs, pinned lists;
  [coordinator record](docs/plan/archive/lanes/coordinator-three-repos-2026-09-16.md)):
  QF_LRA 107 → 113 ([ADR-2147](docs/research/09-decisions/adr-2147-a-violated-disequality-is-a-case-split-not-an-unknown.md)),
  QF_UFLRA 148 → 150, UFNIA 54 → 61
  ([ADR-2148](docs/research/09-decisions/adr-2148-nia-lemmas-versus-slice-versus-iteration.md)).
- The five weakest divisions each have a mechanism named at `file:line`
  ([stock-take, 2026-09-16](docs/plan/five-divisions-stock-take-2026-09-16.md)).

### Library, CAS, Lean

- **Facts** (counted 2026-10-05 over `artifacts/facts/*.json`): **2,971** —
  proved 2,692 · open 267 · computed 5 · refuted 4 · conjectured 3.
- **Trusted surface** (`docs/plan/lean-axiom-ledger-v1.json`, population as of
  2026-08-17, not re-run — `gen-lean-axiom-ledger.py --check` builds Rust):
  30 declared axioms, all in the `axreal` package; every other prelude 0.
  **Declared is not reached**
  ([ADR-0509](docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)):
  both are published, and the 30 are reached by no shipped route — the package
  is kept as the negative control those measurements are read against.
- **CAS** (`scripts/check-cas-trust-registry.py`, run 2026-10-05): 1,280 public
  functions — 151 certified, 110 checker, 1,019 uncertified; floor 151 held.
- **Lean replay** ([ADR-1661](docs/research/09-decisions/adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md),
  2026-09-10, not re-run): of 4,478 proved declarations pinned Lean accepts
  4,394; 50 are `Type`-valued theorems Lean refuses; 34 are blocked behind them.
  What "Lean compatible" means is fixed in
  [`14-lean-lang.md`](docs/math-department/14-lean-lang.md) (ADR-1668).

### Evidence

- **QF_BV certification** (`PARITY.md` evidence entry, 2026-08-17,
  `c799be2f7`, not re-run): 93/130 UNSAT certified (71.5 %), 79/130 re-checked
  from serialized text alone, 0 certificates failed. The other 37 are bare UNSAT.
- **SAT engine**: the native core is the only engine
  ([ADR-1908](docs/research/09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md));
  BatSat is removed and the referee is an external CaDiCaL/Kissat binary on
  our DIMACS text
  ([ADR-1910](docs/research/09-decisions/adr-1910-the-sat-referee-is-an-external-binary-reading-dimacs-text-and-batsat-is-removed.md)).

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|


Rows come from active lane files; with none active the table is empty. The
2026-09-17 results above are the last landings.

## Next Actions

**P0 preempts every track:** a wrong verdict, a crash, data loss, or a gate that
cannot fail (or is red) is reproduced, root-caused, regressed and repaired
first. Otherwise work runs in five tracks; within a track, take the first
unblocked item. Tracks may run in parallel, one lane per item.

User feedback researched on 2026-10-10 is recorded in the
[audit](docs/plan/user-feedback-audit-2026-10-10.md). CON-5 starts with fresh
reproduction of ignored objectives and unboundedness classification; confirmed
incorrect optimization claims invoke P0. Installed-extension probes are diagnostic,
not a fresh solver board or a new parity measurement.

**OMT correctness (`WIP`, omt-correctness, 2026-10-10).** CON-5 O0/O1 patch:
generic objective-bearing solve/model/session calls explicitly decline; text
optimizers share caller budgets and stop unresolved lexicographic prefixes;
integer unboundedness uses replayed affine rays, not numeric search ceilings.
Focused fresh tests: optimize 25, optimize_robustness 14, smtlib 102, all passed.
Ray equality-guard mutation: baseline 4 pass, mutant 3 pass/1 fail. Closed-affine
coefficient controls (including div/mod by zero): 2/2 pass.
Workspace gate failed an untouched CAS timing test (isolated rerun passed).
Initial front-door group failed a timed string fixture (isolated rerun passed);
serial rerun passed all 158 tests. Five linear differential suites passed (20 tests).
Fresh full-feature library gate: 2008 pass/1 fail (EUF pigeonhole timeout
control returned Unknown under the generous budget). Workspace gate is live. Frontier finished 11 pass/1 NRA timing failure (degree 40 retained).
Module-graph ratchet is red with the same parent findings.
Both guard mutations killed exactly one test; independent finite oracle matched
128/128 cases. Next: finish required gates, Python OMT result/model/optimality
API, preemptible ingest. BV/multiobjective probes now receive remaining budgets;
fresh optimize 25 and robustness 16 tests passed, including all four zero-budget
BV entry points. ADR-2300 is
proposed pending validation. Other feedback tracks remain open. Detail:
[consumer plan](docs/plan/proof-api-consumer-plan-2026-10-10.md).

Evidence and live validation handles: [lane notes](docs/plan/notes/omt-correctness.md).

**Signed integer literals (`WIP`, signed-literals, 2026-10-10).** Implements
optional ASCII minus with unbounded integer construction, declared-symbol
precedence, and preserved quoted numeric identity. Writer stays canonical;
signed decimals require unary subtraction. ADR-2400 records the decision.
Public parser package passed 380 tests including 5 new regressions;
Fresh isolated Python extension passed all 12 selected tests with SAT replay.
Fresh solver front door passed 1/1 and fresh CLI passed 6/6.
Required
required front-door/workspace gates remain pending. `abs`/`distinct` parse and
receive semantic controls. Exact `notes/80` location remains unknown.

**CAS exact inputs (`WIP`, cas-exact, 2026-10-10).** Rust Rational already carries
promoted coefficients, but the big zero-test fallback narrowed them with getters
that panic. Fix uses exact big numerator/denominator conversion. Three fresh
integration controls passed: equality/replay/tamper, big refutation, and the
360-period payment against an independent Python Fraction (2859/2849 bits).
Wide Python transport/evaluation implemented with explicit 16,384-bit limits;
fresh Python: 213 pass. Constant folds/rendering repaired; four Rust controls,
focused clippy, generated stubs and arithmetic-boundary gate pass (ADR-2900). Private-snapshot guard mutation killed exactly one test. Earlier Rust-only CAS gate passed 2,140 (11 ignored). Latest full CAS: red,
2,139 pass/one untouched finite-group timing failure (6.095s > 5s); new full CAS/workspace gates run against e7b58fc86 (runner 59537; logs in notes). Next: audit other promoted-value
boundaries, implement exact expression/Python arithmetic and amortization,
negative powers, pi and bounded text parsing. No LIB-6 completion is claimed.

**CAS step traces (`WIP`, cas-traces, 2026-10-10).** First opt-in polynomial
producer/checker carries full input/result and before/after trees, ordered IDs,
locations, stable rules/arguments, premises/context/side conditions and local
normal-form witnesses. Eight fresh integration tests passed; examples compiled
but their zero-test harnesses are only build evidence. Separate-process replay
accepted 1 genuine claim and rejected all 5 corruptions; focused clippy passed.
Context-guard mutation: baseline 5 pass; mutant 4 pass/1 fail. Fresh Python bindings passed 6 tests and the rational four-step export demo.
Final-source rebuild passed: six Python tests, byte-identical Rust/Python
exports and two standalone replays. Generated stubs contain 649 items.
Malformed local witnesses now report their failing step; focused clippy passes.
Latest rebuilt extension passes seven Python tests including that diagnostic. ADR-2500 is proposed pending validation.
Next: complete gates and guarded division,
then kernel reconstruction. Wide trace coefficients also remain pending. No
kernel admission or LIB-5 completion is claimed. Evidence:
[trace lane](docs/plan/notes/cas-traces.md).

**Boolean Alethe (`WIP`, boolean-alethe, 2026-10-10).** Text proof API now
emits source-bound Boolean refutations for not/and/or/equality/xor/constants plus implication/Boolean ite,
reusing the existing proof tail. Literal source syntax survives IR folding;
quoted atoms serialize/reparse. Fresh checks: six solver proof tests, four CNF
controls, 645 CNF library tests and focused clippy pass. Pinned Carcara accepts
seven exports without holes and rejects two source/premise corruptions.
False-pin mutation: baseline 3 pass; mutant 2 pass/1 fail. ADR-2600 proposed.
Conditional rows: two checker tests pass; 13 exports pass pinned Carcara.
Nine SAT controls replay; conditional mutation kills exactly one test.
Negative-real multiplication now checks, including a nested-negation bridge;
five arithmetic exports are accepted by Carcara, but a changed-coefficient
source also passes: the unpatched checker fails source binding. An isolated pinned guard-patched
checker now passes all 18 exports and rejects that changed source. Both new
arithmetic mutations kill exactly one test. Fresh public Python: five tests pass;
five full,z3 arithmetic differential suites: 20 tests pass. Updated CNF library: 645 pass. Full solver: 2007 pass; five front-door suites: 158 pass. Workspace remains live.
Next: scoped/macro source reconstruction, elaboration/checking
budget propagation, broader Python coverage, kernel reconstruction and full
workspace gates. Boolean+LIA composition is in progress (ADR-2800): five new tests pass, source quoting and serialized replay repaired;
portable integer elaboration remains. All 16 targeted Rust proof tests, focused clippy and seven fresh Python tests pass.
Gates pin 446aae38b (logs in notes); workspace PID 3297276 remains live.
The negative-real repair still needs remaining source/coercion controls. No full EVD-6 completion or integration claimed.
Details: [notes](docs/plan/notes/boolean-alethe.md).

**Signed CAS powers (`WIP`, cas-negative-powers, 2026-10-10).** Based on
97359c332's bounded wide Python surface. ADR-3000 proposes signed Rust/Python
powers lowering to partial Div/Pow nodes with explicit limits and zero/missing
behavior. Four Rust tests pass; revised fresh extension passes 223 Python tests,
including seeded Fraction comparisons and degenerate inputs. Focused clippy,
645-item stub generation and diff checks pass. Private domain-guard mutation:
four baseline passes, three mutant passes/exactly one failure. Parent CAS gate
has one timing failure; workspace jobs remain live. Bounded Python text parsing now passes 28 additional tests (251 combined);
ADR-3100 specifies exact grammar, spans and limits. π/serialization/Rust parsing
remain open. Promoted evalf panic repaired: two Rust regression tests and
focused clippy pass; rebuilt extension passes 256 combined Python tests. Next: distinguished π, domain-aware trace
certificates, kernel admission and integration gates. No completion claim.
[Evidence](docs/plan/notes/cas-negative-powers.md).

**Rules Date facade (`WIP`, rules-dates, 2026-10-11).** ADR-3200 proposes
Python Date/Duration terms over integer ordinals, years 1–9999, range obligations
and retained source sorts. Initial facade implemented; eight public Python tests pass, including Date
range, leap/century/year boundaries, source-query replay and type rejection.
Pack loader reads all seven metadata sets; typed benefit evaluator passes
fixture witnesses with SAT replay and missing/applicability statuses. Combined
Python: 13 tests pass; four benefit obligations return native UNSAT (no proof
check claim). Tax/procurement evaluators now replay all 210 generated bounded rows; combined
Python: 18 tests pass. All seven now have typed evaluators; enum/Real lowering passes 251 additional
generated rows. Combined Python: 24 tests pass. Enum guard mutation kills exactly
one targeted test. Real binding limit and explicit as_of are documented. Sourced Minnesota day-period template now computes under explicit applicability
and calendar assumptions: 31 combined tests pass, including 124 reference cases.
Native feasibility/minimality/uniqueness validate all 124 reference cases;
34 Python tests pass. Feasible models replay; UNSAT remains uncertified.
Verdict guard mutation kills exactly one test. Finite-window certificates now replay native ground facts in a separate process;
35 Python tests pass. Least-endpoint guard mutation kills exactly one test.
Certificates remain conditional; native UNSAT/kernel proof routes are open.
Added complete generated benefit coverage: all 576 rows evaluate with
source SAT replay and matching expected outputs (one targeted test passed).
Next: validator integration and complete CON-7
validation. No integration/completion claim.

**Feedback integration (`WIP`, feedback-integration, 2026-10-11).** Base
wide CAS/signed powers/parser/evalf da0e38a0a plus rules c3c747eb9, signed literals
343a289c8, OMT a536b76d0, proofs de0b570f3 and traces cd5287f84 now combine
without source conflicts. CAS history retains newer c0a083978 evidence. Generated
views, formatting and merge hygiene pass with documented skipped scopes.
Focused runner 63353 completed at source 2a111e062 (logs in notes):
native build succeeds; sealed Python now 384 pass/zero skipped with CLI, CAS integrations
18 pass, parser 101 pass, solver regressions 160 pass. Focused runner completed.
Required runner 88821: five front-door suites pass 158 tests; full solver is red
(2008 pass/one EUF timeout-expectation failure); workspace is now active. CLI route comparisons are same-engine checks.
Lint and independent oracle gates remain. Python SAT export/census and three
tests pass with pinned private empty-clause LRAT guard; unmodified checker accepts
a SAT control. All six representative term exports recheck, with replayed SAT controls.
Datatype source rendering fails parse; portable translation binding remains open.
Next: complete interactions/full gates, then
remaining trace width/domains/kernel bridges, pi/serialization, OMT Python gold,
SAT routes and consumer validation. Source branches retained; imports are linear.
No combined runtime pass, main landing or overall completion claimed.

**CAS pi (`WIP`, cas-pi, 2026-10-11).** Isolated from integration baf50f913.
Distinct Pi leaf and Rust/Python constructors now preserve constant identity;
ordinary Var(pi) no longer triggers constant evalf/enclosure/trig recognition.
Internal formulas and examples migrate to Pi; polynomial decoding preserves its
leaf and rejects forged source constant keys. Source-bound enclosure controls
cover both constant and bound-variable subjects. ADR-6000 remains proposed.
Core compile passes; five targeted Rust and 21 trig tests pass. Fresh native
build succeeds and sealed Python CAS suites pass 269 tests/zero skips, including
constructor, pi/Unicode parser and wrong-rewrite controls (hash/logs in notes).
Stub generation passes (27 modules/649 items), name/arity and type ratchets pass.
Same-interval constant/variable replay rejection strengthens the five Rust controls.
Private head-guard mutation passes: baseline five; mutant four plus one failure.
Parent runner21448: CAS 2140 pass/11 ignored; workspace is live. Child evidence
repair gates nonzero Pi polynomial claims and rejects raw atom aliases in both
producer and replay. Seven Rust controls pass. Fresh child native build passes; sealed Python suites pass 271/zero skips.
Both private replay-guard mutations kill exactly one of seven controls. Child
runner15629 on source286c6d445: CAS red (2139 pass/one Gaussian expectation
failure/11 ignored); workspace live. Expression-wire child fixes that unsafe
inequality expectation and focused Gaussian passes; broad child gates pending.
Canonical tagged serialization and reconstruction remain pending.
Version-1 traces and rational-only bridges explicitly decline unsupported Pi.
Next: finish stubs and full gates, source-binding guard mutation, portable Pi
encoding/replay and remaining consumer audits. No full Pi or goal completion claim.

**Expression wire (`WIP`, cas-expression-wire, 2026-10-11).** Child of
ff9e9301e, isolated from the Pi repair broad runner. ADR-6100 specifies tagged
version1 JSON preserving Pi/Var(pi), ordered syntax, wide exact rationals and
all unary heads. Rust and Python APIs implemented; four Rust transport tests
pass, with every head and malformed/resource controls. Fresh native build
passes; eight Python suites collect/pass279, zero skips. Stub generation and runtime name/arity/type ratchets pass. Private canonical
guard mutation passes (four baseline, three plus one mutant failure).
Read-only format and focused CAS-library Clippy pass. Broad runner64759 is
on c34b7bc89: format passes and CAS 2140 pass/zero fail/11 ignored; workspace
remains live. Pi certificate child retains this source while implementing replay. Parent CAS broad run is red: 2139 pass/one failure/11 ignored;
Gaussian test expects a false opaque-atom inequality between equal functions.
Require Unknown before radical simplification while preserving certified
integration and simplified equality controls. Parent workspace remains pending.
Focused Gaussian regression passes one test, retaining certified integration.
Next: full CAS/workspace gates and remaining consumer/certificate work;
checker controls and broad gates. Certificate transport and kernel admission
remain separate unfinished requirements; no full goal completion claim.

**Pi enclosure transport (`WIP`, cas-pi-certificate, 2026-10-11).** Isolated
child of 087fc31b5; parent broad runner64759 retains immutable source. ADR-6200
specifies version1 source-bound single-Pi Machin evidence, exact endpoints,
remainder/order, precision up to256 and resource caps. Rust/Python transport,
producer and counted replay implemented. Four Rust controls pass, including
precision256. Fresh native rebuild and nine Python suites pass283/zero skips,
including a separate-process certificate replay. Stub generation and runtime
name/arity/type gates pass. Source-binding mutation passes (four baseline;
three pass/one failure when the guard is removed). Format, focused CAS Clippy,
link and plan-authority checks pass. Broad runner43938 is live on56fe5378d:
full CAS suite terminal pass: 2,140 passed, 0 failed, 11 ignored, 373.02s
(`/var/tmp/axeyum-pi-certificate-full-gates-_dy3bzlq/cas_lib.log`).
Workspace libraries remain live; no workspace pass credited. Replay never
invokes production; parsing alone grants no acceptance.
Tamper tests require wrong-source, understated remainder and invalid endpoint/
precision declines; conservative relaxations retain the verifier semantics.
Next: workspace gates, general enclosure transport and checked Pi
value inequalities; retain byte/source checking through reconstruction. General enclosure transport,
checked Pi inequalities and kernel reconstruction remain separate open work.

**Python OMT reports (`WIP`, python-omt-results, 2026-10-11).** Isolated from
integration9221ebb67. ADR-6300 adds typed Rust/Python optimization reports with
exact Int/unsigned-BV values, direction/sort, explicit lex/box semantics, shared
budgets and original model/value replay. Separate models retained for boxed
objectives; lexicographic witnesses include earlier optimum pins. Scoped/popped,
reset and post-query objectives now select the same query snapshot as assertions;
legacy text optimizers share this correction. Compile check and initial native build pass. Seven focused Rust tests pass
again after retaining the full Script and declared-string lift metadata
(`/var/tmp/axeyum-python-omt-retained-script.log`: 7 passed, 0 failed/ignored).
Fresh extension at 933fbbe02: six selected Python suites report 93 passed,
34 skipped (CLI-dependent controls); all six OMT controls pass. Binary SHA-256
89d3ef632addb05f453fa4ee2814b51ed34f8bab81cfcc1547a9fd108cae8e85.
Full solver/workspace runner 55477 and stub runner 53264 are live, not passes;
private mutation baseline 75540 passed all seven Rust tests; two guard
mutations run under 45506 in the private snapshot. Added fresh Python lifting
control: declared String decodes, actual BV stays BV. Added independent
24-case finite-domain optimum oracle; OMT suite now 8 passed.
Gold eligibility stays false until source-bound no-better evidence is checked;
generic self-contained evidence checks cannot provide that binding by themselves.
Next: nonzero focused tests, fresh native/stubs, replay guard mutations, required
full gates, then source-bound optimality certificates and preemptible ingest.
Prior EUF failure does not reproduce in this run: its heavy timeout test
passes; full solver/workspace still live. No goal completion.

**OMT evidence (`WIP`, omt-source-bound-certificates, 2026-10-11).** ADR-6301
binds Farkas atoms, variable columns and assertion origins to original LRA
constraints. Integer strict-better refutations exclude the current optimum pin,
retain earlier lexicographic pins, and regenerate deterministic real relaxation
for replay. Gold eligibility checks feasible models and refutations for every
lex prefix objective; box results are independent. Integer-only cuts and BV
optimality evidence remain explicitly missing.

Verified: 2 source-binding controls; 10 gold Rust tests; fresh native rebuild
and 53 Python tests, zero skips. Five private guard mutations each cause exactly
one intended failure (three source bindings; model constraints and value).
Generated stubs: 27 modules/652 items; runtime gate1856 symbols; type gate
1717/1802 typed params. Format passes. All identities, logs, counts and storage
recovery details live in [notes](docs/plan/notes/omt-source-bound-certificates.md).

Required runner54092 remains live: five z3 arithmetic suites, five front doors,
full solver, workspace. All five z3 suites pass20 tests, zero failed/ignored;
front doors and remaining phases uncredited. Clippy runner32215 is live. Logs `/var/tmp/axeyum-omt-gold-required-_volk68z/`. Rust is frozen.
Next: complete required gates, portable source-bearing certificate transport and
independent process replay; Boolean/integer-cut/BV proof producers, bounded
ingest and replay, then kernel reconstruction. Overall goal remains active.

**Portable OMT evidence (`WIP`, omt-portable-evidence, 2026-10-11).** Isolated
child of 0a0a3b144. ADR-6302 specifies original-source, selected-objective and
lex-prefix certificates with named models/columns and source-bound Farkas replay.
Strict transport and counted byte checker rebuild subject/objectives, models,
lex prefixes and strict-better source bindings without optimization search.

Fixed internal relaxation-column lookup: certificates carry explicit namespace
tags; no user/helper lookup fallback. Enabled the bounded set-option whitelist
and added priority retargeting and namespace corruption controls. Seven focused
Rust tests passed, 0 failed/ignored, 0.03s in
`/var/tmp/axeyum-omt-portable-tests-v3.log`; compilation and the earlier five-test
run also passed. Fixed two CAS test format-string Clippy errors observed on the
parent; full lint rerun remains required.

Parent source-bound branch front-door gates completed: 2/48/13/82/13 tests,
158 total, all 0 failures/ignored, in
`/var/tmp/axeyum-omt-gold-required-_volk68z/`. Those are parent evidence, not
portable-child broad-gate credit. Parent full solver passed 2021 tests, 0
failed/ignored, 865.62s (`solver-full.log`); workspace remains uncredited.

Python now exports objective certificate JSON and provides counted replay against
caller-supplied source via `check_optimization_certificate`. Fresh native build
75801 passed; sealed package
`/var/tmp/axeyum-omt-portable-python-hy6yxe7f/package`, SHA256
`79eaea84038abb9cbfc2cc71f42c556f46e8d23be3fa295eca82fb07aa2ddc1e`.
Fifteen Python tests passed, 0 skipped, including separate-process replay without
optimization and invalid subject/value/prefix/envelope controls. Updated example
ran four model replays plus counted certificate checks. Logs:
`/var/tmp/axeyum-omt-portable-python-tests.log`. Stub generation56496 running.

Additional fresh-extension proof/Date/pack/statute suites passed 43 tests, 0
skipped, 4.26s (`/var/tmp/axeyum-omt-portable-consumer-tests.log`): 58 Python
tests total across both runs. Read-only formatting and generated-plan gates pass.
Private snapshot `snap-omt-portable-evidence-mutation-0b44e2703` baseline:
7 passed; removing source guard: exactly 1 intended failure, 6 passed, exit101.
Priority mutation1108 running; log `/var/tmp/axeyum-omt-portable-mutations.log`.
Full lint45243 pending/running, `/var/tmp/axeyum-omt-portable-clippy.log`.

Next: finish generated stub validation, priority mutation and broader gates.
Integer-only/BV/Boolean optimality producers, preemptible replay and kernel
reconstruction remain open; full feedback goal remains active.

**LIB-5 guarded traces (`WIP`, cas-guarded-traces, 2026-10-11).** Child of
71d640d68. ADR-6400 specifies caller-bound nonzero context and polynomial
witnesses; original version-1 traces remain unconditional. Implemented original
quotient/result/context transport, exact denominator premise, checked
cross-multiplication, syntactic cancellation producer and bounded byte replay.
Kernel admission is separate. Initial Rust and signature-rerun suites each
passed 3 tests, 0 failed/ignored. Context-extension control added; focused
job24408 passed 4 tests, 0 failed/ignored, `/var/tmp/axeyum-cas-guarded-tests-v3.log`.

Python exposes `cancel_trace`, `replay_guarded_trace`, guarded trace/result
classes and explicit production/checking/refusal outcomes. JSON replay returns
the checked object after one parse. Fresh integrated native9129 passed; sealed package
`/var/tmp/axeyum-cas-guarded-integrated-python-ubkp2p19/package`, SHA256
`22d70d4986bbf002270e88f708bf04ac1a216bdd5b9a385ad7451b636993988c`.
235 CAS/trace/OMT Python tests passed, 0 skips, 1.03s; initial 21 trace tests also
passed with separate-process and assumption/subject/result/witness controls.
Updated example checks x*x/x = x under x != 0, rejects a missing context.
`/var/tmp/axeyum-cas-guarded-integrated-tests.log`.

Stub generation24855 passed: 27 modules/658 items. Runtime signature gate:
1867 symbols/5 aliases/319 synthesized dunders. Type gate: 1816 parameters,
1731 typed, 131 allowlisted Any, 46 Any returns, 95.3%. Generated CAS/SMT stubs
included. Imported parent source repairs from 61d220a4d/5dfed320c: fallible
midpoint conversion, priority syntax, documented checker-length allowance and
linted docs/test names. Parent full lint: 925 targets/27 crates/0 diagnostics;
this is parent evidence, not this child's broad-gate credit.

Private controls72512 completed in snapshot `snap-cas-guarded-traces-controls-322a4cced`:
baseline 4 passed; each context/identity/zero guard removal produced 3 passed,
exactly 1 intended failure, exit101. Source restored byte-identical. Log
`/var/tmp/axeyum-cas-guarded-controls.log`. Trust registry passed: 1291 public
functions, 151 certified (floor held), 114 checker, 1026 uncertified.
Own lint96940 and broad runner42378 running. Logs:
`/var/tmp/axeyum-cas-guarded-clippy.log`,
`/var/tmp/axeyum-cas-guarded-required-322a4cced/`; no broad pass credited.

Next: complete own CAS/solver/workspace/lint gates and integration. Nested
cancellation, wide trace coefficients, cost measurements and kernel admission
remain required; the full feedback goal is active.

**LIB-5/LIB-6 (`WIP`, cas-wide-traces, 2026-10-11).** Base435de8c46.
ADR6500 defines opt-in v2 promoted arithmetic/codec,16384-bit intermediate cap,
width-weighted work, bounded shape/expansion/degree and constant powers512.
V1 stays narrow. V2 constant division carries checked nonzero conditions and
validates original domains even for empty traces. Sourcec6b0a5db1.

Rust suites passed8 v1+7 v2,0 failed/ignored after helper extraction:
`/var/tmp/axeyum-cas-wide-postlint-tests.log`. Private snapshot controls:
baseline7 passed; condition/domain/bit guard removal each causes6 passes and
one intended failure, exit101; restored bytewise. Logs
`/var/tmp/axeyum-cas-wide-control-{baseline,condition,domain,bits}.log`.
Full lint58742 passed926/926 targets,27 crates,0 diagnostics:
`/var/tmp/axeyum-cas-wide-clippy-v2.log`.
Serial full CAS29000 running, uncredited: `/var/tmp/axeyum-cas-wide-full-cas.log`.
Parent solver2028 passed; parent workspace remains pending.

Fresh native68539 passed; package
`/data0/axeyum/artifacts/python/cas-wide-trace-zyb2jcxy/package`, SHA256
`8d15fa2aa3664369c9031fbe191aeeb46032fe11720ea15072d74e45dde83f55`.
Python34 trace tests passed/0 skipped,9.07s; Fraction payment controls and
separate-process replay included. Example exact payment2859/2849 coefficient
bits; zero-rate2500/3. Stubs27 modules/658 items; runtime1867 symbols;
types1817 parameters/1732 typed,131 Any all allowlisted.

Cost runs completed with exact checks:payment6 steps/34998 bytes, revised
median production0.848s/replay0.367s. Small ordinary normalization0.011ms,
tracing0.152ms. [Diagnostics](docs/plan/notes/cas-wide-traces/cost.md) retain both runs
and extension identity; host-load sensitivity prevents parity claims.

Next: finish broad gates; wide guarded quotients, kernel reconstruction and
branch integration. Entire feedback goal remains active.

**LIB-5/LIB-6 (`WIP`, cas-wide-guarded-traces, 2026-10-11).** Child of4cd646409.
ADR6600 specifies guarded-quotient v2 with exact external nonzero-context binding
and matching polynomial-v2 identity witnesses. Existing v1 remains narrow.
Rust producer/checker now select v1/v2 transport and arithmetic consistently;
both identity witnesses must match envelope version. Zero-polynomial denominator
checks and exact external-context binding remain mandatory. Existing Rust suite passed4/0 failed/ignored; new wide suite passed4/0 failed/ignored:
`/var/tmp/axeyum-cas-wide-guarded-{rust,tests-v2}.log`. First wide compile
failed a nonexistent context field; corrected, not credited as a test run.
Wide suite crate-doc warning corrected.
Python `cancel_trace(..., wide=True)` added; replay/getters carry wide values.
Fresh native32955 passed,1m35s; sealed package
`/data0/axeyum/artifacts/python/cas-wide-guarded-k7j9mc0m/package`, SHA256
`2d37d850399ac8caf485f41ba64625995d5587531fcd39f64cc1d10f29e62fe7`.
Added10 Python runtime cases including separate-process replay with producer
disabled; syntax compilation passed. All4 trace suites7355 passed44/0 skipped,9.81s,
`/var/tmp/axeyum-cas-wide-guarded-python.log`; stub generator53068 passed27 modules/658 items.
Runtime stub check passed1867 symbols; type check1818 params/1733 typed,
131 Any all allowlisted. `wide: bool=False` generated in CAS stub.
Parent wide CAS2147 passed/0 failed/11 ignored,389.32s; this is parent evidence.
Private version mutation79117 completed:baseline4 pass; removed guard3 pass
and exactly `wide_identity_versions_are_bound_to_the_envelope` failed, exit101;
snapshot restored bytewise. `/var/tmp/axeyum-cas-wide-guarded-controls.log`.
Example passed:2912 bytes/3 steps/201-bit coefficient with exact replay,
`/var/tmp/axeyum-cas-wide-guarded-example.log`.
Own full lint12735 and serial CAS39650 running, uncredited; logs
`/var/tmp/axeyum-cas-wide-guarded-{clippy,full-cas}.log`.
Full solver23701 launched, uncredited:
`/var/tmp/axeyum-cas-wide-guarded-full-solver.log`.
Next: finish broad gates; nested conditional traces, kernel reconstruction
and integration. Entire feedback goal remains active.

**LIB-5 T3 (`WIP`, cas-trace-kernel, 2026-10-11).** Child ofb0e327536.
ADR6700 specifies syntax-preserving step translation and kernel proof composition
through existing Complex ring laws. Existing cas_bridge_tests proves whole
univariate integer identities, not serialized step traces. Next: implement
trace-driven before/after translation, compose proofs, admit generated identity,
measure axiom footprint, reject altered statement/assumptions, release validation.
Implemented syntax translator for bounded integer ring expressions and a generated
multistep trace test: byte replay, before/after kernel terms, transitivity,
admission, measured empty footprint, altered-endpoint rejection. Release job44600
passed1/0 failed/ignored,95.98s (compile4m55s): `/var/tmp/axeyum-cas-trace-kernel-test.log`.
[Route inventory](docs/plan/notes/cas-trace-kernel.md) records current producer/checker/
context/kernel boundaries and explicit translator declines.
Parent guarded full lint passed927 targets/27 crates/0 diagnostics; not a child
lint result. All broader feedback requirements remain active.

Trust registry checked:1296 public functions,151 certified floor held,114 checker,
1031 uncertified. Generated plan and diff whitespace checks passed. Release44600
completed:generated multistep theorem admitted, empty measured footprint and
changed-endpoint rejection all asserted. Fact-ledger/link validation33874 running, uncredited.

Compatibility launched after verifying installed toolchains:wasm84951 and
MSRV1.88 check53910, uncredited; `/var/tmp/axeyum-cas-trace-kernel-{wasm,msrv}.log`.

Parent guarded CAS39650 passed2147/0 failed/11 ignored,478.13s; release44600
passed as recorded above.
Source check:existing text parser lives in python/axeyum/_cas_parser.py; native
Rust parsing entry point remains a required LIB-6 extension.

Wasm84951 passed19.87s; MSRV1.88 check53910 passed1m39s, with existing solver
unused-code warnings (37/35 respectively), not warning-free claims. Added
fractional/wide/domain/foreign-variable translation declines and hostile added-
assumption intake controls. Release13258 running, uncredited:
`/var/tmp/axeyum-cas-trace-kernel-controls.log`.

**LIB/EVD/CON (`WIP`, feedback-consolidation, 2026-10-11).** Child97e700533.
Merging Pi/canonical expression wire/Machin certificates cb5d142b1 into wide,
guarded and kernel-trace ancestry. Resolve generated files by regeneration;
preserve v2 closed division and explicitly decline Pi in polynomial traces.
Consolidated as squash0c8a07884 (44 files); lane helper rejects MERGE_HEAD,
so own merge metadata was quit while preserving all resolved content.
Integrated Rust79219 and native79572 live, uncredited; logs
`/var/tmp/axeyum-feedback-consolidation-{cas,native}.log`. Hygiene37784 live.
Parent kernel bridge lint1809 passed; no integrated lint credit.
Initial inventory command omitted paths and failed usage; explicit recount log
`/var/tmp/axeyum-feedback-consolidation-inventory-v2.log`.
Next: hygiene/inventory verification,
focused Rust/Python compilation and replay, broad integration gates; Rust parser
and remaining proof/consumer requirements remain active. No push authorized.

**LIB-6 X2 (`WIP`, cas-rust-text-parser, 2026-10-11).** Child1ac2e66f7.
ADR6800 specifies native grammar matching current Python parser, exact decimals,
Pi distinction, signed powers, byte-span diagnostics and explicit intake caps.
Implemented native tokenizer/Pratt parser, exact BigInt decimal conversion,
Pi/unary/signed powers and byte errors. Final lowered AST also checks64 nodes/
depth32 because subtraction/negative powers add syntax nodes. Initial compiles
caught NthRoot(3) and fallible Rational conversion; corrected, no tests credited.
Compile4076 passed9.82s: `/var/tmp/axeyum-cas-rust-parser-check-v3.log`.
Next: broad gates and integration; shared native Python parsing migration.
Entire feedback goal remains active; parent consolidated build remains separate.

Added5 behavioral tests with constructor/precedence/wide/Pi/wire agreement,
unary heads, malformed UTF8 byte spans and paired resource controls. Test51221
passed5/0 failed/ignored: `/var/tmp/axeyum-cas-rust-parser-tests.log`.
Parent kernel release controls passed3/0 failed/ignored,72.62s.

Differential suite48239 passed6/0 failed/ignored:37 independent Python grammar
fixtures (24 accepted/13 rejected), canonical AST wire comparison. Fixture
generator records sealed native SHA. `/var/tmp/axeyum-cas-rust-parser-differential.log`.
Parser lint passed after one semicolon formatting fix: `/var/tmp/axeyum-cas-rust-parser-clippy.log`, v2 log passed7.90s.
Combined Python run originally failed collection(missing pinned SymPy); installed
SymPy1.14.0/mpmath1.3.0, rerun45817 passed1100/0 skipped,68.95s against sealed combined binary
SHA2560f638f71c1cd68b3e6cf35260f1f10e945938c3137a982ea2c2072fd9dd2cf76.
Rust parse_text example completed2 expression exports; example lint passed1.38s.
Cross-language payment roundtrip passed:9 replayed steps/40141 bytes, Fraction
agreement and4 malformed refusals, `/var/tmp/axeyum-cas-rust-parser-roundtrip.log`.
[User guide](docs/user-guide/cas-text.md) documents grammar, spans and limits.

Source87753b5d4 frozen for full CAS3957, workspace81069, complete lint32519;
`/var/tmp/axeyum-cas-rust-parser-{full-cas,workspace,full-clippy}.log`, uncredited.
Parent full solver2028 passed/0 failed/ignored,1123.99s. Fact validation33874
passed2971 facts/0 errors and dependency-derived checks; links passed.

**Aggregate gate repair (`WIP`, feedback-cas-lint, 2026-10-11).**
Child of native-parser source 5bd364e9b; parent source remains frozen for live
CAS3957/workspace81069. Complete lint32519 terminated101: gamma_and_polygamma_head
has102 lines, limit100. Split functional values into a separate behavioral test;
retain every existing assertion without suppressing the lint. Targeted CAS
lint46807 passed with warnings denied,16.67s. Gamma-filter tests35379
remain live; complete lint rerun launched against e170ddfcd, not yet credited.
Logs: /var/tmp/axeyum-feedback-cas-lint.log and
/var/tmp/axeyum-feedback-cas-lint-tests.log.
Next: collect nonzero results, run complete lint, integrate with parent after
its live tests terminate. Full feedback objective remains incomplete.

**CON-7 (`WIP`, rules-date-validation, 2026-10-11).** Child fddf0d2b2.
Gregorian/ASCII dates, bool-vs-Int, interval endpoints/order now validated in
repository validator and Python pack loading. Duplicate pack fields, non-object
JSON and Boolean schema versions reject. Focused Rules API52 passed; repository
controls17 passed. Native-dependent Python runs used local changed facade with
sealed combined package feedback-consolidation-zwt2z8bn, not a new native build.
Private date/type/order controls and intake duplicate/object/version controls
remove each guard and cause exactly1 failure with positive controls retained;
original files restored bytewise. Logs /var/tmp/axeyum-rules-{date-v2-*,runtime-control-*,intake-control-*}.log.

Statute validation includes manifests/required files/nonempty fixture population.
Default reports0 certificate replays; --statute-certificates checked1 conditional
fixture. Private85932e31a snapshot:6 manifest guards each kill exactly1 of7 tests;
real native replay rejects a changed claim. /var/tmp/axeyum-statute-guard-*.log.
No source authentication, holiday completeness or legal applicability follows.
Dashboard now derives statute editions/effective status/fixture counts/evidence
limits from manifests. Second generation byte-identical;17 controls and validator
pass. Existing query artifacts unchanged. README updated.

Full CAS3957 passed2147/0 failed/11 ignored,411.14s. Complete lint13564 passed
932/932 targets,27 crates,0 diagnostics,14576 fresh inputs (Rust47c91033e).
/var/tmp/axeyum-cas-rust-parser-full-cas.log and
/var/tmp/axeyum-rules-runtime-full-clippy.log. Workspace81069 remains live.
Next: source/calendar authority, applicability/effectivity evidence and general
proof routes, plus integration. Entire feedback goal remains incomplete.

**LIB-6 X2 (`WIP`, cas-python-native-parser, 2026-10-11).** Child a95216e37.
ADR6900 migrates Python parse to native grammar with character-span translation,
explicit surrogate errors and native byte/final-AST caps. Binding and wrapper
implemented; former Python implementation retained as private reference.
Check4896 passed (1m33s), /var/tmp/axeyum-cas-python-native-check.log.
Native build37851 passed3m04s; stub generation72621 passed3m29s:27 modules/661 items.
Sealed package /data0/axeyum/artifacts/python/cas-python-native-parser-fa_a312k/package,
SHA2567989e34f4deaf1c9982823d3d6e14b74b6fd179317f379cabbc859c2ba689f71.
Initial runtime run46 passed/2 failed: test regexes mismatched actual native
source-byte/shape messages. Corrected assertions; rerun48 passed/0 skipped,
/var/tmp/axeyum-cas-python-native-parser-tests-v2.log. Native/parser source unchanged. Added native
vs37 reference fixtures, UTF8 byte/character/surrogate controls and final AST
subtraction caps. Fixture generator now uses the independent private reference.
User guide documents tightened native bounds. Next: fresh sealed package/test
runs, stubs and required gates. Source binding frozen during compilation.
Python source length guard now rejects before UTF8 allocation; discriminating
control passed1 test against local wrapper/sealed prior native (no new binding
called). Focused native runtime suite passed; broad combined Python suite/stubs pending. Entire goal remains incomplete.

Runtime stub drift passed27 modules/1874 symbols/5 aliases/319 dunders;
type gate1823 params/1738 typed/131 Any all allowlisted/46 Any returns95.3%.
Generated cas stub carries native parser transport. Targeted lint launched.
Combined Python72341 passed1120/0 skipped,67.53s against sealed native;
/var/tmp/axeyum-cas-python-native-combined.log. OMT review confirms unbounded parsing remains
in optimize_smtlib/lex/typed paths, despite search deadline sharing; next lane.

**CON-5 O1 (`WIP`, omt-ingest-deadline, 2026-10-11).** Child f038d6147.
ADR7000: lexical/typed parsing and OMT objective/priority reads share original
start/deadline. Typed intake unknown has reason/no fabricated rows; Python getter
and guide updated. Parser96 tests passed; lexical4 passed; OMT integration3 then
4 with portable budget controls passed. Direct command controls3 passed.
Private lexical initial-poll mutation:4 ->3 pass/1 intended failure; restored.

Fresh native build2415 passed46.62s at ca62f7bf2. Sealed package
/data0/axeyum/artifacts/python/omt-ingest-deadline-1r9m56mg/package;
SHA25691e40f6df3ba95ae20f808c83939cfa0dec45412c82df7de0ebbdabc426bc2ae.
OMT Python18 passed/0 skipped,0.30s. Stub72102 passed27 modules/661 items;
drift27 modules/1874 symbols and type1824 params/1739 typed/131 allowed Any
passed against this binary. Broad CAS/OMT/Rules Python18641 passed1123/0
skipped,67.49s. Private mutation4465: baseline12 ->11 pass/1 intended
original_constraint_model_tampering failure after removing false-assertion guard;
restored bytewise in snapshot ca62f7bf2. Full solver59611 terminated143 without summary; no pass credited.
Serial rerun83566 running; full-solver-serial.log under /var/tmp/axeyum-omt-shared-deadline-.

Portable check_within shares parsing/command/model/Farkas deadline and reports
resource_limited. Python checker timeout_ms defaults2000. Front-door14307 passed:
corpus2, online48, word-first13, fixed-splice82, stoi13; all0 failed/ignored.

ADR7100 adds eval_within: None is resource exhaustion, Some is actual Value.
Same deadline propagates through iterative terms and finite quantified bindings;
existing eval/memo signatures unchanged. Primitive operators remain atomic.
IR library92005 passed104/0 failed. Evaluator integration passed3/0 failed;
portable model replay now uses eval_within for original assertions/objective;
OMT integration passed4/0 failed. Controls prove expired intake vs false and
preserve nested finite quantifier semantics, not mid-enumeration interruption.
Targeted Clippy75893 passed42.60s with warnings denied. Producer final replay
now shares its deadline; exhaustion clears model/value/no-better evidence and
returns ResourceLimit unknown. Generic checker preserves quantified certificates
(atomic checks between polls); ordinary assertions use eval_within. OMT controls
passed4. Private optimization group initially11 pass/1 stale zero-intake row
expectation failed; corrected to empty rows plus reason/no gold. Rerun89587
passed12/0 failed (2021 filtered). Clippy60534 passed23.39s with warnings denied;
Public checker uses fail-closed fallback.
Next: remaining broad gates, mid-quantifier budget controls, integration.
Logs /var/tmp/axeyum-omt-{ingest-*,checker-budget-tests,deadline-ir-tests}.log.
Entire feedback objective remains incomplete.

**LIB-6 X0 / P0 (`WIP`, wide-real-smtlib-writer, 2026-10-11).**
Child 3d5ff4029. Source audit found write_script uses narrowing Rational
numerator()/denominator() on public Real constants, which panic for promoted
values. Writer now uses exact big accessors, preserving canonical signs and
Real decimals/quotients. Four promoted cases pass in one regression. Initial
fixtures mistakenly used bounded arithmetic; corrected to wide_mul/wide_neg.
Private original-source snapshot reproduces the numerator panic (one failed
test, exit101); fixed source passes. All SMT-LIB tests385 passed, no failures/
ignores; warning-denied Clippy passed11.09s.
ADR7300: exact bounded (4096-digit) wide decimal intake; promoted unary negation,
quotient/floor/is_int folds; FP rounder explicitly declines promoted values.
Round-trip controls6 passed, including zero divisor preservation; SMT/FP broad
run passed486 tests (before added zero control),0 failed/ignored. Clippy SMT/FP
passed; solver Clippy passed38.49s. New front-door2 passed after finding/fixing
NRA sign-narrowing panic; existing NRA controls12 passed (2021 filtered).
Doc plan/ADR/link gates passed. Private snapshot69c3e0d7d controls completed:
syntax baseline6 and NRA baseline12 passed; removing decimal cap, FP
representation and NRA sign guards each caused exactly one intended failure.
All sources restored bytewise. Full solver serial gate74254 running on final
source; no pass credited yet. Datatype export child starts at3e4d96ad0: missing declarations, sort/name
placeholders and parenthesized nullary constructors repaired; dependencies
collected through recursive fields, arrays and UF signatures. Six reparsing
controls running2515; no pass credited. Next: collect tests and full gates.
No solver-wide completion or integration claim. Overall goal stays active.

### SOL — Solver parity

Close the measured gap to the named reference division by division, never
trading a verdict for speed. Every lever ships only under the ship criterion
(0 stable losses, 0 flips, ≥ 1 stable gain on pinned **and** held-out); a lever
that fails it stays OFF with its A/B in an ADR. Detail:
[families](docs/plan/families/README.md),
[stock-take 2026-09-16](docs/plan/five-divisions-stock-take-2026-09-16.md),
[CDCL consolidation plan](docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md).

1. **SOL-1 Re-measure the board on head.** The ledger frame `c1d6db6fe` is 976
   commits behind `a38d5f5da`; the A13 frame `db31113fa` is 425 behind; and the
   ledger is badly stale for QF_NIA (41 ledger vs 87 on the 09-17 board) and
   QF_DT (114 vs 171). Run all 16 lists through `scripts/parity-run.sh` at one
   commit, plus a same-day z3/cvc5 reference board on the identical lists.
   *Exit:* 16 ledger entries at one solver commit, 0 disagreements, and
   `scripts/check-parity-freshness.py` exits 0 (it exits 2 today — ENG-1).
2. **SOL-2 Finish CDCL(T) consolidation (phase B4).** ADR-1908 made the native
   core the one CDCL(T) driver, but `ufbv_online.rs:1468` and `:3498` still
   build `CdclT`; ADR-1913 scopes it as a swap gated on one probe. *Exit:* no shipping path
   constructs `CdclT`; board verdict-invariant against SOL-1.
3. **SOL-3 Linear arithmetic depth** (QF_LRA 107/145, QF_UFLRA 142/198,
   QF_IDL 113/123 on the ledger). In order: budget hand-back from a
   non-converging online search (the `ecoliMILP` shape) and the `sc-19…25`
   search cost; the 7 files stopped at a pivot-0 deadline poll
   (`simplex.rs:1441`); the 49 `cilled`/`minepump` QF_UFLRA files that land at
   ~25 s; `dl-online` as a portfolio arm and QF_IDL's 19 early declines.
   *Exit per lever:* ship criterion, plus the five LRA/DL/LIA z3 fuzzes green.
4. **SOL-4 Nonlinear and quantified** (QF_NIA, QF_NRA, UF/UFNIA/UFLIA).
   67 of 116 undecided QF_NIA rows timed out inside the linear relaxation
   (stock-take, before ADR-2148 shipped); S12's
   coefficient-width rung was never built; ADR-2149 (nested-binder activation)
   is registered OFF with no A/B run; ADR-2134 (+4 pinned QF_NRA, 0 held-out
   movers) stays OFF. *Exit:* one shipped lever per division under the ship
   criterion, or an ADR recording why the named mechanism is not the block.
5. **SOL-5 Dispatch cost and cause coverage.** `int-real-relax` decides 0 of
   198 rows while costing 754 s (ADR-2106); QF_RDL's last 2 files have no
   census; the families tree has no files for QF_DT, QF_S, QF_UFLRA and calls
   QF_FP "not entered". *Exit:* the rung is budgeted or removed by A/B; every
   ledger division has a family file with a cause or an explicit "no".

### LIB — Library and the flywheel

Make the flywheel automatic: the system should establish theorems nobody wrote
proofs for, through the one trust anchor (ADR-0601), as graded statement
families (ADR-0603). The metric is the trusted base and unassisted results, not
volume. The L0–L4 programme (ADR-0717) is done through S6, C3, G5 and D5;
what remains is below. Detail:
[throughput](docs/formalized-math-2026-08/05-throughput.md),
[CAS](docs/math-department/13-computer-algebra.md).

1. **LIB-1 Closed-loop batch discovery (D6).** *Exit:* a batch establishes a
   theorem whose checked proof consumes a theorem an earlier batch established,
   with no human-written target proof and an empty axiom footprint.
2. **LIB-2 Statement families, MOS-0.** None of the MOS files exist yet
   (`artifacts/statement-families/`, `scripts/check-statement-families.py`).
   *Exit:* every family row resolves to its declaration and receipt, and the
   targeted negative controls fail.
3. **LIB-3 CAS remainders.** Seven items of `13-computer-algebra.md` are `[~]`
   (1, 3–7, 9), e.g. moving four of five CAS arithmetic copies onto
   `axeyum-arith`, Galois groups, multivariate factorization. *Exit:* each item's
   own remainder, and the certified floor in `check-cas-trust-registry.py`
   rises above 151.
4. **LIB-4 Library artifact compatibility C4/C5.** C4's first demand-gated
   feature measured +0 population survival (ADR-1667). *Exit:* a C4 feature with
   nonzero survival, or C4 closed by ADR; C5 stays conditional on adapter use.

5. **LIB-5 Certified CAS step traces.** Reuse current whole-result certificates
   to implement the [trace plan](docs/plan/cas-certified-trace-plan-2026-10-10.md)
   T0–T3: source-bound deterministic steps, checked side conditions, Python
   replay, then kernel reconstruction. *Exit:* a multi-step trace rechecks from
   serialized bytes, targeted corruption fails, and one generated identity is
   admitted with an empty kernel-measured axiom footprint.
6. **LIB-6 Exact CAS expression surface.** Follow X0–X2 of the same plan:
   arbitrary-precision public rational transport, negative integer powers with
   domain obligations, symbolic π backed by existing enclosures, bounded text
   parsing. *Exit:* exact 360-period amortization and wide-value round trips;
   zero-denominator controls; canonical parse/print agreement; wider certificates
   remain replayable or explicitly decline at unsupported bridges.

### EVD — Evidence and Lean

Every unsat/valid carries a machine-checkable proof, and every claim names
which check it passed. Detail: [evidence family](docs/plan/families/evidence/README.md),
[Lean](docs/math-department/14-lean-lang.md),
[proof-gap matrix](docs/plan/generated/proof-gap-matrix.md).

1. **EVD-1 Re-measure QF_BV evidence on head** (last: 93/130 certified,
   2026-08-17) and split the bare-UNSAT rows by route provenance; re-check
   whether the two QF_NIA `IntPow2` proof-production errors recorded in August
   still reproduce. *Exit:* a fresh evidence-mode ledger entry; zero production
   errors; certified, text-rechecked, arena-checked and bare counts kept apart.
2. **EVD-2 Delete the SOS reconstruction fallback.** ADR-1673 relabelled it and left
   deletion open; `reconstruct_sos_certificate_wrapper_to_lean_module` is still
   in `axeyum-solver/src/reconstruct.rs`.
   *Exit:* the wrapper is gone and no reconstruction emits a statement-only shim.
3. **EVD-3 Lean residuals.** ℤ and an LRAT route for `by axeyum` (ADR-1666 is
   ℕ only); the 50 `Type`-valued theorems and 34 blocked declarations
   (ADR-1661); the unfinished 1,077-command audit (107 excluded). *Exit:*
   each closes with its own run and regenerated Lean matrices
   (`gen-lean-compatibility.py --check`, `gen-lean-complete-parity.py --check`).
4. **EVD-4 Propositional SAT entry.** RAT in the backward elaborator, the last
   piece after ADR-1722. *Exit:* RAT proofs elaborate to LRAT checked by
   `check_lrat`.

5. **EVD-5 Python SAT certificate routes.** DIMACS/DRAT/optional LRAT already
   export; inventory public routes and source-to-CNF binding using the
   [proof/API plan](docs/plan/proof-api-consumer-plan-2026-10-10.md).
   EVD-4 retains RAT elaboration ownership. *Exit:* a documented export example
   passes a pinned independent checker; missing LRAT remains explicit; altered
   source bindings and hints fail.
6. **EVD-6 Boolean/arithmetic Alethe gaps.** Freshly regress pure Boolean,
   Boolean+LIA and `(* (- 1.0) x)` examples, then implement the plan's A0–A3.
   *Exit:* mandatory source-bound proofs and SAT controls pass; Boolean resolution
   and supported arithmetic steps externally check without holes; integer-only
   local evidence is labelled separately until portable.

### CON — Consumers

Real users drive the product surface: the Python bindings, cindergraph (C
source graphs) and Glaurung (binary analysis) consume Axeyum; the SMT-LIB front
door serves everyone else. Foreign repositories are pushed only by the user.

1. **CON-1 Glaurung's default-backend decision.** Its ADR-0272 timing
   campaign was inconclusive; re-register it with a work-bounded budget.
   *Exit:* a registered campaign result that decides the default.
2. **CON-2 The defects pipeline over a real C library** (cindergraph → QF_BV
   → `axeyum_cli` → sanitizer replay; `python/examples/cindergraph_defects/`).
   *Exit:* findings on an unmodified upstream library, each replayed.
3. **CON-3 cindergraph's `for (;;)` empty-body policy.** Needs a Joern run.
   *Exit:* the policy pinned by a test against recorded Joern output.
4. **CON-4 SMT-LIB session semantics.** ADR-0342 is still `proposed`:
   scoped declarations under `push`/`pop`, reset epochs, atomic continued
   errors; then `define-fun-rec`, full `(reset)`, parametric `declare-sort`.
   *Exit:* accepted ADR; textual fixtures compare ordered outputs; a malformed
   command cannot partially mutate session state.

5. **CON-5 Trustworthy OMT front doors.** Implement O0–O2 of the
   [proof/API plan](docs/plan/proof-api-consumer-plan-2026-10-10.md): fresh ignored-
   objective regressions, explicit objective handling, shared budgets, honest
   unboundedness, then Python results with objective-mode and evidence fields.
   *Exit:* supported maximize/minimize produce the checked optimum or explicitly
   decline; overflow/resource limits never prove unboundedness; gold answers carry
   a replayed model and a checked no-better-solution refutation.
6. **CON-6 Signed-literal convenience and capability corrections.** Specify
   bare `-1` as compatibility syntax, preserve wide integers and canonical unary
   subtraction output. `abs` and `distinct` already parse. *Exit:* fresh public
   route/round-trip and negative controls pass; capability docs reflect tested
   sort/coercion coverage; correct `notes/80` when its exact path is identified.
7. **CON-7 Python Rules-as-Code with typed dates.** Implement R0–R1 of the same
   plan and the [rules roadmap](docs/rules-as-code/ROADMAP.md): Date facade over
   checked day ordinals, evidence-preserving Python pack API, then a bounded
   statute-backed computation-of-time template. *Exit:* temporal model lifting,
   invalid/leap-date controls and existing-pack reuse pass; the new pack pins
   official source/applicability and checks source-linked bounded obligations.

### ENG — Engineering hygiene

Gates that cannot fail, stale labels and abandoned state are how false claims
ship. Detail: [architecture review](docs/research/11-design-review/2026-08-27-architecture-review.md),
[gate divergence](docs/refactor-2026-08/gate-divergence-2026-08-14.md).

1. **ENG-1 Red gates.** On `a38d5f5da`, 25 `check.sh` steps fail when run
   alone, including `check-parity-freshness.py` (exit 2: the `PARITY.md:1972`
   "Budget curve" header), `shape-duplicates`, `proposition-duplication`,
   `merge-hygiene`, `carcara-gate` and `kernel-stack-envelope`; 79 more failed
   only in a parallel sweep and are unconfirmed. The consolidation fixed three
   (`plan-authority`, `example-inventory-count`, its controls). List and method:
   [gate sweep 2026-10-05](docs/plan/gate-sweep-2026-10-05.md); the `just`-only
   `check-parity-docs.py` adds 104 errors (92 of them undocumented examples). *Exit:* every step
   exits 0 alone on main (or is removed by an ADR), the unconfirmed 79 are
   classified, and each repaired guard has a control that kills exactly one test.
2. **ENG-2 Worktrees and branches.** `git worktree list` showed 201 entries on
   2026-10-05 before this consolidation (198 under `.claude/worktrees/`); 14 branches are unmerged into `main` (13 dated
   2026-08-22…31, one 2026-09-01). *Exit:* a read-only inventory classifies
   each (dirty/merged/unmerged/target size); unmerged work is merged or
   recorded abandoned; then exact-target removal.
3. **ENG-3 ADR status sweep.** 81 of 1,003 ADRs read `proposed` (counted 2026-10-05 from each file's first status line), including
   shipped decisions (ADR-2121, ADR-2126, ADR-2142). *Exit:* every decision on
   `main` reads `accepted`; every OFF lever reads `proposed` or `deferred` with
   its A/B.
4. **ENG-4 Split `creal.rs`.** It fuses name registry, field struct, build
   order and dispatch (441 fields at the review; 11,595 lines on 2026-10-05, after a partial split — topological order and the generated `STEPS` table landed, ADR-1512/1530). *Exit:* the review's split
   lands with prelude projection byte-identical and the kernel suites green.

## Families and divisions

The per-division source of truth for **state, cause, lever and exit criterion**
is [`docs/plan/families/`](docs/plan/families/README.md); measurements live in
the [ledger](bench-results/PARITY.md). This table is the index.

| Family | On the board | State, 2026-10-05 |
|---|---|---|
| [SMT, quantifier-free](docs/plan/families/smt-quantifier-free/README.md) | 15 divisions | QF_UF closed at 200/200; every other gap has a named cause except QF_RDL's last 2 (not re-censused since S1). The family tree has no files yet for QF_DT, QF_S and QF_UFLRA, and still lists QF_FP and QF_UFLRA as "not entered" although both have ledger rows (SOL-5). |
| [SMT, quantified](docs/plan/families/smt-quantified/README.md) | UF (90/93) | cause measured ([uf.md](docs/plan/families/smt-quantified/uf.md)); nested-binder activation measured and OFF (ADR-2149, proposed). UFNIA, UFLIA, AUFDTLIRA are scored on A13 lists, not the board. |
| [Certificate chain](docs/plan/families/evidence/README.md) | none, by construction | a division can reach parity with empty certificates and no board row shows it — hence EVD. |
| [Propositional SAT](docs/plan/families/sat/README.md) | not entered | CNF entry point and binary DRAT landed (ADR-1722); RAT in the backward elaborator is the piece left. |
| [SMT-COMP other tracks](docs/plan/families/smt-comp-tracks/README.md) | not entered | model validation is the cheap entry. |
| [Hardware model checking](docs/plan/families/model-checking/README.md) | not entered | best architectural fit (AIGER in, AIG certificate out); unscoped. |
| [Boolean optimization / counting](docs/plan/families/boolean-optimization/README.md) | not entered | no input formats. |

Two standing cautions. **Our reference is not the frontier** in several
divisions — OpenSMT, Yices2 and SMTInterpol lead some logics we score against
cvc5, so "parity" means parity with the named reference
([survey](docs/research/02-ecosystems/competition-landscape-2026-09/README.md)).
And **a division without an established cause gets a census, not a slice.**

## Workstream state

All tracks except ENG are `PAUSED` since `a38d5f5da` (2026-09-17) with nothing in flight;
the state column is what a resuming lane inherits.

| Track | State | Boundary |
|---|---|---|
| SOL — solver parity | `PAUSED`; A13 queue closed 2026-09-17 (ADR-2147 and ADR-2148 shipped, ADR-2134 and ADR-2149 OFF) | Every measured number is on an old frame; SOL-1 re-measure gates any new scoring. |
| LIB — library / flywheel | `PAUSED`; L0–L4 phases done through S6, C3, G5, D5 (2026-08-30/31) | The loop has closed by hand, never automatically (LIB-1); statement families not started (LIB-2). |
| EVD — evidence and Lean | `PAUSED`; Lean chair's Next Ten all ticked; BatSat removed (ADR-1910) | QF_BV evidence last measured 2026-08-17; SOS fallback still present. |
| CON — consumers | `PAUSED`; the 2026-09-16 improvement lists closed for Axeyum (16/16) | Glaurung's default-backend decision is open (CON-1); cindergraph and Glaurung are pushed by the user only. |
| ENG — hygiene | `TODO`; planning consolidated 2026-10-05 (lanes archived, size gate fixed) | 25 gates red when run alone on `a38d5f5da` (ENG-1); 198 agent worktrees and 14 unmerged branches (ENG-2). |

Public documentation is guarded rather than tracked: all 260 Cargo examples and
the consumer 48-case aggregate are checked by `scripts/check-parity-docs.py`
and `scripts/gen-example-inventory.py`.

## Resume protocol

1. Read this file first. Do not reconstruct priority from dated notes, archived
   lane files, branch names, or worktree age.
2. Verify live state (`git status --short --branch`, `git fetch origin`,
   `git rev-parse HEAD origin/main`, `git worktree list`). Re-derive any
   baseline you will score against; the boards quoted in Status are snapshots.
3. Pick the first unblocked item of the relevant track in **Next Actions**
   (P0 work preempts). Read its linked detail and the
   [foundational DAG](docs/research/08-planning/foundational-dag.md) before
   editing.
4. Open a lane file `docs/plan/status/<lane>.md` naming the item ID (e.g.
   `SOL-2`), with a `lane-status` block and landed rows
   ([format](docs/plan/status/README.md)). Work in an isolated worktree; one
   writer per branch.
5. Iterate on the narrowest relevant tests; run the aggregate gate once on the
   finished branch and confirm nonzero test counts. Commit with
   `scripts/lane-commit.sh`; merge and push per
   [multi-agent-operations](docs/contributor-guide/multi-agent-operations.md).
6. When the item meets its exit criterion (or is refuted), mark the lane `DONE`,
   **move the file to `docs/plan/archive/lanes/`**, update the item's line in
   the track here if its state changed, and run `python3 scripts/gen-plan.py`.
   Keep at most ~25 active lane files.

## Planning rules

- **One mutable tracker.** `PLAN.md`, generated from `docs/plan/global/` and
  active lane files. `STATUS.md` is a pointer; no root `TODO.md`; no other
  document may claim project-wide priority.
- **Dated notes are evidence, not queue.** A note under `docs/plan/` (stock-takes,
  gap logs, "what to build", improvement lists, roadmaps) records what was
  measured and proposed on its date. Anything still open from it is either an
  item here or not scheduled.
- **Labels.** Items are `SOL-n`, `LIB-n`, `EVD-n`, `CON-n`, `ENG-n`. Older
  labels (A1–A13, L0–L4, S1–S12, C/D/G phases, MOS-, W-, chair "Next Ten") are
  historical; resolve them through [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md) and the archive.
- **Lane lifecycle.** A lane file exists only while its item is active. On
  `DONE` it moves to `docs/plan/archive/lanes/`; at most ~25 are active.
- **Evidence outranks prose.** Benchmark TSV/JSON, generated matrices, test
  output, Git objects and remote refs decide status; correct prose that disagrees.
- **Wrong verdicts preempt everything (P0):** a wrong sat/unsat, a crash, data
  loss, or a gate that cannot fail is reproduced, root-caused, regressed and
  repaired before any breadth or performance item.
- **No false green.** A focused pass is not a full gate; a running job is not a
  pass; a local commit is not integration; a pinned-list gain alone ships nothing
  (the ship criterion is 0 stable losses, 0 flips, ≥ 1 stable gain on pinned
  and held-out).
- **No journal growth.** Global sections carry state, order and exits; detail
  goes in a dated note or artifact. `scripts/check-plan-authority.py` caps
  `global/` at 32,000 bytes and each lane file at 3,000.
- **Decisions require ADRs** for public operators, rewrites, encodings,
  backends, evidence artifacts, logic fragments, and priority-changing
  architecture.
- **Determinism and replay are promises:** stable order, explicit seeds and
  limits, original-term SAT replay, independent UNSAT checking.
- **Graph rank is advisory.** Degree, centrality and cost estimates never bypass
  fact-frontier legality, held-out isolation, or the theorem-credit contract.
- **Proof data does not leak into autonomous discovery:** proof/value edges may
  sequence work but are excluded from producer inputs and autonomous credit.

## Durable detail map

- **History:** [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md) (every dated plan note, its date, what
  superseded it); [`docs/plan/archive/`](docs/plan/archive/README.md) (lane files
  under `lanes/`, the replaced global sections under `global-2026-09-17/`).
- **Measurements:** [`PARITY.md`](bench-results/PARITY.md) (read the latest
  entry per division by solver commit), [`SCOREBOARD.md`](bench-results/SCOREBOARD.md),
  [families](docs/plan/families/README.md),
  [proof-gap matrix](docs/plan/generated/proof-gap-matrix.md),
  [capability matrix](docs/research/08-planning/capability-matrix.md).
- **Foundations:** [roadmap](docs/research/08-planning/roadmap.md),
  [foundational DAG](docs/research/08-planning/foundational-dag.md),
  [research questions](docs/research/08-planning/research-questions.md),
  [ADR index](docs/research/09-decisions/README.md),
  [2026-08-27 architecture review](docs/research/11-design-review/2026-08-27-architecture-review.md).
- **Mathematics and Lean:** [math department](docs/math-department/README.md)
  (chairs, [CAS](docs/math-department/13-computer-algebra.md),
  [Lean](docs/math-department/14-lean-lang.md)); fact ledger `artifacts/facts/`
  (`scripts/validate-facts.py`).
- **Strategy, frozen history:** `docs/refactor-2026-08/`,
  `docs/mathematics-2026-08/`, [`docs/formalized-math-2026-08/`](docs/formalized-math-2026-08/05-throughput.md)
  — read for reasoning, not for queue.
- **Working practice:** [contributor guide](docs/contributor-guide/README.md),
  [multi-agent operations](docs/contributor-guide/multi-agent-operations.md),
  public summary [`PROJECT-STATE.md`](docs/PROJECT-STATE.md).

## Consolidation record

### 2026-10-05

`PLAN.md` had grown to 75,717 lines and its global sections were three to seven
weeks stale. The 770 lane files moved to `docs/plan/archive/lanes/`; the replaced
sections are kept verbatim in `docs/plan/archive/global-2026-09-17/`; A1–A13
and L0–L4 became five tracks. Stale claims corrected, each checked against the
tree at `a38d5f5da`:

- The header said "last consolidated 2026-08-13" and cited A5-era SHAs.
- Status and Workstream quoted 2026-08-21 and 2026-09-05 parity numbers; every
  division has a 2026-09-11 ledger entry, and the 09-17 board is newer still.
- A13 read `PAUSED` with items 1–4 open; all four closed on 2026-09-17
  (`f7cd4195f`, `aa4ea0b6b`, `aab5d2db7`, `4d7c61ad5`). Its item 5 said the
  frame was 313 commits behind; it is now 425.
- A12 asked for a `CdclT` ADR and BatSat retirement; ADR-1908 and ADR-1910 are
  both accepted, and BatSat is out of `Cargo.lock`. Only phase B4 is left.
- L0–L4 read `TODO`; the phase lane files report S0–S6, C0–C3, G0–G5, D0–D5
  done on 2026-08-30/31. Only D6, C4 and C5 remain.
- A9 listed four open Lean items; `14-lean-lang.md` ticks all ten.
- Families said QF_RDL had "fourteen" unexplained files; the ledger gap is 2.
- The math chair's "Next Five" landed on 2026-09-06 and was never ticked.

### 2026-08-05

Removed two conflicting append-only root journals and one subsidiary live
tracker, made this file the only project-level authority, and corrected five
stale claims (CAS wave 24, an August-1 resume block, seven-vs-eleven divisions,
T3.5 ordering, PLAN-vs-STATUS authority). Detail is in Git history.
