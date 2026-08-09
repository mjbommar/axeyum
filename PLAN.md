# Axeyum plan, status, and next actions

**Canonical project tracker.** This is the repository's single mutable source
for current project status, ordered work, blockers, and resume guidance. Read it
first and update it before ending a project-level work session.

- Last consolidated: **2026-08-09**
- Integrated baseline merged into the active topic:
  `c516b5fac20f38886dfad41433656bad988f9f5c`
- Active repair candidate: declaration-scale QF_IDL repair
  `550b2c1f1e604f6f91b7310ef7584793d9c63b51`, merged with current main and
  pushed as `e996afd839c0dd076673cea861ea59dda329f344`
- Latest full-gate attempt: exact pushed merge `e996afd839c0dd076673cea861ea59dda329f344`
  passed `just check` with external frontier artifacts and exit 0
- Latest comprehensive green exact-commit gate:
  `e996afd839c0dd076673cea861ea59dda329f344` (`just check` exit 0)
- Latest integrated A3 code increments: bounded SMT-LIB `distinct` expansion at
  `63c82a6ef`, typed arithmetic-model reconstruction at `4ff9a82c6`, and
  deterministic string/integer coupling at `db7b426e8`
- Status vocabulary: `TODO` · `WIP` · `BLOCKED` · `DONE`

`STATUS.md` is now a compatibility pointer. There is intentionally no root
`TODO.md`. Detailed phase plans, ADRs, result notes, generated matrices, and
benchmark ledgers remain under [`docs/plan/`](docs/plan/README.md),
[`docs/research/`](docs/research/README.md), and
[`bench-results/`](bench-results/README.md). They provide evidence and task
detail; they do not override the order or current state in this file.

The pre-consolidation journals remain available immutably in Git at revision
`803c08439`: `PLAN.md` blob `fe75343c2f9dc8c845fe03246dfde7552690c77c`
and `STATUS.md` blob `0f169eddfabb190f45428090ffb057e8289bf355`.

## Status

**Live A5 checkpoint (2026-08-09).** Three fail-closed QF_LRA restarts exposed
wide-core memory growth, a valid mixed-numeric `ite` parser gap, and a large
first-solve Boolean skeleton. Their pushed repairs are `9d7a70a65`,
`11deff4ee`, and `d599b682f`. The next clean capture completed 200/200 rows in
1,012,663 ms with exit 0, zero stderr, and all former abort rows returning typed
budget `unknown`. The latest comprehensive gate remains the exact
`b07be65aa` frozen `just check` exit 0; it predates the two newest code repairs.

QF_IDL then failed closed after 58/200 rows on a 696,997-byte historically
unsolved BlockedNQueens case; QF_RDL was not started. The retained failure SHA is
`b723502e4982c082d3c5556e75d3172284ee99f789b74d86441d383a909bdc7f`.
Backtraces proved two native-recursion defects: 18,036 integer-collector frames,
then more than 15,000 DPLL abstractor frames with an unhonored deadline. The
focused candidate makes both Boolean-spine walks iterative and charges DPLL
construction to the remaining deadline. The trigger now returns typed budget
`unknown` in 21.23 seconds at about 83 MiB; `lpsat-goal-18` remains `unsat`.
Strict Clippy, all 1,084 solver-library tests, deep-input 16/16, LRA integration
20/20, and both LRA differentials are green with zero disagreement.
The pushed, not-yet-full-gated change requires a row-1 census restart. See the
[failure/repair record](docs/plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md).

The host gate later cleared. A row-1 restart at exact pushed `bbd079cfa`
reproduced QF_LRA atomically (200/200, 89 decisions, zero stderr), but QF_IDL
attempt 002 aborted after 63 rows on a 49.2 MB, 555,251-declaration scheduling
benchmark; QF_RDL was not started. Backtraces exposed quadratic declaration and
Boolean simplification plus residual recursive rewrite, collector, and Tseitin
walkers. The focused repair makes those paths dense/indexed or iterative. The
exact trigger now exits 0 with typed budget `unknown` in 37.88 seconds at 2.69
GiB peak RSS. Strict Clippy, all 1,090 solver-library tests, deep-input 16/16,
online arithmetic integrations, and both Z3 differential suites are green with
zero disagreement. Because behavior changed again, the complete census must
restart from QF_LRA row 1 after the candidate is committed, pushed, and fully
gated. See the updated
[failure/repair record](docs/plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md).

Axeyum is a working research-grade automated-reasoning stack with a pure-Rust
default path, replay-checked SAT models, multiple independently checked UNSAT
evidence routes, broad but uneven theory support, an independent Lean-core
checker/importer, and several consumers. It is not yet a drop-in Z3 replacement
or a replacement for the Lean system.

The 2026-08-09 README-only pass adds an application map and architecture/vision
guide; it changes no capability, evidence, measurement, or roadmap claim.

The exact pushed merge `e996afd83` then passed the complete externally isolated
`just check` gate with exit 0, including all workspace/solver tests, slow
differentials, frontier/CAS proofs, rustdoc, Glaurung, SMT-COMP resume, Lean,
parity, plan-authority, and link stages. The fresh A5 census retained valid
atomic QF_LRA and QF_IDL captures: each has
200/200 rows, zero stderr, exact pushed source/binary identity, and unchanged
24-second/8-GiB limits; IDL closes the former row-64 abort. QF_RDL attempt 001
failed closed after 196/200 emitted rows with exit 101, zero stderr, and no
credited output; metadata is retained at
[`QF_RDL-attempt-001.failure.json`](docs/plan/evidence/qf-linear-a5/failures/QF_RDL-attempt-001.failure.json).
The row and 21-row tail pass alone, identifying cumulative process pressure.
No derivation or score claim is authorized.

A3 is **WIP**. Pushed result checkpoint `3696e7dd5` is integrated on current
main by `47d8cd956`; its source branch remains preserved. The repaired complete
67-row census
classifies 52 NIA-linearization budget declines, 13 former generic model-replay
declines, one verifier rejection, and one bounded giant-`distinct` ingest
decline. The ingest repair replaces a 4.36 GiB expansion abort with a typed
resource limit. The 13-row diagnostic proved that absent reconstruction models
were fabricated after typed oracle declines; `4ff9a82c6` preserves empty,
model, declined, and inconsistent outcomes separately. A preregistered exact
probe-model reuse experiment recovered zero of seven SAT targets, kept six
UNSAT controls non-SAT, and was rejected without retaining its code or
authorizing a 200-row run. The residuals are now split between five large
DPLL/core-search targets and two integer-model reconstruction-deadline targets.
The two-case reconstruction cluster is now rejected: both valid diagnostic
observations entered reconstruction after the shared deadline, dense Gomory was
size-inadmissible, and B&B ran zero nodes; a follow-up root-repair discriminator
shifted among earlier load-sensitive stops and never produced stable mechanism
evidence. No cap, deadline, route-order, or solver-code change was retained.
The repeated-large-core diagnostic then confirmed size-only admission in 3/3
direct `SAT14/1051` observations and 2/3 `SAT14/1280` observations. A separately
preregistered, sound four-group deletion pass shrank the broad clauses but
reduced `1051` from 192--202 to 35 lazy rounds and `1280` from 391--397 to 338,
without deciding either target. It was rejected at the two-target gate; all
temporary solver code was removed and no 200-row run was authorized.
The remaining small-core pair then received the cheaper preregistered
relevance-activated bound ladder. It emitted 470--472 checked implications on
`p4943` and 484 on `p32598` without extra theory-oracle calls, but all six target
observations remained `unknown`; the target gate failed and all temporary code
was removed. This closes the five-row DPLL/core-search partition against both
measured explanation-quality mechanisms. The 52 budget rows are now exactly
repartitioned into 37 width-ladder timeouts, 11 all-reference-SAT pre-lowering
clause-estimate refusals, three reference-UNSAT combined-theory timeouts, and
one reference-UNSAT replay-detected model overflow. Fresh discrimination shows
the four-row UNSAT tail is not a valid target for the SAT-only width ladder.
The bounded estimate-attribution route also closed without production code.
V1 exceeded its analysis-work cap; deduplicated v2 stayed bounded but its
fresh-parse estimates differed from the exactly reproduced live route by 24/39
clauses. The complete-record gate failed, so no mechanism or 200-row run is
authorized and the 64,000,000 ceiling is unchanged. A3 yields to A4.
The first aggregate A3 gate exposed one load-sensitive string/integer fixture:
a hidden two-second default deadline could return `unknown` before the known
`i = 500` witness under aggregate CPU contention. Commit `db7b426e8` removes
that implicit clock, retains the caller's explicit timeout, and uses
deterministic 128-candidate / 2,000-node ceilings. The repaired rerun passed
format, stable all-target Clippy, every workspace unit/integration/differential
test and doctest, the 1,078-test solver library, the repaired 14/14 coupling
fixture in 15.58 s, 9/9 isolated frontier tests, both order-255 CAS moment
proofs in 1,014.84 s, warning-denied rustdoc, QF_BV/reflection/Glaurung gates,
foundational resources, rules-as-code, the 165-test resume aggregate, and all
Lean contract suites. It then exited 1 in the final parity-docs stage because
the generated complete-parity manifest still hashed `.github/workflows/ci.yml`
before the pinned-`just` workflow repair. Commit `704318a5f` refreshes that one
source-identity SHA-256 without changing any outcome or parity claim; complete
parity-docs, plan authority, and links are green. Because the aggregate command
itself did not exit 0, a final exact-head rerun was required. That rerun at
`3586c41d9` exited 0 with the tracked tree clean: stable format and all-target
Clippy; every workspace test and doctest; the 1,078-test solver library; the
repaired coupling fixture; 9/9 externally stored frontier tests in 212.94 s;
both order-255 CAS moment proofs in 940.10 s; warning-denied rustdoc; QF_BV,
reflection, and both 162-file Glaurung policies with zero disagreement;
foundational resources; rules-as-code; the 165-test resume aggregate in 47.125 s
with one expected live-host skip; every Lean/process-free contract; parity docs;
plan authority; and links. The five 20 KiB external frontier artifacts and their
pointer were removed after recording the result. Topic `ee5042dee` was then
pushed, merged as `0c31baf97`, and independently passed the combined-main gate
described above. Exact-SHA hosted docs run `31192792512` and CI run
`31192792245` at later merge `bd413357c` are separately terminal green.

A2 is **DONE** on current main. The old
`agent/smtcomp/full-preparation-live` head `3e53ca631` is 401 commits behind
current main and was rejected as a whole. Four still-valid process-free code
increments and their R1--R4 contracts were ported; stale root tracker changes
were excluded. R5 exact-source build provenance is now implemented at topic
commit `e4bb854bf`: the live CLI has no caller-selected Axeyum binary, the
operator builds once from exact clean integrated source in a unique private
locked/offline two-job target, and preparation schema v3 retains and replays
the source/tool/output/binary/run/completion chain. The port passes 52 focused
tests with 82 subtests, the 165-test resume aggregate with one expected
live-host skip, the generated-contract check, and the scoped gate. A real
fixture-boundary build smoke produced a 14,208,408-byte binary with the
registered environment and removed its private target. The exact pushed topic
`2925efea556cab59251e690c9e4e449468865d2c` passed a clean, uninterrupted
`AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR=<external> CARGO_BUILD_JOBS=2 just check`
with exit 0. All five frontier artifacts were written only to the external
directory, the worktree and tracked curves remained clean, and the local and
remote topic refs matched exactly. A prior direct
`CARGO_BUILD_JOBS=2 just check` passed every
code, solver, doctest, ignored moment-proof, rustdoc, profile, reflection,
benchmark, foundational-resource, rules-as-code, and SMT-COMP resume stage,
then exited 1 because its frontier stage used the historical tracked artifact
location and the later scoreboard check correctly rejected those volatile
curves. The exact committed curves were restored with no retained diff;
`just parity-docs plan-authority links` then passed cleanly. That earlier run
reproduces why the port's R3 external artifact isolation is required; the later
exact-topic gate closes the topic-only gap. Integration-owner review found the
20-commit topic strictly ahead of main with no divergence, and the synthetic
merge preview was conflict-free. Merge `8ed5ad089` integrated the reviewed
stack. Focused post-merge gates passed 52 readiness tests, the 165-test resume
aggregate, resume-contract generation, plan authority, links, and
`git diff --check`. That exact merge then passed one uninterrupted
external-frontier `CARGO_BUILD_JOBS=2 just check` with exit 0: workspace tests
and doctests, 9/9 frontier tests, both order-255 CAS moment proofs (939.24 s),
warning-denied rustdoc, both 162-file Glaurung policies, generated resources,
rules-as-code, SMT-COMP resume, Lean/process-free contract checks, parity docs,
plan authority, and links all passed. The five frontier artifacts were
external and the tracked tree remained clean. No host, NAS, sentinel,
allocation, live Lean, or solver action was performed. See the
[`A2 stale-branch audit`](docs/plan/smtcomp-a2-stale-branch-audit-2026-08-06.md)
and
[`R5 implementation result`](docs/plan/smtcomp-credited-full-preparation-f2-live-capture-r5-implementation-2026-08-06.md).

### A1 arithmetic resource closure

A1 is **DONE**. Resource increment `96ff85930` (merge `14f80a2bf`) resolves the
two measured arithmetic resource defects:

1. ADR-0377 makes arithmetic timeout query-global across sequential exact-real,
   NRA, real-relaxation, NIA-linearization, bounded-blast, and width-ladder
   routes. The same absolute deadline is polled inside solver-local CAD
   polynomial, projection, determinant, exact-division, and rational-cell loops.
   The public QF_NIA `ext-rew-aggr-test` now returns `Unknown(Timeout)` in 0.30 s
   for a 250 ms optimized request instead of 1.10 s; a committed debug regression
   finishes in 0.28 s and requires less than 1 s.
2. Online LRA normalization now has deterministic node, coefficient-work, and
   retained-cache ceilings. Production entry points distinguish deadline expiry
   from resource exhaustion and return `Unknown(Timeout)` or
   `Unknown(ResourceLimit)` rather than constructing a partial theory. The
   existing 1,024-atom front-door cap remains; current `sc-39.base.cvc.smt2`
   declines in 0.10 s at roughly 13 MiB instead of reproducing the historical
   8 GiB abort seen when that cap was experimentally raised.

Focused resource gates are green: deadline 6/6, online-LRA 7/7, CAD 37/37, the
normalization exhausted/near-miss unit, full all-feature solver Clippy, format,
and documentation links. The terminal aggregate solver gate
`CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --all-features --quiet --
--test-threads=2` passed 1,073 library tests and every integration/doctest bin,
including the 397.85-second UFLIA and 286.00-second word-equation differential
tests. `just parity-docs` is independently green at 35 rows, 24 logics, 992
files, 762 decided, 674 oracle-compared, and zero disagreements; its unrelated,
load-sensitive frontier refresh was discarded.

All six required retained lists were rerun fresh from row 1. Results are QF_NIA
34/200 versus 89, QF_LIA 117/200 versus 140, QF_LRA 86/200 versus 146, QF_RDL
105/200 versus 155, QF_IDL 68/200 versus 124, and QF_UFLIA 94/200 versus 180;
all have zero disagreements. The sole lower whole-sweep decision, one QF_LIA
`ex3000...` UNSAT, reproduced 3/3 in isolation at about 8.1 seconds under the
24-second protocol and is classified as load-sensitive sweep timing, not a
semantic loss. The ledger honestly retains 117.

The QF_IDL run exposed and then closed a real fallback-reservation regression.
Commit `4477f2bb9` bounds every probe-front-end phase and uses a measured 12/12
probe/fallback split only for 128–1,024-atom numeric equality gates; a global
12/12 split was rejected after losing five controls. A 171-case QF_IDL/QF_RDL
A/B was monotone. The final full sweep recovers `lpsat-goal-18.smt2` as UNSAT,
retains the BubbleSort gain, adds one SAT graph case, and has no Axeyum loss.

Commit `5ce07c55e` (merge `8ea6a7cad`) also makes parity resume identity
fail-closed: exact committed-list paths are canonical; ambiguous legacy
basenames, duplicate rows, and population drift are rejected. The six accepted
A1 runs were fresh and non-resumed. Full evidence, sidecar hashes, rejected IDL
policies, and gate separation are retained in
[`docs/plan/arithmetic-a1-retained-result-2026-08-06.md`](docs/plan/arithmetic-a1-retained-result-2026-08-06.md).

Disk cleanup first removed only reproducible Cargo artifacts and clean,
inactive worktree checkout directories; dirty worktrees and every branch were
preserved.
The 2026-08-07 follow-up removed 14 additional clean checkouts, retained their
13 unmerged branch tips, and reduced the registered worktree count from 39 to
25. After A3 was pushed, merged, and fully gated, its clean 127 GiB worktree was
retired and pruned; `cargo clean` then removed 70,833 files / 122.6 GiB from the
main worktree. A later user-authorized cleanup salvaged every dirty delta from
24 remaining inactive worktrees into path-labelled Git stashes, kept every
branch tip, removed those exact checkout directories, pruned the registrations,
and removed one inactive 1.7 GiB Axeyum session directory from `/tmp` after
verifying it had no open file descriptors. After the residual A3 evidence was
integrated, its clean topic worktree passed exact ancestry and cleanliness
checks; `cargo clean` removed 40,064 reproducible files / 71.0 GiB and the
checkout was retired while preserving the branch. The final merged A3
explanation-partition checkout was also retired with its branch preserved,
reclaiming about 176 GiB from its Cargo target. Only clean `main` remains
registered. Current free space is about 902 GiB on `/` and 28 GiB on the 62 GiB
`/tmp` tmpfs. Retained A3 census evidence and unrelated temporary projects were
left untouched.
Four empty A3 frontier directories and their pointer file were removed after
the failed aggregate attempts; they contained no retained evidence.

### Current evidence snapshot

- The committed regression scoreboard contains **35 baselines across 24 logic
  fragments**: **762/992** files decided, **674** oracle-compared, and **zero
  recorded disagreements**. This is bounded regression evidence, not universal
  soundness or representative SMT-LIB coverage. See
  [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md).
- The refreshed 4-second frontier artifacts report BV reduction **38**
  (baseline 30), LIA cuts **35** (baseline 26), NIA UNSAT **40** (baseline 40),
  NRA degree **40** (baseline 40), and string bound **40** (baseline 8). These
  are load-sensitive local frontier measurements; they do not raise baselines.
- The append-only head-to-head ledger currently covers **eleven divisions**.
  Its weak measured edges are QF_NIA **34/89 = 38.2%**, QF_UFLIA
  **94/180 = 52.2%**, QF_IDL **68/124 = 54.8%**, QF_LRA
  **86/146 = 58.9%**, and QF_RDL **105/155 = 67.7%**. Every credited entry has
  zero disagreements. Read the latest entry per division in
  [`bench-results/PARITY.md`](bench-results/PARITY.md); never copy an older
  entry merely because it has a higher score.
- QF_BV evidence mode decides 130 UNSAT rows: **92/130 certified**,
  **78/130 rechecked from serialized text alone**, and **92/92 certified rows
  independently checked against a fresh re-parse and term arena**. Neither
  check had a failure. The remaining 38 are bare UNSAT decisions because the
  evidence-producing route could not decide them within 60 seconds.
- The broader evidence audit still records **58 uncertified occurrences**,
  **eight independently checked results without Lean reconstruction**, and
  **two QF_NIA `IntPow2` proof-production errors**. Do not combine these
  denominators with the newer QF_BV-only experiment.
- The current official-source proof-family population has a retained local
  Lean 4.30 result of **70/70 accepted**. A corrected remote attestation and the
  exhaustive tier remain open. Lean language, ecosystem, and complete native
  compatibility remain far beyond the current K0/K1 slices.
- The previous 64,345-file full-library candidate is not a result: it produced
  zero admissible raw shards. Resumable/process-free readiness work exists, but
  a representative current-main run has not been admitted or published.

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|
| 2026-08-07 | `3576e6739` / `c92155454` / `d09e6debb` | Rejected relevance-activated bound ladders after 0/6 target decisions, exactly repartitioned all 52 A3 budget rows, refreshed the generated CI identity, and integrated the clean pushed evidence branch. |
| 2026-08-07 | `3696e7dd5` | Confirmed repeated size-admission large cores on the selected QF_NIA pair, then rejected bounded four-group deletion after it shrank clauses but decided neither target; temporary solver code was removed. |
| 2026-08-07 | `704318a5f` | Refreshed the complete-parity manifest's sole stale source identity after the pinned-`just` CI workflow change; outcomes, populations, gates, and parity credit are unchanged, and full parity-docs/authority/links pass. |
| 2026-08-07 | `db7b426e8` | Replaced a hidden load-sensitive two-second string/integer coupling deadline with deterministic 128-candidate and 2,000-node ceilings while preserving caller timeouts; the direct budget regression, 14-test fixture, and all-target solver Clippy pass. |
| 2026-08-07 | `7b35dbcb6` / `8bab16429` / `799c5c8c7` | Kept fallible DPLL oracle fixtures explicit and synchronized evidence plus representative Lean expectations with the checked Boolean-simplification route selected after bounded duplicate short-circuiting. |
| 2026-08-07 | `9f94e1873` | Provisioned exact, commit-pinned `just` for both hosted docs gates after three remote runs exposed that the integrated readiness fixtures require the registered executable; the 165-test local resume aggregate passed with one expected skip. |
| 2026-08-07 | `63c82a6ef` / `4ff9a82c6` / `3c5816fdf` | Bounded giant SMT-LIB `distinct` expansion, preserved typed arithmetic reconstruction declines, completed the 67-row A3 census, and rejected zero-gain probe-model reuse without retaining experimental code. |
| 2026-08-07 | `2072483f8` | Retained the bounded disk cleanup while preserving dirty worktrees and every unmerged branch tip. |
| 2026-08-06 | `2925efea5` / `8ed5ad089` | Completed A2 topic and integration review, merged the exact-source SMT-COMP readiness stack, and passed focused plus uninterrupted combined-main `just check`; live C0/F2 remains separately prohibited. |
| 2026-08-06 | `e4bb854bf` | Implemented R5's operator-owned exact-source Axeyum build, schema-v3 source/tool/output/binary/run/completion replay, and rejecting fixture matrix; integration and live action remain prohibited. |
| 2026-08-06 | `ebbabb34c` | Retained the fresh QF_UFLIA 94/200 versus 180/200 run; its complete normalized status matrix is identical to the accepted baseline and has zero disagreements. |
| 2026-08-06 | `4477f2bb9` / `198f2dc1b` / `71ca85d9f` | Bounded the complete DL probe front end, preserved fallback time, passed full topic and exact-SHA gates, and retained QF_IDL 68/200 versus 124/200 with zero losses or disagreements. |
| 2026-08-06 | `5ce07c55e` / `8ea6a7cad` | Made parity resume identity exact-path and fail-closed for duplicate, ambiguous, or drifted populations. |
| 2026-08-06 | `c5d617c10` / `b353419e7` / `54b366517` | Retained fresh QF_NIA 34/200, QF_LIA 117/200, QF_LRA 86/200, and QF_RDL 105/200 runs, all with zero disagreements. |

Older landed changes remain in Git and their dated result notes; this table is
deliberately bounded to changes that still determine the immediate queue.

## Next Actions

Work in this order unless new evidence reveals a wrong verdict, crash, data-loss
risk, or invalid gate. Those are P0 and preempt the queue.

The ordered ten-item programme remains A2 through A11. A1 and A2 are retained
here as closed evidence boundaries. A3 remains incomplete, but all currently
preregistered bounded mechanisms are closed negatively. A4 has now also yielded;
A5 is the first active item.

**Immediate action (`WIP`).** Diagnose QF_RDL attempt 001's cumulative
exit-101 failure by sampling per-row RSS/virtual memory across the exact list;
the row and 21-row tail are negative controls. Do not change budgets or credit
196 partial rows. A repair needs a bounded regression, focused/full gates, and
a fresh QF_LRA row-1 restart under the unchanged 24-second/8-GiB envelope.
The failed 172-row abort stream,
the complete-but-parse-invalid 200-row stream, the failed 168-row pursuit abort,
the failed 58-row QF_IDL abort, and the failed 63-row declaration-scale QF_IDL
abort all remain non-credited, as does the new 196-row QF_RDL stream. The valid
200-row QF_LRA/QF_IDL captures at `e996afd83` prove the current repairs but
cannot stand in for the final three-division census after another behavior
change. Stop
on any historical-decision loss, wrong verdict, stderr, malformed trace, or
process failure. Only valid atomic QF_LRA success metadata authorizes sequential
QF_IDL and QF_RDL capture and the preregistered derivation. No score gain is
claimed by changing a crash into typed `unknown`, and no further solver or
budget change is authorized before the complete monotone census identifies a
repeated mechanism.
A4's v3 restart decided 93/200, with one 2/3-SAT wall-clock boundary. Both
model-reuse variants failed isolated stability and were removed; do not retry
until 94 happens to pass. A3/A4's negative routes remain closed. A2 still does
not authorize C0/F2, host/NAS mutation, allocation, or a solver fleet.

**Parallel documentation action.** The comprehensive pass and 2026-08-09
README application/vision revision are closed. Continue only for a concrete
stale claim; keep application maturity and sub-document links aligned, but do
not duplicate generated capability tables or modify solver behavior to match
prose. The user/reference/internals/crate surfaces and all 34 Cargo examples are
indexed, and source guards reject universal proof claims.

### A1 — Complete arithmetic deadline and resource enforcement (`DONE`, P0)

Shared deadlines, CAD cancellation, deterministic LRA normalization ceilings,
the DL fallback-reservation repair, exact resume identity, six fresh retained
division runs, and their ledger commits are complete. See the closure note
linked above. The one QF_LIA whole-sweep miss is retained honestly and bounded
by a 3/3 isolated UNSAT reproduction well inside the protocol budget.

### A2 — Rebase and finish credited full-library readiness (`DONE`, P0)

**Why now.** Eleven division samples are useful, but representative general
solving-power remains unmeasured. The topic branch
`agent/smtcomp/full-preparation-live` contains substantial process-free work
based on older July state and must not be merged or launched as-is.

**Completed checkpoint.** The branch audit and R1--R5 process-free topic are
complete. R5 is implemented at `e4bb854bf` with 52 focused tests / 82 subtests,
165 aggregate tests, scoped gates, and a successful real locked/offline build
smoke. Exact topic `2925efea5` was pushed, matched its remote, and passed one
uninterrupted R3-isolated `just check`. Integration review proved the topic was
strictly ahead with no divergence and previewed a conflict-free merge. Merge
`8ed5ad089` then passed the focused post-merge gates and the full combined-main
`just check` with external frontier artifacts and a clean tracked tree. The
exact disposition and gate separation are in the dated A2 audit and R5
implementation result.

**Next slice.** None in A2. Preserve the integrated process-free contract and
move to A3. Do not execute the constructed live operator merely because its
process-free and integration gates are green.

**Exit.** Current-main identity is immutable, readiness and resume gates are
green, the published root is process-free with `launch_authorized=false`, and
an independently reviewed later step authorizes any bounded live execution.

**Stop.** No host/NAS mutation or solver launch from stale refs, red gates, or
an unaccepted root. Follow
[`docs/plan/smtcomp-full-library-workstream/README.md`](docs/plan/smtcomp-full-library-workstream/README.md).

### A3 — Re-certify and deepen QF_NIA (`WIP`, P1)

**Why now.** The current clean entry is 34/200 versus 89/200 (38.2%), a material
gain over the former 21-decision entry but still the weakest retained arithmetic
ratio. Twelve Axeyum-only decisions also make replay and causal classification
important, not just score growth.

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

**Next slice.** None is currently evidence-authorized. The v1/v2
[`clause-estimate result`](docs/plan/qf-nia-a3-clause-estimate-attribution-v2-result-2026-08-07.md)
closed the final selected route at its complete-record gate without changing
production code. Preserve the 34/200 ledger, every negative control, the
64,000,000 pre-allocation ceiling, and original-term replay, then move to A4.
Resume A3 only when independent new evidence identifies a bounded mechanism;
do not revive probe-model reuse, reconstruction reservation, group deletion,
relevance ladders, or fresh-parse clause attribution, and do not raise general
caps.

**Exit.** One preregistered cluster improves a fresh whole-list result without
losing any of the 34 decisions; all SAT answers replay on the original terms and
the ledger remains disagreement-free.

**Stop.** Do not optimize on the 12 Axeyum-only cases as if they were reference
failures, and do not raise general caps to convert time into apparent breadth.

### A4 — Deepen QF_UFLIA combination (`WIP`, yielded, P1)

**Why now.** QF_UFLIA is 94/180 (52.2%) with zero Axeyum-only decisions and 86
reference-only cases, making it the clearest combined-theory depth gap.

**Next slice.** None is evidence-authorized. The theory-model reuse result
stopped negatively; revisit only with deterministic-work evidence for the
conjunctive LIA probe. The 26 wide-integer rows remain ADR-0376 controls.

**Exit.** One preregistered, replay-checked cluster improves the clean full-list
result without losing any of the 94 decisions or weakening retained controls.

**Stop.** No general cap increase, speculative recursive MBQI, or unchecked SAT
model credit.

### A5 — Consolidate linear arithmetic after warm simplex and DL (`WIP`, P1)

**Why now.** QF_LRA, QF_IDL, and QF_RDL improved sharply but remain strict
subsets of their references. The newest architecture has not yet received one
cross-division residual census.

**Next slice.** Classify normalization failures, unsupported
difference shapes, disequalities, explanation blowups, and ordinary search
failures across the three current ledgers. Treat the repaired high-memory LRA
normalization case and the rejected global 12/12 DL split as permanent controls
before adding new DL syntax. The
[`v1 cross-division census preregistration`](docs/plan/qf-linear-a5-cross-division-census-v1-preregistration-2026-08-07.md)
freezes all three populations and historical sidecars, makes all 259 retained
decisions monotonicity controls, and authorizes only fresh current-Axeyum traces
plus lossless derivation. No production change is yet authorized.

**Exit.** A/B measurement is monotone across all three divisions, exact
Farkas/DL evidence checks pass, deep input returns without recursion abort, and
the retained arithmetic fuzz suites execute nonzero cases.

### A6 — Close proof-production errors and evidence gaps (`TODO`, P1)

**Why now.** Definitive answers without checkable evidence violate the product's
core direction even when verdicts are sound.

**Next slice.** Fix the two QF_NIA `IntPow2` production errors first. Then use
route provenance—not query syntax alone—to split the 38 QF_BV bare UNSAT rows
and the broader arithmetic/string-sequence proof gaps.

**Exit.** Zero production errors; every newly credited certificate passes its
own independent checker; text-only recheck, arena-backed check, Lean
reconstruction, and bare-result counts remain separate fields.

**Stop.** Never relabel arena-backed checking as serialized proof replay or
generate proof credit through query-only re-derivation.

### A7 — Finish route observability before searched policy (`TODO`, P1)

**Why now.** `RouteTrace::to_json` landed, but the bench path and quantifier
preamble are incomplete. The proposed exploration tracker also incorrectly
placed T3.5 before its own G1 phase-3 gate.

**Required order.** Accept or revise the blocking ADRs; complete T0.2 route
registry; complete T0.6 recorder sites and `solve_explained`; finish T0.1 bench
persistence; add T2.5 public-corpus coverage; run T2.3/G1; only then consider
T3.5 policy-v0 equivalence.

**Exit.** Every registered route has a stable ID, the representative corpus
covers the catalogue or records explicit gaps, legacy dispatch replays exactly,
and G1—not enthusiasm—decides whether searched policy proceeds.

**Stop.** The exploration track remains proposed and may not preempt A2–A6.
See [`docs/plan/exploration-track/`](docs/plan/exploration-track/README.md).

### A8 — Implement SMT-LIB ordered command/event capture (`TODO`, P2)

**Why now.** The checked conformance matrix has six absent command families,
seven accepted no-ops, and zero interactive textual-session rows.

**Next slice.** Accept or revise ADR-0342, then implement S1 capture-only ordered
command/event IR with scoped declarations/definitions, reset epochs, exact query
snapshots, immediate options, and atomic continued errors before rendering.

**Exit.** The registered 14 invariants and 20 fixtures/107 commands pass through
the product path; malformed commands cannot partially mutate session state.

**Stop.** Do not add isolated output helpers and call them textual conformance.

### A9 — Restore official Lean execution and shrink the prelude (`TODO`, P2)

**Why now.** The local host currently has neither `lean` nor `elan`; remote
70/70 attestation remains open; seven ledger rows are already classified as
derivable theorems.

**Next slice.** Provision the checksum-pinned Lean 4.30 executable, prove it
runs outside the repository working directory, obtain the remote 70/70 result,
then replace the seven derivable axioms with theorem terms in dependency order.

**Exit.** Kernel tests, official Lean, generated ledger counts, declaration
order, parity docs, and mutation controls all pass; no hard-coded old count
survives.

**Stop.** Do not widen into String literals, quotient computation, or broad
ecosystem claims during this bounded trust-reduction slice.

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
targets. The later authorized cleanup preserved all 24 dirty deltas as labelled
stashes, retained every branch tip, removed the inactive checkout directories,
and initially left two registered worktrees. After the A3 result merged, its
clean 71.0 GiB topic target was removed and the merged checkout retired while
its branch remained. After merge `d09e6debb`, the final clean topic checkout
and its 176 GiB target were also retired while preserving the local and remote
branch. Only `main` is registered; `/` currently has about 902 GiB free and the
`/tmp` tmpfs about 28 GiB free. Automation and fixture coverage remain open.

**Exit.** The inventory is deterministic and tested against dirty, merged,
unmerged, detached, missing-target, and malformed-cache fixtures. A dry run
identifies disposable bytes without mutation; cleanup requires explicit exact
targets and preserves branches and live work.

**Stop.** Never recursively delete a worktree root, infer safety from age alone,
or remove dirty/unmerged state to meet a free-space target.

## Workstream state

| Workstream | State | Current boundary / next action |
|---|---|---|
| Integration and gates | `DONE`; current checkpoint | Local and remote `main` contain audited merge `6be32cb4a` plus its tracker checkpoint; A3 topic `2269488ef` is pushed and merged. Exact topic/merge pre-push gates and focused post-merge tests are green. Hosted CI remains separate evidence. |
| Arithmetic deadline reliability | `DONE` | Shared deadline, CAD polls, LRA ceilings, bounded DL probing, exact resume identity, and six fresh retained divisions are complete; see the 2026-08-06 closure note. |
| Full-library measurement | `WIP`; A2 readiness `DONE` | The R1--R5 readiness stack is integrated by `8ed5ad089` and focused/aggregate/scoped/topic/full-main green; the real registered offline-build smoke passed. No live run, preparation root, or launch authority exists. A later live C0/F2 step requires separate review. |
| QF_NIA breadth | `WIP`, yielded | Current clean result remains 34/200 versus 89/200. Reconstruction, large-core deletion, relevance activation, and bounded clause-estimate attribution are closed negatively without production solver code. The final diagnostic failed its exact pipeline-boundary record gate; no mechanism or 200-row run is authorized and the 64,000,000 ceiling remains. Move to A4 unless independent new NIA evidence appears. |
| QF_UFLIA breadth | `WIP`, yielded | Historical 94/180 remains; the exact-commit restart produced 93/200 because one SAT case is wall-clock unstable. No sidecar or new result was credited. |
| LRA/IDL/RDL | `WIP` | Current results are 86/146, 68/124, and 105/155; A5 owns cross-division consolidation. |
| QF_BV/QF_SLIA/UF/QF_ABV | `WIP`, strong selected cells | Preserve current ledgers; do not prioritize small score gains above A2–A6. |
| Evidence and Lean reconstruction | `WIP` | A6 and A9; distinct certificate/check/reconstruction claims. |
| Route exploration | `BLOCKED` beyond catalogue work | Proposed track; T0.2/T0.6/T0.1/T2.3 precede T3.5. |
| SMT-LIB/API conformance | `WIP` | A8 then A10; S1 command/event IR first. |
| CAS parity | `BLOCKED` by deliberate pause | Wave-24 code `01d47334` and pause commit `245d8f25` are ancestors of current main. Do not start wave 25 until the user resumes it and retained specialized gate evidence is re-audited. |
| Consumer apps / verified systems | `WIP`, non-critical path | Existing EVM, verifier, property, reflection, and symbolic-execution slices remain useful; do not preempt A2–A7 without measured demand. |
| Foundational resources | `WIP`, separate content lane | Keep generated-resource gates green; record only project-level priority changes here. |
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; 34 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
| Worktree and build-cache hygiene | `WIP`, recovered | A11; only clean `main` is registered. The cleanup stored all 24 inactive dirty deltas in labelled stashes, retained every branch tip, removed the inactive checkouts and one 1.7 GiB session tree, retired the earlier clean A3 target, and finally removed the merged explanation-partition checkout with its 176 GiB Cargo target. Current free space is about 902 GiB on `/` and 28 GiB on `/tmp`; all topic branches remain preserved. Next automate the deterministic read-only inventory and exact-target cleanup classification. |

## Resume protocol

1. Read this file first. Do not reconstruct current priority from historical
   result notes, old status journals, branch names, or worktree age.
2. Verify live state:

   ```sh
   git status --short --branch
   git fetch origin
   git rev-parse HEAD origin/main
   git worktree list
   gh run list --limit 10
   ```

3. If `main` is dirty, diverged, or owned by another lane, create an isolated
   worktree from current `origin/main`. One writer, one branch, one worktree.
4. Select the first unblocked item in **Next Actions**. Read its detailed phase,
   ADR, result notes, foundational DAG implications, and named handoff before
   editing.
5. During iteration, run the narrowest relevant crate or script tests. Run the
   aggregate pre-merge gate once on the finished branch. Confirm nonzero test
   counts and retain real exit codes.
6. Commit and push owned paths only. Integration requires conflict preview,
   green branch gates, merge, green main gates, pushed main, and remote-ref/CI
   verification.
7. Update this file in the same bounded increment:
   - status and exact evidence;
   - next executable action;
   - blocker or stop condition;
   - committed/pushed/integrated/remote states separately.

For concurrency and resource rules, follow
[`docs/contributor-guide/multi-agent-operations.md`](docs/contributor-guide/multi-agent-operations.md).

## Planning rules

- **One mutable project tracker:** update this file only. Root `STATUS.md` is a
  pointer; do not create root `TODO.md`; subsidiary `STATUS.md` files may retain
  local historical evidence but may not claim project-wide priority.
- **Evidence outranks prose:** benchmark JSON/TSV, generated matrices, test
  output, Git objects, remote refs, and CI results determine status. Correct this
  file when they disagree.
- **Wrong verdicts preempt everything:** reproduce, root-cause, regress, and
  repair before breadth or performance work.
- **No false green:** a focused pass is not a full gate; a running job is not a
  pass; a process-free readiness artifact is not launch authorization; a
  local commit is not integration.
- **No journal growth:** result detail belongs in a dated note under
  `docs/plan/` or a committed benchmark artifact. Keep only the current state,
  ordered queue, and a short recent-change table here.
- **Decisions require ADRs:** public operators, rewrites, encodings, backends,
  evidence artifacts, logic fragments, or priority-changing architecture need
  the applicable research question and ADR resolved first.
- **Determinism and replay are product promises:** stable order, explicit seeds
  and limits, original-term SAT replay, and independent UNSAT checking remain
  mandatory.

## Durable detail map

- Short public implementation account: [`docs/PROJECT-STATE.md`](docs/PROJECT-STATE.md)
- Full plan index: [`docs/plan/README.md`](docs/plan/README.md)
- Foundation roadmap: [`docs/research/08-planning/roadmap.md`](docs/research/08-planning/roadmap.md)
- Foundational dependency DAG: [`docs/research/08-planning/foundational-dag.md`](docs/research/08-planning/foundational-dag.md)
- Open research questions: [`docs/research/08-planning/research-questions.md`](docs/research/08-planning/research-questions.md)
- ADR index: [`docs/research/09-decisions/README.md`](docs/research/09-decisions/README.md)
- Capability matrix: [`docs/research/08-planning/capability-matrix.md`](docs/research/08-planning/capability-matrix.md)
- Scoreboard and parity: [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md), [`bench-results/PARITY.md`](bench-results/PARITY.md)
- Proof gaps: [`docs/plan/generated/proof-gap-matrix.md`](docs/plan/generated/proof-gap-matrix.md)
- SMT-COMP lane: [`docs/plan/smtcomp-full-library-workstream/README.md`](docs/plan/smtcomp-full-library-workstream/README.md)
- Lean implementation: [`docs/plan/lean-system-implementation-plan-2026-07-21.md`](docs/plan/lean-system-implementation-plan-2026-07-21.md)
- Exploration proposal: [`docs/plan/exploration-track/README.md`](docs/plan/exploration-track/README.md)
- CAS pause handoff: [`docs/plan/cas-parity-handoff-2026-07-22.md`](docs/plan/cas-parity-handoff-2026-07-22.md)

## Consolidation record

The 2026-08-05 consolidation removed two conflicting append-only root journals
and one subsidiary live tracker from active use. It corrected these stale
claims:

- CAS wave 24 was described as unpushed and unintegrated; its code and pause
  commits are both ancestors of current main.
- An August 1 shell-failure resume block remained active after later green CI
  and clean parity reruns.
- The reality summary still said seven measured parity divisions after the
  ledger reached eleven.
- The exploration tracker called T3.5 next while its own G1 gate blocked all of
  phase 3.
- Repository instructions disagreed about whether `PLAN.md` or `STATUS.md` was
  the mutable source.

The containing commit establishes this file as the only current project-level
authority. Historical claims remain reviewable through Git and the dated result
notes they cite.
