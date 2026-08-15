# Axeyum plan, status, and next actions

> **Generated; do not edit by hand.** Sources: project-wide sections in
> [`docs/plan/global/`](docs/plan/global/README.md), one file per lane in
> [`docs/plan/status/`](docs/plan/status/README.md). Edit **your lane's file**
> and run `python3 scripts/gen-plan.py`; `--check` is a gate. This file was
> touched 67 times in 24 hours by concurrent lanes on 2026-08-13/14 and one
> lane's edit was swept into another's commit — that is what the split fixes.

**Canonical project tracker.** This is the repository's single mutable source
for current project status, ordered work, blockers, and resume guidance. Read it
first and update it before ending a project-level work session.

- Last consolidated: **2026-08-13**
- Current `main` contains linear A5 through exact commit
  `4b6b765556c4ff1fb4dc47ffd75568a3ed1f9246` by conflict-free fast-forward
- Active A5 large-equality DL repair: code at exact pushed
  `46edad8bac7e193303871d601914fef2115bf721`; its documentation descendant
  `d1b570f91c27f83ef55127ea3d1c8baf700f05a5` passed the full release gate
- Latest full-gate attempt: exact pushed checkpoint `d1b570f91c27f83ef55127ea3d1c8baf700f05a5`
  passed `just check` with external frontier artifacts and exit 0
- Latest comprehensive green exact-commit gate:
  `d1b570f91c27f83ef55127ea3d1c8baf700f05a5` (`just check` exit 0)
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

Pre-consolidation journals are immutable in Git at revision `803c08439`.

## Status

**A5 repair history.** Fail-closed LRA/IDL restarts exposed wide-core and
first-solve allocation growth, mixed-numeric parsing, native recursion,
unhonored construction deadlines, and declaration-scale quadratic work. Their
pushed bounded/iterative repairs and every non-credited partial stream are
retained in the
[failure/repair record](docs/plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md);
the current release returns typed `unknown` on each former abort trigger.

Axeyum is a working research-grade automated-reasoning stack with a pure-Rust
default path, replay-checked SAT models, multiple independently checked UNSAT
evidence routes, broad but uneven theory support, an independent Lean-core
checker/importer, and several consumers. It is not yet a drop-in Z3 replacement
or a replacement for the Lean system.

The [Lean requirements](docs/plan/lean-kernel-requirements-2026-08-13.md) are
**WIP**. Nat is zero-axiom; Int reconstruction remains assumption-bearing.

Exact pushed `e996afd83` passed `just check`; its RDL capture then failed closed
at 196/200 because allocator arenas accumulated across files. ADR-0379 rejects
allocator tuning and uses one inherited-limit child at a time. The isolated
200-row trigger passed with zero stderr; the old partial stream remains
non-credited. See the
[result](docs/plan/qf-linear-a5-rdl-process-isolation-repair-2026-08-09.md).

Exact pushed repair `5a53012e1` passed the complete external-frontier
`just check` gate with exit 0. The preregistered V2 sequence then produced three
structurally valid atomic 200-row captures with zero stderr and the exact
pushed source/binary identity. QF_LRA decided 89, QF_IDL 68, and QF_RDL 105;
the RDL stream crossed the former row-196 process boundary and completed in
2,127,949 ms. The lossless derivation nevertheless stopped correctly:
historical QF_LRA UNSAT control
`sal/windowreal/windowreal-no_t_deadlock-17.smt2` returned deterministic pre-SAT
resource `unknown` at 1,217 arithmetic atoms and 6,526 CNF variables. Gains
elsewhere hid that loss in the aggregate count. The entire V2 sequence is
non-credited. A bounded
[pre-SAT boundary discriminator](docs/plan/qf-linear-a5-pre-sat-boundary-monotonicity-v1-preregistration-2026-08-10.md)
now owns the P0 path; no residual grouping or census-based breadth change is
authorized.

The bounded repair is exact-pushed at `8a6de50ac`. Its rebuilt 11,859,344-byte
binary (`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`)
replayed the lost control as byte-identical UNSAT in 3/3 observations at 0.10
seconds and below 17 MiB peak RSS; both allocation-abort controls and the
low-atom/31,944-variable IDL control retained typed pre-SAT declines. Formatting,
strict all-feature solver Clippy, all 1,091 solver-library tests, deep-input
16/16, online arithmetic/CDCL(T) 41/41, and both differential suites are green
with zero disagreement. Exact pushed checkpoint `3267432a7` then passed one
uninterrupted external-frontier `just check` in 6,410 seconds with exit 0; see the
[result](docs/plan/qf-linear-a5-pre-sat-boundary-monotonicity-v1-result-2026-08-10.md).

The `sc-39` classifier repair (`d646382e7`, gated at `b9938576b`) and the V2
DL repair (`d1b570f91c2`, full external-frontier `just check` exit 0) are
release-qualified. Exact-pushed `6d4718e13` completed fresh atomic QF_LRA and
QF_IDL captures — 90/200 and 70/200, six agreeing gains, zero losses or wrong
verdicts, all controls retained. QF_RDL is authorized but not started. Full
detail, including the rejected non-credited streams, is in the
[result](docs/plan/qf-linear-a5-idl-extended-dl-slice-v2-result-2026-08-11.md).

A3 is **WIP**. Pushed result checkpoint `3696e7dd5` is integrated on current
main by `47d8cd956`; its retired source tip is in the 2026-08-12 branch-cleanup
bundle. The repaired complete
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

Disk cleanup preserved every branch and salvaged dirty inactive-worktree deltas
to labelled Git stashes before retiring their checkouts. Reproducible Cargo
artifacts and empty failed-run directories were removed only after ancestry,
cleanliness, and open-file checks. Only clean `main` remains registered; retained
evidence and unrelated temporary projects were untouched.

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
| 2026-08-15 | `geometry-frontier` | default geometry monomial order switched to degree-reverse-lex, justified by a per-subset per-order audit showing 6 unchanged condition sets and 6 byte-identical certificates — and every subset *decided*, which upgrades the corpus's minimality claim from budget-scoped to absolute; `rhombus-diagonals-perpendicular` promoted off the frontier as the seventh certified theorem with its non-degeneracy counterexample and both tamper controls, the controls now running over every saturated certificate rather than the first; `euler-line`'s obstruction measured rather than timed (basis growth and a quadratic S-pair backlog, not width and not overflow) via new `ReductionStats` and an S-pair ladder | `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/src/groebner_cert.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/examples/geometry_order_audit.rs`, `crates/axeyum-cas/examples/geometry_obstruction.rs`, `artifacts/geometry-certificates/rhombus-diagonals-perpendicular.json`, `artifacts/facts/F-geometry-rhombus-diagonals-perpendicular.json` |
| 2026-08-15 | `euler-linearity` | `euler-line` certified and promoted off the frontier by **linear elimination** rather than a bigger budget — 4–6 ms and 0 S-pairs against a Gröbner run that had not returned in 27 minutes — with the cofactors derived from the adjugate identity so they stay against the ORIGINAL hypothesis generators, and the `det^d` multiplier divided out through the Rabinowitsch generator (`N = 2`, so the saturation cofactor is `−conclusion·(1 + d·z)`); a multiplier the stated conditions do not license is a refusal; condition-set minimality established **absolutely** by refuting every proper subset with a committed counterexample rather than by a `2ⁿ` budget-relative audit; the on-locus-but-harmless tamper control repaired from a constant that skipped every triangle theorem into a covered table; `geometry_check.rs` untouched and the seven older certificates byte-identical. Pappus's hexagon theorem then also certified (three 2x2 blocks, 292 s, checker-verified) and deliberately **left on the frontier**, because its three conditions can only be necessitated as a set and the new minimality ratchet correctly refuses the budget-relative claim | `crates/axeyum-cas/src/linear_elim.rs`, `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/src/lib.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/examples/geometry_linear_route.rs`, `crates/axeyum-cas/examples/emit_geometry_certificates.rs`, `artifacts/geometry-certificates/euler-line.json`, `artifacts/facts/F-geometry-euler-line.json` |
| 2026-08-15 | `pappus-minimality` | Pappus's hexagon theorem promoted into the corpus with **one** non-degeneracy condition instead of three (6.7 ms against 292 s), and its minimality established **absolutely** — the previous lane's three collapsed attempts to necessitate a single condition turned out to be a *proof that each condition is individually redundant*, confirmed three ways (synthetic strata argument; exhaustive `F_p` decision for seven primes over the committed polynomials, orbit reduction cross-checked against a full enumeration; and a **certificate for each condition in isolation**). The root cause is ADR-0460: the route's subset tests were all *decided* and therefore read as absolute under ADR-0455, but they tested the subset against a decomposition the producer had already fixed, so they were **representation-relative** — decided and wrong. Fixed by `licensed_blocks`, which lets the condition subset choose its own block decomposition. New `cofactor_ansatz` module: bounded-degree ideal membership by exact sparse linear algebra, which settles in ~25 ms with `±1` coefficients a residue Buchberger was killed on after 7.5 minutes without returning; incomplete on purpose, bounds the shape of the system and never the solve, self-checks its own identity. `geometry_check.rs` untouched across a third independent producer; the handover refuses to run when no block was consumed, which is what keeps the eight older certificates byte-identical (**8 unchanged, 1 written**) | `crates/axeyum-cas/src/cofactor_ansatz.rs`, `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/src/lib.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/examples/pappus_condition_subsets.rs`, `crates/axeyum-cas/examples/geometry_cofactor_routes.rs`, `artifacts/geometry-certificates/pappus-hexagon.json`, `artifacts/facts/F-geometry-pappus-hexagon.json`, `docs/research/09-decisions/adr-0460-a-decided-subset-test-may-still-be-a-test-of-the-route.md` |
| 2026-08-15 | `0fc7cc357` | `Int.subNatNat`'s borrow proved (shift lemma, two characterisations, elimination principle) and five of the six remaining integer axioms discharged: `add_assoc`, `mul_assoc`, `left_distrib`, `add_le_add`, `add_lt_add_of_le_of_lt`. `integer: axiom=6 → 1`; 50 `Int` theorems, all with an empty axiom footprint; real-Lean gate green at 112 checks. |
| 2026-08-15 | `7c7b0ca16` | `Real`'s 30 axioms measured as an ordered-ring package (no inverse/completeness/Archimedean) and modelled in the constructed ℤ: `build_int_model_of_arith` admits 22 kernel-checked witnesses, all with an empty axiom footprint and all syntactically the `Int` law. `Int.sq_nonneg` proved (`Int: 50 → 51` derived, 51 empty footprints). Measured and pinned that this kernel has **no `Quot.sound`**, so a quotient ℝ is inexpressible, not merely expensive — correcting three comments and the ℤ diary. ADR-0456. |
| 2026-08-15 | `ordered-ring-reconstruct` | Farkas/SOS refutations generalize over the ordered-ring interface: empty `axiom_footprint`, confirmed by real Lean's `#print axioms`, with the `Real`-specific statement recovered by instantiation (ADR-0457, `F:ordered-ring-farkas-refutation`). |
| 2026-08-15 | `lra-dispatch` | Conjunctive `QF_LRA` reaches `ProofFragment::Lra` at the Lean facade instead of the contentless `LraDpll` shim, with the first tests asserting a query reaches the real reconstructor; structural-attestation modules now self-label, are typed by `LeanModuleContent`, are cross-checked against the fragment table on every call, and are declined by `prove_unsat_to_lean_theory_module`. |
| 2026-08-15 | `33cbe5131` | Formalized-math strand started: real Lean import measured at 13/40 with a four-cluster blocker census, `imported-kernel-lean` proof route (ADR-0454), five imported facts with pinned streams, `01-collect.md` rewritten against cited measurements. |
| 2026-08-15 | (pending) | `Proj`/`Proj` congruence in `def_eq` closes 9 of 10 root import blockers (40-stream census: 22→37 clean, 10→1 root); first-class decline census `census_ndjson`; pinned `Nat.add_comm` capability fixture. |
| 2026-08-15 | `d326c74af` | WHNF cache key split on `has_fvars` (closed → kernel, open → `LocalContext`) with a `reduction_ctx_reads` tripwire; the collision demonstrated as a test against a kept pre-fix replica; K-like reduction with a guard-by-guard controlled negative suite; import census 37/40 → **40/40**, 1 root blocker → **0**. |
| 2026-08-15 | (pending) | Literal `Nat` arithmetic in the kernel (Lean's `reduce_nat`, 14 operations, guarded by a validated `Nat`/`Bool` bootstrap and a non-interning name lookup), with 15 new tests, guard-by-guard controls, and a real-Lean crosscheck generated from this kernel's own answers (gate floor 105 → 107, measured 115); `scripts/lean-import-scale-census.sh` censuses a seeded sample of the whole exported environment with roots separated from cascades; census example runs on a 512 MB stack and reports reader-refused streams as their own class. |
| 2026-08-15 | (pending) | Primitive Lean `String`-literal semantics in the trusted kernel: a checked `String`/`String.ofList`/`Char.ofNat`/`List` bootstrap, the exact Unicode-scalar expansion, Lean's projection / recursor / def-eq hooks, the `strVal` wire arm, and the writer arm with Lean's own JSON escape grammar. 11 mutation controls plus hook-removal controls, a real-Lean crosscheck generated from this kernel's reducts (floor 107 → 109, measured 117), the ADR-0366 root export reproduced byte-exactly and imported clean, and a re-census of both seeded samples. |
| 2026-08-15 | (pending) | `docs/reference/examples.md`: documented six landed Cargo examples that `check-parity-docs.py` flagged as missing — `geometry_linear_route`, `lean4export_census`, `nat_add_reduction_probe`, `arith_model_witness`, `ordered_ring_refutation` (the five named by the task), plus `prelude_build_timing` (flagged by the gate itself, not on the original list). The example-count marker in `docs/documentation-plan.md` and `PLAN.md` was already correct (67) and needed no edit. |
| 2026-08-14 | `19f4c769b` | Automatic hypothesis minimisation (`hypothesis_min`): two route-B Rado lemmas that stay `unknown` at 1800 s close in ~2 s with the same subsets a human found in ~32 min; the boundary is measured to be `nra.rs:107` `MAX_CROSS_PRODUCTS = 2`, not hypothesis count, and the guards are mutation-tested one deletion at a time (agent-k). |
| 2026-08-14 | `telescoping` | Creative telescoping (Zeilberger) with an independent certificate checker; 5 classical binomial identities landed as `cas-certificate` facts; 10 tamper controls reject perturbed certificates | `crates/axeyum-cas/src/telescoping.rs`, `crates/axeyum-cas/src/telescoping_check.rs`, `crates/axeyum-cas/tests/telescoping_identities.rs`, `artifacts/facts/F-*binomial*.json`, `artifacts/facts/F-chu-vandermonde-convolution-recurrence.json` |
| 2026-08-14 | `telescoping-scale` | Gosper–Petkovšek derived denominator and degree bound replace the `Q` ladder and the degree sweep (Chu–Vandermonde 18.5 s -> 46.7 ms); order-2 recurrences reachable (Franel); symbolic base cases close Chu–Vandermonde's closed form; certificates serialised to `artifacts/cas-certificates/` and re-checked from file; 3 new facts | `crates/axeyum-cas/src/telescoping.rs`, `crates/axeyum-cas/src/telescoping_check.rs`, `crates/axeyum-cas/src/telescoping_json.rs`, `crates/axeyum-cas/tests/telescoping_identities.rs`, `crates/axeyum-cas/tests/telescoping_certificate_artifacts.rs`, `artifacts/cas-certificates/*.json`, `artifacts/facts/F-chu-vandermonde-convolution.json`, `artifacts/facts/F-cross-binomial-row-sum.json`, `artifacts/facts/F-franel-numbers-recurrence.json` |
| 2026-08-14 | `geometry` | new domain on the `cas-certificate` route: coordinatisation front end + Rabinowitsch saturation + independent checker; 6 classical theorems certified with committed degenerate counterexamples for every side condition used; measured that 4 of 6 need NO non-degeneracy condition; 2 frontier theorems recorded with timings; 6 new facts | `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/geometry_check.rs`, `crates/axeyum-cas/src/geometry_json.rs`, `crates/axeyum-cas/src/geometry_corpus.rs`, `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs`, `crates/axeyum-cas/tests/geometry_encoding_agreement.rs`, `crates/axeyum-cas/examples/emit_geometry_certificates.rs`, `crates/axeyum-cas/examples/geometry_probe.rs`, `artifacts/geometry-certificates/*.json`, `artifacts/facts/F-geometry-*.json` |
| 2026-08-14 | `mvpoly-bignum` | `MvPoly::gcd` moved into an unbounded-integer ring with per-step content removal (Apéry's shift quotient: 4187-bit peak against a 127-bit type, now 76); Apéry's recurrence found and verified, with an artifact and a fact; `CofactorOutcome::Declined` split into ceiling-versus-overflow and propagated to geometry and the solver; degree-reverse-lex added to `groebner.rs`, measured at 1.3–2.2× on the geometry corpus, and shown to reach `rhombus-diagonals-perpendicular` in 23.6 s where `lex` declines after 287.8 s | `crates/axeyum-cas/src/mvpoly/big.rs`, `crates/axeyum-cas/src/mvpoly.rs`, `crates/axeyum-cas/src/groebner.rs`, `crates/axeyum-cas/src/groebner_cert.rs`, `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/lib.rs`, `crates/axeyum-solver/src/cas_poly.rs`, `crates/axeyum-cas/tests/telescoping_identities.rs`, `crates/axeyum-cas/examples/telescoping_search_cost.rs`, `crates/axeyum-cas/examples/geometry_probe.rs`, `crates/axeyum-cas/examples/emit_telescoping_certificates.rs`, `artifacts/cas-certificates/apery-numbers-recurrence.json`, `artifacts/facts/F-apery-numbers-recurrence.json` |
| 2026-08-14 | `229cceb1e` | ℤ constructed over the proved ℕ development: `Int` inductive + operations as checked definitions, 20 laws derived with empty axiom footprints — including ADR-0106's decidable integer equality. `integer: axiom=34 → 6`. |
| 2026-08-14 | `22f3db735` | `F:quantifier-negation-duality` proved: quantifier-negation duality and alpha-equivalence in the canonicalizer, and in the certificate checker independently (import backlog 10 to 9). |
| 2026-08-14 | `pending` | FP kernel-equivalence enters the fact ledger: seven facts (4 proved, 2 refuted with pinned witnesses, 1 open as a measured parity target), each settled one by two routes sharing no code, plus `kernel_equivalence`, an exhaustive LLVM-APFloat enumerator. Measured: neither z3 4.13.3 nor bitwuzla 0.9.1 can decide any fp8 E5M2 addition query. |
| 2026-08-14 | `a8fac8e57` | Certified infeasibility for operations research: three committed OR instances with measured-irreducible cores (4.9% / 15.6% / 8.3%), leave-one-out re-solves with evaluator model replay, z3 cross-check, and a kernel-checked Farkas refutation of the schedule's critical chain. Four facts. |
| 2026-08-14 | `fb1066709` | The workspace test gate's zero-test list capped and phrased as information (parser validated at 1191 tests / 34 binaries). |
| 2026-08-14 | `23bd018be` | `check.sh` stops claiming to mirror a recipe it does not; the claim was false for the life of the file. |
| 2026-08-14 | `585d4ac23` | Control 6: the step floor itself is exercised (20 controls). |
| 2026-08-14 | `fc1090126` | Frontier curves re-recorded with the machine, load, calibration and comparability that produced them. |
| 2026-08-14 | `4be94e45c` | Controls for the aggregate gate's own scope (18 checks). |
| 2026-08-14 | `952a3ae2b` | Calibration kernel corrected to track the workload (it under-reported the core-class slowdown by 60 %). |
| 2026-08-14 | `1bc24b326` | `progress_frontier` gains a measured reference frame: per-family calibration, scaled budget, `NOT COMPARABLE` / `ADVISORY ONLY`. |
| 2026-08-14 | `ec72fdf66` | `just check` vs `check.sh` divergence measured and pinned; the Lean axiom ledger now runs in both. |
| 2026-08-14 | `fa4676e33` | Clippy and the workspace test sweep prove what they examined; content-addressed source freshness; 14 negative controls. |
| 2026-08-14 | `27d91fa12` | Real-Lean gate: elan toolchain discovery, skips that cannot read as passes, and a counted `scripts/check-lean-gate.sh` in both aggregate gates. |
| 2026-08-14 | `b4604bae7` | The compact Lean writer keeps regenerated-constant spines saturated; `quant_bv_source_instance_set` checks in real Lean and `lean_crosscheck` joins the gate (40 → 112 real-Lean checks). |
| 2026-08-07 | `3576e6739` / `c92155454` / `d09e6debb` | Rejected relevance-activated bound ladders after 0/6 target decisions, exactly repartitioned all 52 A3 budget rows, refreshed the generated CI identity, and integrated the clean pushed evidence branch. |
| 2026-08-07 | `3696e7dd5` | Confirmed repeated size-admission large cores on the selected QF_NIA pair, then rejected bounded four-group deletion after it shrank clauses but decided neither target; temporary solver code was removed. |
| 2026-08-07 | `704318a5f` | Refreshed the complete-parity manifest's sole stale source identity after the pinned-`just` CI workflow change; outcomes, populations, gates, and parity credit are unchanged, and full parity-docs/authority/links pass. |
| 2026-08-07 | `db7b426e8` | Replaced a hidden load-sensitive two-second string/integer coupling deadline with deterministic 128-candidate and 2,000-node ceilings while preserving caller timeouts; the direct budget regression, 14-test fixture, and all-target solver Clippy pass. |
| 2026-08-07 | `7b35dbcb6` / `8bab16429` / `799c5c8c7` | Kept fallible DPLL oracle fixtures explicit and synchronized evidence plus representative Lean expectations with the checked Boolean-simplification route selected after bounded duplicate short-circuiting. |
| 2026-08-07 | `9f94e1873` | Provisioned exact, commit-pinned `just` for both hosted docs gates after three remote runs exposed that the integrated readiness fixtures require the registered executable; the 165-test local resume aggregate passed with one expected skip. |
| 2026-08-07 | `63c82a6ef` / `4ff9a82c6` / `3c5816fdf` | Bounded giant SMT-LIB `distinct` expansion, preserved typed arithmetic reconstruction declines, completed the 67-row A3 census, and rejected zero-gain probe-model reuse without retaining experimental code. |
| 2026-08-07 | `2072483f8` | Retained the bounded disk cleanup while preserving dirty worktrees and every unmerged branch tip. |
Older landed changes (including the 2026-08-06 A1/A2 closure commits) remain
in Git and their dated result notes; this table is deliberately bounded to
changes that still determine the immediate queue.

## Next Actions

Work in this order unless new evidence reveals a wrong verdict, crash, data-loss
risk, or invalid gate. Those are P0 and preempt the queue.

The ordered ten-item programme remains A2 through A11. A1 and A2 are retained
here as closed evidence boundaries. A3 remains incomplete, but all currently
preregistered bounded mechanisms are closed negatively. A4 has now also yielded;
A5 is the first active item.

**Clausal reconstruction lane (`DONE`, agent-h, 2026-08-13).** `DP_POOL_BUDGET`
is not the ceiling; LRAT hint chains bypass that fallback. Compact reconstruction
(`1b2b13c70`) is smaller/faster, scales linearly with hint count, reconstructs
two four-colour cases the inlined route cannot, and introduces no statement or
axiom-footprint mismatch. Nineteen refutations check in Lean 4.30. **Next:**
kernel arena checkpointing, spooling admitted theorems before truncation so
proof size becomes disk-bounded rather than RAM-bounded.

**CAS bridge lane (`DONE`, agent-i, 2026-08-13).** `cas-ideal-refuter`
(ADR-0429, `119858e2c` + `04249ded3`) emits cofactor-tracked ideal identities
that a CAS-free checker re-derives. Six non-polynomial-atom query classes moved
from `unknown` to certified `unsat`; route ordering avoids the measured fast-path
regression. Guard-isolating satisfiable-query forgeries replaced ineffective
tamper cases. **Next:** exact-rational LP over candidate residues instead of
unit-coefficient subset search; see `agent-i-cas-bridge/FEEDBACK.md` F8.

**New lane — certified definite hypergeometric summation (2026-08-14).**
Opened the domain the CAS stack was one step away from: `gosper.rs` decided
*indefinite* summation, and the definite half — Zeilberger's algorithm / creative
telescoping — did not exist as a checkable object. Landed
`crates/axeyum-cas/src/telescoping.rs` (an untrusted linear-algebra search over a
degree-bounded ansatz, minimal recurrence order first, nullspace in
`BigRational`) and `crates/axeyum-cas/src/telescoping_check.rs` (an independent
checker sharing no code with it). Five classical identities proved end to end and
filed as facts:

| identity | order | recurrence | certificate `R` |
|---|---|---|---|
| `∑_k C(n,k) = 2ⁿ` | 1 | `2S(n) − S(n+1) = 0` | `k/(n−k+1)` |
| `∑_k (−1)^k C(n,k) = 0` | **0** | `n·S(n) = 0` | `−k` |
| `∑_k C(n,k)² = C(2n,n)` | 1 | `(4n+2)S(n) − (n+1)S(n+1) = 0` | `k²(3n+3−2k)/(n−k+1)²` |
| `∑_k k·C(n,k) = n·2^{n−1}` | 1 | `(2n+2)S(n) − nS(n+1) = 0` | `(k−1)(n+1)/(n−k+1)` |
| Chu–Vandermonde (recurrence only) | 1 | `(m+n−p)S(p) − (p+1)S(p+1) = 0` | `k(k+n−p)/(p−k+1)` |

The independence is carried by concrete evidence, not by two people writing the
same algebra twice: the checker cross-checks every symbolic shift ratio against
`F` computed from **actual factorials in exact bignum rationals**, then confirms
the pointwise telescoping identity and the summed recurrence the same way. Ten
tamper controls — `P+1`, `2P`, `Q+k`, a wrong recurrence constant, a degree bump
in `a_j`, a zeroed recurrence, a certificate re-pointed at a *different summand*,
a summation window narrower than the support, and two wrong closed forms — are
all rejected.

Schema: added `proof_route: cas-certificate` and `formal.language: cas-term`
(`artifacts/ontology/fact.schema.json`, `scripts/validate-facts.py`). A
telescoping certificate is **not** a `search-certificate`: a replayed witness
settles one finite instance, while an identity in `ℚ(vars)` settles every
instance at once, and their footprints differ in kind. `axiom_footprint` names
the real assumptions, including the one this lane does **not** discharge —
`cas.telescoped-term-natural-boundary`, that `R·F` keeps `F`'s support and
acquires no pole inside it.

Ordered follow-on work:

1. **Degree bounds instead of a degree sweep** (Abramov universal denominator +
   Gosper–Petkovšek normal form). The single biggest win: the search cost is
   dominated by the ladder, not by the linear algebra — Chu–Vandermonde took
   ~250 s on default limits and seconds on tight ones. This also replaces the
   heuristic `Q` ladder, which is where completeness is currently lost.
2. **Symbolic base cases.** Without them every multi-parameter identity stops at
   its recurrence, as Chu–Vandermonde did; with them the whole
   Vandermonde/Gauss/Saalschütz family follows.
3. **A `CasExpr` → `HyperTerm` front door and a committed identity corpus**, so a
   hundred identities are one regression sweep and the existing `prove_wz_sum`
   callers can migrate onto the checkable route.
4. **Serialise `TelescopingCertificate` to `artifacts/`** so an evidence row
   points at the certificate itself rather than at a test that rebuilds it.

Full write-up, including what the fragment does *not* cover:
[`docs/mathematics-2026-08/diary-telescoping.md`](docs/mathematics-2026-08/diary-telescoping.md).

**Continuation lane — took the four ranked follow-ons from lane `telescoping`
(2026-08-14).** All four landed; the first two landed properly, and the honest
limit moved from "the search is a degree sweep" to a much more specific place.

**(1) The degree sweep and the `Q` ladder are gone.** The search now derives what
it used to guess. For each order, `ρ(k) = r(k)·D(k)/D(k+1)` is put into
**Gosper–Petkovšek normal form** `(a/b)·(s(k+1)/s(k))`, which makes Gosper's
criterion the single polynomial equation `a(k)x(k+1) − b(k−1)x(k) = s(k)N(k)` and
hands back the certificate outright as `R = b(k−1)x(k)/(s(k)D(k))`. So the
certificate **denominator is derived** (`s·D`, no ladder), the certificate
**degree in `k` is derived** (Gosper's classical bound), and the recurrence
coefficients are solved for over the **field `ℚ(parameters)`** with no degree
ansatz at all — `Limits::max_recurrence_degree` is deleted, not defaulted. What
was up to 72 linear systems per order is one.

Measured, release build, `examples/telescoping_search_cost.rs` (committed, so the
claim is reproducible):

| identity | before | after |
|---|---|---|
| `∑_k C(n,k)` | 55.7 ms | 1.3 ms |
| `∑_k C(n,k)²` | 137.5 ms | 3.8 ms |
| `∑_k k·C(n,k)` | 40.2 ms | 1.3 ms |
| `∑_k C(m,k)C(n,p−k)`, default limits | **18.5 s** | **46.7 ms** (396×) |
| `∑_k C(n,k)³` (Franel) | **declined after 9.8 s** | **found, order 2, 109 ms** |

The bounds **do** subsume the heuristic: every identity the old engine found, the
new one finds with the same classical recurrence, and the tests assert those
coefficients exactly. `J ≥ 2` came free as predicted.

**(2) Symbolic base cases.** `check_closed_form_symbolic` settles a base case
with the parameters left symbolic: substitute only the shift variable, read the
**forced support** off the `Γ` factors whose argument became parameter-free
(Chu–Vandermonde at `p = 0`: `Γ(k+1)⁻¹` forces `k ≥ 0`, `Γ(−k+1)⁻¹` forces
`k ≤ 0`, support `{0}`), *check* — not assume — that every window point outside
it vanishes, and cancel the symbolic `Γ` powers pairwise. Both sides must reduce
to a rational; a leftover `Γ` is refused as not comparable, never compared by
coefficient. This is what the previous lane called its sharpest gap.

**(4) Certificates are artifacts.** `artifacts/cas-certificates/*.json`, seven of
them, written by a checker-gated emitter and re-checked **from the file** by a
sweep that never calls the search. Fact evidence rows now point at the
certificate instead of at a test that rebuilds it. Hand-rolled deterministic
codec; the crate still depends on nothing but `axeyum-ir` and `num-*`.

**(3) not taken.** The `CasExpr` → `HyperTerm` front door and a surface-syntax
corpus. Depth over breadth; the serialised format covers part of the same need
(a corpus is a directory and one command sweeps it) and gives a parser an obvious
target.

Three new facts (the `cas-certificate` route is now 8; `validate-facts.py` 0 errors):
`F:chu-vandermonde-convolution` (the closed form, symbolic base case),
`F:cross-binomial-row-sum` (`∑_k C(m,k)C(n,k) = C(m+n,n)`),
`F:franel-numbers-recurrence` (the first order-2 certificate on this route). New
axiom named where it is used: `cas.symbolic-gamma-arguments-avoid-poles`.

15 tamper/limit controls now, all rejecting: the previous lane's ten, plus a
symbolic closed form with the wrong base, one with the wrong ratio but the right
base *value*, one leaving an uncancelled `Γ`, a window that does not **strictly**
contain the forced support, and an unbounded support that declines instead of
truncating. The artifact sweep adds its own: an edited numerator, an edited
recurrence coefficient, a certificate re-pointed at a neighbouring file's
summand, and truncated / foreign-format / decimal-bearing files.

**The next honest limit is `MvPoly`'s `i128` coefficients, specifically inside
`MvPoly::gcd`.** Apéry's `∑_k C(n,k)²C(n+k,k)²` declines, and the cause is
measured rather than assumed: the derived degree bound is 2, which is exactly the
degree at which the certificate exists (verified out of tree), so the search
design is not what fails — the primitive-PRS pseudo-remainder overflows `i128` on
the degree-8 shift quotient, already at order 0. The fix is a subresultant PRS or
bignum coefficients in `MvPoly`, both changes to a module the whole crate depends
on. Two smaller limits: `leading_integer_zeros` still declines when the leading
recurrence coefficient mentions more than the shift variable (a Saalschütz-type
identity will hit it), and a symbolic base case needs the support pinned by
parameter-free `Γ` factors.

Full write-up:
[`docs/mathematics-2026-08/diary-telescoping-scale.md`](docs/mathematics-2026-08/diary-telescoping-scale.md).

**New domain, opened 2026-08-14.** The certifier already existed —
`groebner_cert.rs` emits `target = Σ cofactorᵢ·generatorᵢ + remainder`, which is a
Nullstellensatz certificate — so this lane built the two missing halves: a
**coordinatisation front end** (points as symbolic coordinate pairs; collinear,
parallel, perpendicular, equidistant, midpoint, centroid as polynomials) and a
**corpus**. Six theorems certified and filed as facts, two on a measured
frontier, `validate-facts.py` at 0 errors.

**The headline finding is not the expected one.** The brief warned, correctly,
that a mechanised geometry proof silently assuming non-degeneracy is wrong in the
direction that manufactures theorems — so the certifier tries the **empty**
condition set first and records what it consumed, making the question measured
rather than assumed. **Four of six theorems need no side condition at all.**
Concurrency of the altitudes, the theorem whose textbook statement always begins
"in a triangle", is in the universally quantified incidence form the bare identity
`(P−C)·(B−A) + (P−A)·(C−B) + (P−B)·(A−C) = 0`, with constant cofactors `(−1,−1)`,
valid for any four points. Same for the medians. Thales is the single identity
`(A−C)·(B−C) = |C−O|² − |A−O|²` and is true *on* the degeneracy locus, not merely
off it.

The rule the corpus exhibits is sharper than "geometry needs non-degeneracy":
**a side condition is needed exactly when the theorem locates a point the
hypotheses are supposed to pin down; incidence is free, location is not.**
`medians-concurrent` and `centroid-divides-medians` sit adjacent in the corpus and
share their two hypotheses character for character (one shared helper builds
both); only the conclusion differs, and only the second needs a condition.

**Non-degeneracy is explicit, saturated, and broken by a committed
counterexample.** A condition `d ≠ 0` is admitted only via Rabinowitsch — a fresh
variable and the generator `d·z − 1` — so it is visible in the artifact, and
`ideal(h, d·z−1) ∩ ℚ[coords]` is exactly the saturation `(h) : d^∞`, the ideal of
the configurations actually claimed. Both conditions used carry exact rational
counterexamples: `A=(0,0), B=(1,0), C=(2,0), P=(7,0)` satisfies both median
hypotheses (`B` is the midpoint of `CA`, so one becomes vacuous) while `3P.x = 21`
against `A.x+B.x+C.x = 3`; and `A=(0,0), B=(1,0), C=(2,0), D=(5,0)` satisfies both
parallelism hypotheses while the diagonal midpoints are `(1,0)` and `(3,0)`. Two
controls keep these load-bearing: **deleting** a counterexample rejects, and
**replacing** it with a configuration that violates the condition but fails to
break the theorem also rejects.

**Everything is in fully generic coordinates** — every point two free
indeterminates, no WLOG frame anywhere. Frame normalisation would have brought
Euler's line into range and was deliberately not used: it buys the reduction with
an invariance assumption about exactly the degenerate case, which is the wrong
trade in the one domain whose characteristic failure is a hidden hypothesis.

**Evidence.** `artifacts/geometry-certificates/*.json` (six files, 26 kB,
readable), written by a checker-gated emitter and re-checked **from the file** by
a suite that never calls the certifier. `geometry_check.rs` shares no code with
Buchberger and runs five passes: rebuild the saturation generators and compare
them with the ones the cofactors are taken against; expand the identity
symbolically; re-evaluate it at 24 integer points through a different code path;
require every declared condition to carry a nonzero cofactor; replay every
degenerate and generic configuration. The **coordinatisation** — the one
assumption exact arithmetic cannot verify — is attacked from outside by
`tests/geometry_encoding_agreement.rs`, which makes the older concrete
`geometry.rs` decide the same six predicates over 244 integer configurations,
opening with the degenerate shapes; the equidistance row goes through exact surds
in `CasExpr`, a completely different route.

**The frontier, measured.** `rhombus-diagonals-perpendicular` (one extra
quadratic hypothesis beyond the parallelogram) declines after 247–365 s;
`euler-line` returns no verdict in 600 s. Everything in the corpus decides under
250 ms. Instrumenting the probe to ask the same question **without** cofactor
tracking gives the same 4.6 s on the rhombus's empty-condition attempt, so the
expense is the Gröbner basis itself, not the representation carried alongside —
this is **not** the `MvPoly::gcd` wall the `telescoping-scale` lane hit. Stated
honestly: whether the saturated rhombus decline is a tripped ceiling or an `i128`
overflow is **not** established, because `CofactorOutcome::Declined` is one value
for both. The structural suspect is the **pure lexicographic monomial order** this
crate uses everywhere — the worst order for computing a basis, the best for
elimination, and ideal membership needs no elimination.

**Next, ranked.** (1) A degree-reverse-lexicographic order in `groebner.rs` — the
single change most likely to move the frontier, and it helps every consumer of
Gröbner bases in the crate. (2) Split `Declined` into ceiling-vs-overflow, the
same distinction `telescoping-scale` needed for `MvPoly::gcd`. (3) Re-attempt
Euler's line, then Simson's line (16 coordinates), then Pappus (18). (4) A surface
syntax emitting a `GeometryProblem`.

Full write-up:
[`docs/mathematics-2026-08/diary-geometry.md`](docs/mathematics-2026-08/diary-geometry.md).

**Continuation lane — took the shared wall that `telescoping-scale` and
`geometry` both hit in `crates/axeyum-cas/src/mvpoly.rs` (2026-08-14).**

**(1) The multivariate GCD no longer runs in `i128`.** The failure was
*intermediate*, and the reproduction is the whole argument: on Apéry's degree-8
shift quotient the inputs' largest coefficient is **120**, the answer's is **6**,
and the pseudo-remainder sequence between them passes through **4187 bits** —
against the 127 an `i128` numerator holds. So the binding bound was on the
scratch space, not on the question or the answer. `MvPoly::gcd` now converts to
an unbounded-integer ring (`src/mvpoly/big.rs`), runs the same recursive
primitive PRS there with the integer content divided out at **every** step
(4187 bits becomes 76), and converts only the answer back. `MvPoly` itself keeps
its `Copy` `i128` rationals and its checked contract; 163 call sites across two
crates are untouched, and the Gröbner path — which never calls `gcd` — is
unaffected. Chosen over a subresultant PRS because that only makes the growth
polynomial: a large enough input still overflows, and the decline would still be
a fact about `i128` rather than about mathematics.

**(2) Apéry verifies.** `∑_k C(n,k)²·C(n+k,k)²` was the acceptance test; the
search returns **Apéry's own recurrence** — `(n+1)³`, `−(2n+3)(17n²+51n+39)`,
`(n+2)³`, coefficient for coefficient — in 97 ms, and the independent checker
accepts it. Committed as an artifact (`apery-numbers-recurrence.json`,
re-checked from the file by a sweep that never calls the search) and as
`F:apery-numbers-recurrence`; the `cas-certificate` route is now 15 facts,
`validate-facts.py` 0 errors. The fact claims the **recurrence only** — not the
irrationality of `ζ(3)`, which needs the second solution and a growth estimate.

Cost, measured as a real A/B (a `git archive HEAD` snapshot built clean, both
binaries pinned to cores 0–7, best of seven): **1.10–1.26× slower** on the seven
identities that already worked, checker times unchanged, and one identity that
declined now verifies. Reproducible via
`cargo run -p axeyum-cas --release --example telescoping_search_cost`, whose
second table reports peak GCD coefficient width per identity against the 127-bit
line — including what the *old* sequence computed, so "could not have finished"
is a measurement rather than an inference.

**(3) A decline says which kind.** `CofactorOutcome::Declined(DeclineReason)`
splits `ReductionSteps` / `PairIterations` / `BasisSize` / `PolyTerms` from
`Overflow`, with `is_ceiling()` drawing the line that decides whether raising a
budget could help. Every `?` on exact arithmetic in `groebner_cert.rs` goes
through `Budget::arith`, so the attribution is exhaustive rather than a guess.
It propagates to `ProofOutcome::Declined(GeometryDecline)` (which also separates
`UnverifiedWitness` — a refusal, not a resource limit) and into the solver, where
`cas_poly.rs` had been reporting the fixed string "hit a deterministic step
ceiling" for overflows too. Two controls, one per side: a starved budget must
decline as `ReductionSteps`, and reducing `x²` modulo `x − 10³⁰` must decline as
`Overflow` with every budget barely touched.

**(4) Degree-reverse-lex is available and measured, and it moves the geometry
frontier.** `MonomialOrder::{Lex, DegRevLex}` on `groebner_cert::Limits`. On the
corpus that already certifies, `grevlex` is **1.3–2.2× faster** with identical
verdicts and identical cofactor term counts. On the frontier it is not a
constant factor: `rhombus-diagonals-perpendicular` with `{abd-not-collinear}`
**declined after 287.8 s under `lex` and is IN IDEAL in 23.6 s under `grevlex`**,
34 cofactor terms, same ceilings. A frontier theorem is reachable.

And the decline it used to give is now legible: **`ceiling: ReductionSteps`,
not an overflow.** The geometry lane suspected `i128` and recorded that as
unestablished; it is now established, and it is not `i128` — so widening
`MvPoly`'s arithmetic would not have moved that theorem at all.

Defaults stay `Lex` in `geometry_limits()` and `ideal_limits()`, deliberately.
`certify` returns the certificate for the **smallest condition subset that
succeeds**, so a faster order can change *which* non-degeneracy conditions a
certificate uses — and those conditions are hypotheses in the facts'
`formal.statement`. Regenerating six committed certificates under a new order is
a change to what six facts claim, not a re-render, and it belongs to the lane
that curates the geometry corpus. `euler-line` was re-attempted under both
orders and **remains out of reach**: 1200 s each, no verdict on even the empty
condition subset. `grevlex` is a large lever, not a general solvent.

Gates: `cargo test -p axeyum-cas` 598 lib + 38 integration + 147 doc, all green;
the 19 telescoping tamper controls and both geometry non-degeneracy
counterexamples still **reject**; the seven pre-existing certificate artifacts
are byte-identical after the GCD change; `check-fact-evidence-replay.sh`
14/14 on `cas-certificate` (15/15 with Apéry); clippy clean on
`axeyum-cas` and `axeyum-solver` with `-D warnings`.

Full write-up:
[`docs/mathematics-2026-08/diary-mvpoly-bignum.md`](docs/mathematics-2026-08/diary-mvpoly-bignum.md).

**Next for whoever picks this up, in order of payoff:** (a) switch
`geometry_limits()` to `grevlex`, regenerate the six certificates, **check
whether any certificate now uses a smaller condition set** (that is a change to
what the fact claims, and the point of doing it deliberately), and promote
`rhombus-diagonals-perpendicular` off the frontier with a fact of its own —
the measurement says it is reachable; (b) the Gröbner path's `MvPoly` arithmetic
is *not* the bottleneck on the rhombus (measured: `ReductionSteps`), so widen it
only when a run actually reports `Overflow` — which is now readable rather than
inferred; (c) `leading_integer_zeros` still declines when the leading recurrence
coefficient mentions more than the shift variable, which a Saalschütz-type
identity will hit.

**Continuation lane, 2026-08-15.** `mvpoly-bignum` measured that
degree-reverse-lex reaches a frontier theorem and then deliberately left the
default alone, because `certify` returns the certificate for the *smallest
condition subset that succeeds* — so a faster order can change **which
non-degeneracy conditions a certificate uses**, and those conditions are
hypotheses in six proved facts' `formal.statement`. This lane took that decision
with the evidence it requires.

**(1) `geometry_limits()` is now `DegRevLex`, and no fact's claim moved.** The
new `geometry_order_audit` example runs **every** condition subset of every corpus
theorem under both orders, then runs the full `certify` under both and compares
the condition set *and the serialized certificate byte for byte*: **six condition
sets unchanged, zero moved, six certificates byte-identical**. The emitter agrees
independently — after the switch it reported *6 unchanged, 1 written*, the one
being the newly reachable rhombus. Not a byte of existing evidence changed.

**The audit proved something stronger than "nothing moved."** For all six, under
both orders, every subset is **decided** (`in ideal` / `not in ideal`), never
declined. Ideal membership does not depend on the order — only whether a verdict is
reached inside the ceilings does — so once every subset is decided, the reported
condition set is smallest **absolutely**. That discharges the qualifier the
`geometry` lane was careful to attach ("smallest among the subsets the budget
decided"). Had any subset declined, the honest move would have been to leave the
default alone. Scope was kept deliberate: `Limits::fast()` and the solver's
`ideal_limits()` still say `Lex`, because the same audit has not been run on their
corpus.

**(2) `rhombus-diagonals-perpendicular` is promoted — the seventh certified
theorem.** `{}` decided *not in ideal* in 0.9 s and `{abd-not-collinear}` *in
ideal* in 25.0 s (under `lex`: 5.1 s and a `ReductionSteps` decline after
301.8 s), 34 cofactor terms, 8.7 kB certificate, and the cofactor of the
saturation generator is exactly minus the conclusion — the signature Rabinowitsch
shape, verified term-for-term from the committed file. Both subsets are decided
under `grevlex`, so its condition set is absolutely minimal too; under `lex` they
are not, which is why the audit now reports that row as `REACH ONLY` rather than
`MOVED` — one order certifies and the other does not, so the failing order's
condition set is *unknown* rather than different and there is nothing to compare.
Headroom on every ceiling axis is 3–9×: 253 S-pairs of
2 000, basis 23 of 200, widest polynomial 1 678 of 8 000, 15 788 reduction steps
of 50 000. `F:geometry-rhombus-diagonals-perpendicular`, `validate-facts.py` 83
facts / 0 errors.

Non-degeneracy is treated in full, and one control had to be **built** rather than
inherited. The saturation controls ran against `first()` — the alphabetically
first saturated certificate — so a newly promoted theorem would have inherited the
*claim* that its counterexample is load-bearing without inheriting the test; they
now iterate over every saturated certificate and assert there are at least two.
And the "violates the condition but does not break the theorem" control was
sharpened: the pre-existing version substituted a *generic* configuration, which
fails on two counts at once and would pass a checker that only tested one.
`A=(0,0), B=(1,0), C=(2,0), D=(1,0)` is collinear — so the condition genuinely
fails — and the diagonals of both the parallelogram and the rhombus still behave;
the test asserts both halves before tampering. Separately, the fact's SMT-LIB
`formal.statement` was cross-evaluated against the certificate's own polynomials
at 300 random rational configurations (1 500 comparisons, 0 mismatches), because
prose review does not catch a transposed sign.

**(3) `euler-line` stays on the frontier, but is no longer described by a
stopwatch.** "No verdict in 600 s" and "no verdict in 1200 s" name no obstruction.
The new `geometry_obstruction` example runs the reduction under a **ladder** of
S-pair ceilings and reports the new `ReductionStats` at each rung, with the
rhombus — which finishes — as the control:

- **Not width.** At 65 S-pairs the rhombus is carrying a **733**-monomial
  polynomial against `euler-line`'s **477**, and finishes at 1 678. Not an
  overflow either; nothing here reported one, and the rhombus decline was
  `ReductionSteps`. Widening `MvPoly` past `i128` would not move this theorem.
- **It is basis growth and the quadratic backlog it creates.** The rhombus's basis
  **saturates at 23 by pair 65** and its queue drains at pair 253, where it
  completes. `euler-line`'s basis is 33 at pair 65 and still climbing ~1 element
  per 2 pairs; each new element queues a pair against every existing one, so 65
  processed leaves **528** outstanding and the ratio is worsening. The `lex` run
  reached one rung further and states it without needing a comparison: going from
  65 to 129 pairs **tripled** the backlog (1 081 → 3 403), added 36 basis elements
  (47 → 83) and cost **ten times** the wall clock (65.0 s → 635.4 s). The order
  changes the constant, not the shape. Memory is a non-issue throughout: peak RSS
  117 MB against a 6 GB cap.
- **The missing lever is identified *and* shown to be insufficient.** This
  `Buchberger` loop applies **no criteria**: on the completed rhombus run **234 of
  253 pairs (92%) reduced to zero** and taught the basis nothing. But the coprime
  counter says the product criterion would skip only 46% of them (28% on
  `euler-line`) — a constant factor under two. The quantity that must change is
  the **basis size**, since the pair count is quadratic in it, and no pair-skipping
  criterion makes a Gröbner basis smaller.

Frame normalisation is still refused, for the `geometry` lane's original reason:
its invariance assumption is an assumption *about the degenerate case*. Everything
stays in fully generic coordinates. Simson (16 coordinates) and Pappus (18) were
gated on `euler-line` and not attempted — a 16-coordinate attempt on a route whose
10-coordinate case diverges produces a longer timeout, not information.
`euler-line` remains **unproved rather than unchecked**, and that half was
strengthened rather than left alone: the corpus now constructs its circumcentre
and orthocentre **exactly** (Cramer's rule over the rationals) for eight triangles
— obtuse, right, isosceles, generic — and asserts on each that the hypotheses
vanish, the condition does not, and the conclusion holds. Not a proof; a guard
against a mis-transcribed predicate sitting unnoticed because no search ever got
far enough to reject it. Its self-control had to be fixed rather than written: the
first version perturbed `O` by one unit in `x` and demanded the conclusion break,
and **failed on the first triangle**, whose Euler line is horizontal — a step
along `x` slides `O` along the line. It now tries both axes and requires one to
break, which a line can never satisfy vacuously.

Full write-up:
[`docs/mathematics-2026-08/diary-geometry-frontier.md`](docs/mathematics-2026-08/diary-geometry-frontier.md).

**Next, ranked.** (1) Buchberger's criteria in `groebner_cert.rs` — product first
(four lines, 28–46% of pairs *by measurement*), then chain; worth it for the whole
crate, and it will **not** by itself reach `euler-line`, which is why the counters
are committed. (2) Audit and switch `Limits::fast()` / `ideal_limits()` the same
way: measure first, flip second. (3) `euler-line` needs an algorithm, not a knob —
F4-style linear algebra over the S-pair matrix, or exploiting that all four of its
hypotheses are **linear in the four unknown coordinates** over `ℚ[ax..cy]`, so the
natural derivation is Cramer's rule over that coefficient ring and Buchberger is
being asked to rediscover it by monomial reduction. (4) Simson and Pappus remain
gated on (3). (5) A surface syntax for the corpus, still open.

**Immediate action (`PAUSED`, Lean lane).** ADR-0452 focused-green; full gate hit
concurrent scoreboard drift. Await refactor. No Gauss credit.
Keep the 14-theorem export labelled rejected by Lean and independently unchecked.
A5 V2 QF_RDL row 1 remains pending and uncredited.

**Continuation lane, 2026-08-15.** `geometry-frontier` measured that `euler-line`
does not fail on width, memory or arithmetic — it *diverges*: the basis never
saturates and the S-pair queue is quadratic in it, so 65 pairs processed leaves
528 queued and the next rung was killed after 27 minutes. It left a structural
observation it did not act on: all four hypotheses are **affine in the four
unknowns** `ox, oy, hx, hy` over `ℚ[ax..cy]`, so Buchberger was being asked to
rediscover Cramer's rule by monomial reduction. This lane acted on it.

**`euler-line` is the eighth certified theorem, and `frontier()` is empty.**
Certified in **4–6 ms** with **0 S-pairs, 0 basis, and a residue of exactly zero**,
against a Gröbner run that had not returned in 27 minutes on the same ladder
(reproduced on this box: 65 pairs / 528 queued / basis 33 / 15.9 s, matching the
recorded 15.8 s). `F:geometry-euler-line`, `validate-facts.py` 98 facts / 0
errors, `cas-certificate` 17 facts.

**The certificate stays in the original generators, which was the actual
requirement.** `crates/axeyum-cas/src/linear_elim.rs` does not substitute solved
forms; it uses the adjugate identity `adj(M)·(M·u + k) = det(M)·u + adj(M)·k` to
express `det(M)·uⱼ` as a polynomial free of the unknowns **plus a combination of
the original rows**, so every cofactor is against a hypothesis the problem stated.
The `det(M)^d` multiplier is then divided out **through the Rabinowitsch
generator** rather than symbolically: `1 = zᴺdᴺ − g·Σ C(N,i)g^{i−1}`. `euler-line`
has `N = 2` (its multiplier is `4·collinear(A,B,C)²`, a power of its own
non-degeneracy condition), so the saturation cofactor is
`−conclusion·(1 + collinear(A,B,C)·Zinv0)` — the `N = 1` case is the familiar
minus-the-conclusion shape of the six older certificates, and the exact polynomial
is asserted term-for-term. **`geometry_check.rs` is untouched**; it knows about
neither route, and its shape pass compares each generator against the stated
hypothesis, so a solved-form substitution would be rejected there. The emitter
agrees independently: **7 unchanged, 1 written**.

**A multiplier the stated conditions do not license is a refusal, not a licence.**
`GeometryDecline::UndividableMultiplier`. This is the soundness-relevant half and
it is tested against Thales, where the elimination *does* clear the residue but
with a two-term multiplier that is nobody's declared condition. Six of the seven
older theorems decline for exactly that reason — the block detector eliminates
*vertex* coordinates there, so its determinant is an artifact rather than the
geometric condition. `euler-line` is different because its unknowns are
constructed points. `certify_any_route` therefore runs **linear first, then
Gröbner** (with Gröbner first, `euler-line` never reaches the cheap route), and
that order was checked rather than argued.

**Minimality is ABSOLUTE, established by a cheaper and stronger instrument than
the `2ⁿ` audit (ADR-0455).** `geometry_order_audit` cannot apply here — the whole
point is that the Gröbner reduction does not return — and the linear route cannot
substitute for it, since its multiplier is an artifact of the decomposition. So:
if `c` lay in the ideal of the hypotheses plus `d·z − 1` for `d ∈ S`, it would
vanish at every common zero; a configuration satisfying every hypothesis, keeping
every condition of `S` nonzero and **falsifying** a conclusion refutes `S`
outright — no budget, no monomial order, no algorithm. The committed degenerate
counterexample *is* such a configuration, so the ledger already held the proof and
had not read it as one. `every_used_condition_set_is_minimal_absolutely` states it
for arbitrary subsets: **4 proper subsets refuted across 4 saturated certificates,
0 undecided** (each uses one condition, so each has one proper subset), with the
count asserted against that arithmetic rather than hand-written.

**Non-degeneracy in full, and one control that had silently stopped applying.**
Counterexample: `A = B = (0,0)`, `C = (1,0)`, `O = (1/2,0)`, `H = (0,1)` — every
hypothesis holds, the condition vanishes, `O`, `G = (1/3,0)`, `H` form a triangle.
On-locus-but-harmless: the same configuration with **`H = (0,0)`**, one coordinate
away, which violates the condition just as thoroughly and leaves `O`, `G`, `H`
collinear on the x-axis; offering it as the counterexample is rejected. That
control was written for the quadrilateral coordinatisation and therefore *skipped*
every triangle theorem, `centroid-divides-medians` included, since the day it
landed. It is now a table keyed by coordinatisation with a **full-coverage
assertion**, so the next promotion fails loudly rather than opting out. The fact's
SMT-LIB `formal.statement` was cross-evaluated against the certificate's own
polynomials at 400 random rational configurations (2 400 comparisons, 0
mismatches), with a control confirming a one-unit coefficient perturbation is
detected.

Full write-up:
[`docs/mathematics-2026-08/diary-euler-linearity.md`](docs/mathematics-2026-08/diary-euler-linearity.md).

**Pappus is certified and deliberately unfiled, which is the session's second
finding.** `pappus-hexagon` is stated on `frontier()` with its witnesses replayed:
18 coordinates, 8 hypotheses, **three 2×2 blocks** whose determinants are exactly
its three non-degeneracy conditions, a 468-term multiplier, a 720-term residue
that reduces in **one S-pair** against the two hypotheses the blocks did not
consume — and a certificate the independent checker **accepts** (292 s, 3583
cofactor terms). It took two narrowings to get there, and both are the point
rather than tuning: reducing the residue against all eight hypotheses (six already
consumed, every one mentioning a variable the residue no longer has) does not
return, and adding the three Rabinowitsch generators to that reduction does not
either — so the handover is now unconsumed *hypotheses* first, unconsumed
*generators* only if that fails, because the saturations are what the **multiplier**
needs, not the residue. The emitter reports **0 written, 8 unchanged** afterwards.

What holds it on the frontier is not reach, it is **counterexamples**. Pappus has
one for the condition set as a whole (six points on the x-axis; every incidence
hypothesis vacuous; X, Y, Z free to be a triangle) and this lane found none
isolating a *single* condition — three attempts, each collapsing differently,
all because killing one intersection forces the two other constructed points onto
the very line the freed point is confined to. Its minimality would therefore be
**budget-relative** in ADR-0455's sense, and
`every_used_condition_set_is_minimal_absolutely` refuses that. **The ratchet this
lane added blocked the very next theorem**, which is the strongest evidence
available that it is set where it should be.

**Next, ranked.** (1) **Decide about Pappus** — isolate a single condition with a
rational configuration (or find a smaller condition set), or relax the ratchet to a
named justified exception and write a budget-relative fact, which ADR-0455 permits
when warranted. Highest value because the computation is already done and what
remains is a decision about the ledger's honesty rules. (2) **Simson**, whose
algebra is *easier* than Pappus's (14 coordinates, three 2×2 blocks, residue modulo
a single generator) and whose real cost is that `|BC|² ≠ 0` is **not** `B ≠ C` over
an arbitrary characteristic-zero field — so the witnesses that would necessitate it
are not rational, and `DegenerateWitness` holds exact rationals. (3) Buchberger's
criteria in `groebner_cert.rs` — still worth it for the whole crate, still not what
reaches a divergent theorem. (4) Teach the block detector to prefer determinants
that divide a **declared** condition; six of eight corpus theorems decline on a
badly-chosen multiplier and the information to choose better is in the problem.
Reach, not soundness. (5) Audit and switch `Limits::fast()` / `ideal_limits()`.
(6) A surface syntax for the corpus, open and recommended three times now.

**Continuation lane, 2026-08-15.** `euler-linearity` left `pappus-hexagon`
certified, checker-verified, and deliberately **unfiled**: 292 s, three
non-degeneracy conditions, and a note saying the three "can only be necessitated
as a set", so its minimality would be budget-relative and
`every_used_condition_set_is_minimal_absolutely` refused it. The brief was to
decide that question rather than route around it. The answer is that the premise
was false.

**Pappus's three conditions are not needed as a set. Each one suffices on its
own.** The three-condition set was not "minimal but unprovably so" — it was **not
minimal**. `pappus-hexagon` is the ninth certified theorem, in `corpus()`, with
**one** condition, certified in **6.7 ms** against the previous 292 s, and its
minimality is **absolute**: the only proper subset of a singleton is the empty
one, and the counterexample the previous lane already committed refutes it.
`F:geometry-pappus-hexagon`, `validate-facts.py` 99 facts / 0 errors,
`cas-certificate` 18 facts.

**The previous lane had the proof and read its sign backwards.** Its three
attempts to isolate one condition collapsed, always because "killing one
intersection forces the two other constructed points onto the very line the freed
point is confined to" — recorded as an obstruction to *claiming* minimality. It is
a **proof of redundancy**. The hypotheses assert that `X`, `Y`, `Z` *exist* on
their line pairs, so a degenerate line pair does not lose its point, it frees it
along a line — and every way that can happen drags the other two cross points onto
that same line. It does not run for all three at once, which is why the empty set
is still refuted and one condition is still needed.

**Why the route said three, which is the transferable part (ADR-0460).** Not a
budget. `detect_linear_blocks` picks its decomposition from the shape of the
generators, so the multiplier was always `c₁·c₂·c₃` and every proper subset failed
at `invert_multiplier` — **decisively**, since exact division always answers. Under
ADR-0455's dichotomy that reads as the *absolute* regime, and the route's own doc
comment said exactly that. The decided test was "can this subset divide **that**
multiplier?", which is a question about a producer-side choice, not about the
theorem. **Decidedness is necessary and not sufficient.** ADR-0460 refines
ADR-0455 with a third regime — *representation-relative*: every test decided,
against a fixed representation, therefore reporting as absolute while being wrong,
and no amount of patience discovers it. The remedy is preferred to the disclosure:
`licensed_blocks` admits a block only when its determinant is a nonzero rational
times a product of powers of the conditions **currently being inverted**, so the
subset chooses the decomposition instead of inheriting it.

**`cofactor_ansatz`: bounded-degree ideal membership by exact sparse linear
algebra.** With one block licensed the elimination leaves a 48-term degree-4
residue over six untouched hypotheses. Buchberger was **killed at 7.5 minutes without returning**;
the new module settles it at cofactor degree 2 in ~25 ms with every coefficient
`±1`. It is incomplete on purpose — `NotInDegree(d)` is a *decided* statement about
a degree slice and says nothing about the ideal — its limits bound the shape of the
system and never the solve, and it re-expands its own answer before returning it.
It is tried before Buchberger in the handover, and that ordering is load-bearing:
second, the subset search never reaches the answer.

**Nothing committed changed.** `geometry_check.rs` untouched — it has now not
changed across three different producers (Buchberger, adjugate elimination, a
Macaulay-style solve), which is the property the design rests on. Enabling the
handover in `certify_any_route` was necessary and would otherwise have turned the
linear route into a second general-purpose prover on theorems whose conclusion is
in the plain hypothesis ideal, so the handover refuses to run when the elimination
consumed **no block**. `emit_geometry_certificates`: **8 unchanged, 1 written**.

**Evidence, ascending in strength.** (1) A synthetic case analysis over the strata
where a cross point is under-determined. (2) `pappus_condition_subsets` decides the
question exhaustively over `F_p` for `p = 5, 7, 11, 13, 17, 19, 23` — reading the
polynomials **out of the committed corpus** and reducing them mod `p`, over every
carrier pair up to the affine group and every solution including the
positive-dimensional ones — and finds exactly one refuting pattern, the all-zero
one; the orbit reduction is itself checked against a full enumeration at `p = 5`.
(3) `each_pappus_condition_alone_certifies` demands a **certificate** for each of
the three conditions in isolation; all three certify at cofactor degree 2. A
certificate is a polynomial identity, so that is the statement about ℚ the sweep
only suggested.

**One bug worth recording.** `factors_into` loops forever on the zero polynomial —
`exact_div(0, d)` is `Some(0)` for every `d`. It cannot arise from a block
determinant, and "cannot arise" is exactly the reasoning that leaves a loop
unguarded; the unit test written to exercise the licensing rule *directly* rather
than only through a theorem hung the suite and found it.

Full write-up:
[`docs/mathematics-2026-08/diary-pappus-minimality.md`](docs/mathematics-2026-08/diary-pappus-minimality.md).

**The shared index is not made safe by discipline, in either direction.** Two
lanes hit the same race inside twelve minutes, once each way. `c391b36d4`
(`lra-dispatch`) carries one line of `docs/reference/examples.md` that is this
lane's, because `git commit -- <pathspec>` commits the *worktree* content of
those paths and discards the hunk they had carefully staged with
`git apply --cached`. `1725615688` (`lra-dispatch`) then carries five files that
are this lane's — `cofactor_ansatz.rs`, `geometry_probe.rs`,
`F-geometry-pappus-hexagon.json`, `diary-pappus-minimality.md` and one
`examples.md` row — because the remedy for the first failure, a bare
`git commit` after confirming `git diff --cached --numstat`, takes whatever is in
the index at commit time, and this lane had staged into it between their check
and their commit. Both were disclosed rather than rewritten; nothing is lost in
either direction, and the content of both is exactly as written.

The rule that follows is not a better incantation. `git commit -- <paths>` reads
the worktree and defeats index-level hunk staging; bare `git commit` reads the
index and is defeated by any concurrent `git add`. **There is no form of the
command that is safe for two lanes sharing one index**, which is the same lesson
CLAUDE.md draws for per-lane state files, arriving one level down: the index is
per-checkout state that every lane writes. What actually works is a worktree per
lane, or not sharing the file.

**Simson, answered rather than restated.** The brief asked whether
`geometry.characteristic-zero-specialisation` licenses the real-plane reading of
`|BC|² ≠ 0`. It does not, and the reason is sharper than "the witnesses are
irrational": the *certificate* is fine over every characteristic-zero field, and
it is the **minimality** side where the readings come apart, in opposite
directions. Over ℂ the isotropic directions make `|BC|² = 0` possible with
`B ≠ C`, so the condition may be genuinely necessary — and `DegenerateWitness`
holds exact rationals, so we could not state the witness. Over ℝ, `|BC|² = 0` is
`B = C` and nothing else, and if that forces the conclusion (the same shape as
Pappus) then the condition is **redundant over ℝ** and ADR-0460 forbids filing it.
These are two different theorems and the footprint entry currently papers over the
difference. Simson is deliberately **not** stated on `frontier()`: the missing
piece is a decision about which field the fact is over, not a `GeometryProblem`.
`frontier()` is empty, and `every_frontier_witness_is_consistent` says so out loud
rather than silently examining nothing.

**Next, ranked.** (1) **Simson** — decide the field first, then the algebra;
a rational configuration is an hour's work (`A=(5,0)`, `B=(0,5)`, `C=(−3,4)`,
`P=(4,−3)` on `x²+y²=25`, concyclicity as the 4×4 determinant, feet `(6/5,27/5)`,
`(27/5,−1/5)`, `(6,−1)`, verified collinear). (2) **Teach
`detect_linear_blocks` to prefer determinants a declared condition divides** —
now half-done, since the filter *rejects* unlicensed blocks but the detector still
proposes them; reach, not soundness. (3) **Raise
`AnsatzLimits::geometry().max_cofactor_degree`** and measure where the corpus's
residues stop falling to it. (4) **The `fact.schema.json` minimality field**, on
its third instance now, and the argument for deferring is thinner because the
wrong value here would have been the *strong* one. (5) Buchberger's criteria in
`groebner_cert.rs`, unchanged in priority from the last two lanes' lists.

**Lane state (`WIP`, int-keystone, 2026-08-14).** ℤ is now *constructed*, not
asserted: `Int` is an inductive over `Nat` (`Int.ofNat` / `Int.negSucc`), every
operation is a checked definition, and `integer` went **34 axioms → 6**
(`opaque=0 quotient=0` throughout). 20 laws are theorems with an **empty**
`Kernel::axiom_footprint`, including the headline `Int.no_int_between` —
discreteness, which the integer-cut route previously assumed — and `Int.eq_em`,
ADR-0106's decidable integer equality, which is now derived from constructor
injectivity and discrimination plus `Nat.beq` rather than assumed. Controls held:
`nat_theorem_inventory` still prints 119 theorems with byte-identical types and
`nat: axiom=0 opaque=0 quotient=0`. Five integer facts landed in
`artifacts/facts/`, the first this ledger has carried.

Next is the `Int.subNatNat` **borrow** sub-development
(`subNatNat m n = subNatNat (m+k) (n+k)`, and a characterization of when it
returns `ofNat`). That single missing piece is the blocker on four of the six
remaining: `add_assoc`, `left_distrib`, `add_le_add` and
`add_lt_add_of_le_of_lt`. `mul_assoc` needs the sign bookkeeping of
`negOfNat (m*n)` across eight branches. Hardest and last:
`euclidean_decomposition`, which needs integer division.

Unchecked and flagged rather than assumed: **no independent Lean binary read the
exported module.** No `lean` is installed here, so
`diophantine_module_checks_in_real_lean` and its siblings take the skip path and
report `ok`. The module grew 1,004,665 → 1,047,668 bytes because `Int` is now an
inductive and now carries proof terms for the derived laws. Anyone with Lean
should run those suites with `AXEYUM_REQUIRE_LEAN=1`.

Cost recorded: `build_int_prelude` now builds the `Nat` prelude first, so
`IntReconstructCtx::new` is ~52 ms slower per fresh context. Splitting `Nat` so
`Int` pulls only arithmetic and order (not gcd/Bézout) would recover most of it.

Full reasoning, including why the setoid quotient of ℕ×ℕ loses in this kernel:
[`docs/mathematics-2026-08/diary-int-keystone.md`](docs/mathematics-2026-08/diary-int-keystone.md).

**Lane state (`WIP`, int-remainder, 2026-08-15).** `integer` went **6 axioms →
1**. `Int.add_assoc`, `Int.mul_assoc`, `Int.left_distrib`, `Int.add_le_add` and
`Int.add_lt_add_of_le_of_lt` are theorems; only
`Int.euclidean_decomposition` is still asserted. `int_theorem_inventory` reports
**50 derived, 50 with an EMPTY `axiom_footprint`, 1 still asserted**.

The blocker the previous lane named was real and was one obstruction, not four:
`Int.subNatNat` is a `Nat.rec` on `n − m`, stuck whenever its arguments are
variables, and every mixed-sign branch of `Int.add` is one. The development that
unblocks it is three steps — the shift lemma
`subNatNat (m+k) (n+k) = subNatNat m n` (induction on `k` over two rewrites by
`Nat.succ_sub_succ`, one for the value and one for the scrutinee, which sit in
different holes); the anchors `subNatNat m 0 = ofNat m` and
`subNatNat 0 k = negOfNat k`, whose shifts are the two characterisations; and
`Int.subNatNat_elim`, which turns `Nat.le_total` + `Nat.le_dest` into a
two-branch case analysis on which constructor the borrow lands in. 25 reusable
lemmas, all with empty footprints.

Two findings worth carrying. `mul_assoc` never needed the borrow at all — it is
blocked by a stuck `negOfNat` under `Int.mul`, which four two-case lemmas
unstick, and then it is eight branches of `Nat.mul_assoc`. And the two additive
**order** laws are proved with **no `Int.rec` in the proof term**: `le a b` iff
`b = a + ofNat i` (`Int.le_dest` / `Int.le_ofNat_add`), so sixteen structural
branches over a stuck `Int.add` become one ring rearrangement over `add_assoc`.
Replacing a case-defined relation by its witness is the transferable move.

Controls held. `nat_theorem_inventory` is **byte-identical**: 119 theorems, diff
clean, `nat: axiom=0 opaque=0 quotient=0`. `cargo test -p axeyum-lean-kernel`
green (249 lib + every integration suite); clippy `-D warnings` clean. **A real
Lean 4.30.0 kernel read the grown export** — the thing the previous lane flagged
as not done: `scripts/check-lean-gate.sh` reports `12 suites, 49 tests, 112
real-Lean checks (floor 105)`, green. The Diophantine golden module hash moved
(1,049,867 → 1,142,494 bytes) and was updated by a script that parses the value
the failing test printed, because the previous lane got that constant wrong by
typing it. Seven integer facts landed and replay: `kernel-lean 30/30 re-derived`
under `check-fact-evidence-replay.sh`.

`tests/axiom_footprint.rs` had built its composite witness out of
`Int.add_assoc` and `Int.mul_assoc`; both are theorems now, so an integer-only
composite is no longer constructible and that suite reaches into `arith` to keep
testing an exact closure rather than "return the root and stop".

Next: `Int.euclidean_decomposition` is a **different kind of problem** and is why
this lane stopped. Every law discharged here is an equation or inequality between
terms already in the language, so the work was making definitions reduce. This
one asserts the existence of two integers the language cannot name, so it needs
`Int.div`/`Int.mod` defined and specified — a new definition with its own
recursion, not another rewriting lemma. The `Nat` side already has
`div_mod_exists`, `div_mod_unique`, `mod_lt` and a certified executable
`Nat.divMod`; the interesting case is negative dividends, where Euclidean
rounding is not truncation and the sign convention must be defended by the
`0 ≤ r < k` bound rather than assumed. `Int.le_dest` and `Int.subNatNat_elim`
are both directly useful there.

Full reasoning, including the three `symm`-direction bugs and why `ExprId`s in
kernel errors cost more than the proofs did:
[`docs/mathematics-2026-08/diary-int-remainder.md`](docs/mathematics-2026-08/diary-int-remainder.md).

**Lane state (`WIP`, real-keystone, 2026-08-15).** The strand item said ℝ was the
whole of the remaining keystone — 30 axioms, 0 derived theorems. Two
measurements taken before writing code changed what the item is.

**1. The `Real` prelude is not an axiomatization of ℝ.** Enumerated rather than
read off the module's own "axiomatized linear ordered field" summary: 8 carrier
and operation declarations, 22 laws, and **no `inv`, no `div`, no completeness,
no Archimedean, no density, not even totality**. It is an **ordered commutative
ring with 1**. Nothing in it distinguishes ℝ from ℚ, and every one of the 22 laws
is true of ℤ. The carrier's *name* was doing the work its axioms were not, and
the strand item inherited that reading.

**2. `Quot.sound` does not exist in this kernel.** `quotient.rs` admits a package
of `PACKAGE_LEN = 4` — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — pinned by
`canonical_package_admits_exactly_four_and_is_idempotent`, and no prelude calls
`add_quotient_package` at all. Without `Quot.sound` nothing proves two `Quot.mk`s
equal, so **a Cauchy-sequence ℝ is not expensive here, it is inexpressible**.
Three comments and the ℤ diary say otherwise (that a quotient would merely put
`Quot.sound` in every footprint); they describe Lean's package, not ours. All
three corrected, and the measurement is now a test.

**What landed instead of a construction.** `build_int_model_of_arith`
(`src/arith_model.rs`) computes each `Real` law's type with the eight
carrier/operation constants substituted — from the environment, never typed by
hand — and admits a theorem of that type proved by the corresponding `Int`
theorem, kernel-checked at admission:

```
Real: 30 trusted declarations = 8 interpreted symbols + 22 modelled laws;
22/22 witnesses have an EMPTY axiom footprint,
22/22 are syntactically the Int law
```

21 were already ℤ theorems. The 22nd, **`Int.sq_nonneg`**, is proved here:
`int_theorem_inventory` goes **50 → 51 derived, all 51 with an empty footprint**,
1 still asserted (`euclidean_decomposition`, untouched). The `identical` column
is stronger than admission — the substituted `Real` axiom is the *same interned
term* as the `Int` law in all 22 cases, two preludes written months apart
agreeing to the term.

**Stated narrowly, because it is easy to overclaim.** This is **relative
consistency**: the `Real` axiom set has a model whose theory is derived from
nothing, so no Farkas/SOS reconstruction is vacuous on account of a
contradictory package — a real, previously unmeasured risk, since a
contradictory package makes every reconstruction "valid" while every gate stays
green. It is **not** a discharge: `real: axiom=30` is unchanged and untouched,
ℤ is not ℝ, and the step from "every axiom translates" to "every derivation
translates" is a homomorphism argument the kernel cannot state.

**Controls held.** `nat_theorem_inventory` **byte-identical** (119 theorems, diff
clean); `nat_axiom_inventory` unchanged at `logic 0, nat 0, real 30, integer 1,
string 1`; `cargo test -p axeyum-lean-kernel` green (255 lib tests, 249 + 6 new,
plus every integration suite); clippy `-D warnings` and
`RUSTDOCFLAGS="-D warnings" cargo doc` clean;
`scripts/check-lean-gate.sh` green and **unchanged at 12 suites, 49 tests, 112
real-Lean checks (floor 105)** — no golden module hash moved, because
`Int.sq_nonneg` is not reachable from any export root. `validate-facts.py`: 96
facts, 0 errors.

**Next, and the trigger is named rather than guessed.** ℚ is the right carrier
for LRA — real and rational satisfiability coincide for linear systems with
rational coefficients — and it *is* quotient-free constructible (`Int` numerator,
`Nat` denominator, normalized by `Nat.gcd`, which sidesteps
`euclidean_decomposition` entirely). It is not built because **no axiom in the
package asks for it**. Build it when a `Real` axiom mentioning `inv`, `div`, a
supremum or Archimedean-ness is proposed;
`the_real_package_has_no_inverse_completeness_or_archimedean_axiom` fails on that
day. The crux lemma is recorded so the next lane does not rediscover it:
`normalize` must be a function of the cross-multiplication class
(`a·d = c·b ⊢ normalize (a,b) = normalize (c,d)`), the ℚ analogue of
`subNatNat`'s borrow.

**The route that actually eliminates the 30 is not constructing ℝ.** Parameterise
`axeyum-solver/src/reconstruct/arithmetic.rs` over the ordered-ring interface, so
a Farkas refutation becomes `∀ (R : Type) …, <the 22 laws> → <refutation>` — an
empty-footprint theorem *stronger* than today's `Real`-specific statement, which
recovers it by instantiation. That makes the 30 axioms unnecessary rather than
proved, and it is a solver change, not a kernel one.

Full reasoning: [ADR-0456](docs/research/09-decisions/adr-0456-real-is-an-ordered-ring-modelled-by-int.md)
and [`docs/mathematics-2026-08/diary-real-keystone.md`](docs/mathematics-2026-08/diary-real-keystone.md).

**Lane state (`DONE`, ordered-ring-reconstruct, 2026-08-15).** ADR-0456 measured
that the `Real` package is an **ordered commutative ring with 1** and named the
route that eliminates its 30 axioms without constructing a carrier: parameterise
the consumer, not build a model. That route is now built and measured
(ADR-0457, [`diary-ordered-ring-reconstruct.md`](docs/mathematics-2026-08/diary-ordered-ring-reconstruct.md)).

`generalize_over_ordered_ring`
(`crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs`) λ-abstracts
the 30 `Real` declarations, the per-variable constants and the per-constraint
hypothesis axioms out of a finished, kernel-gated proof term, in dependency
order, with every binder type computed from the environment. The kernel then
infers the statement:

```
∀ (R : Sort 1) (add mul : R → R → R) (neg : R → R) (zero one : R)
  (le lt : R → R → Prop), <the 22 laws> →
  ∀ (x0 : R), le (add x0 zero) zero → le (add (neg x0) (add one zero)) zero → False
```

**Measured `axiom_footprint`: empty**, on all five fixtures (three Farkas shapes,
a strict cycle, a sum-of-squares). The un-generalized theorem's footprint is
printed beside it on the same run — 18, 22, 24, 7, 10 — so the zero
discriminates. **Real Lean 4.30.0 agrees**: the committed fixture
`arithmetic-ordered-ring-farkas.lean` declares no `axiom` at all and Lean answers
`'axeyum_ordered_ring_refutation' does not depend on any axioms`.
`check-lean-gate.sh` goes **112 → 113** real-Lean checks (floor 105 unchanged).

**Nothing is lost.** Instantiating at `Real` — applying the theorem to the 30
constants and the refutation's own variable/hypothesis axioms — is a term the
kernel accepts against `False`, recovering the original statement with its
original trusted base; under the tight telescope the recovered footprint is
identical name for name. Recorded as `F:ordered-ring-farkas-refutation`, route
`kernel-lean`, `axiom_footprint: []` (`validate-facts.py`: kernel-lean 31 → 32,
axiom-free 30 → 31).

**`real: axiom=30` is untouched, deliberately** — reducing the trusted base was
never the goal. What changed is that no reconstructed refutation *depends* on it;
the 30 are now used only to instantiate. Of the 30, 21 are reached by at least
one fixture; the nine never reached are `le_trans`,
`mul_le_mul_of_nonneg_left`, `add_lt_add_of_le_of_lt`, `mul_comm`, `mul_assoc`,
`mul_one`, `mul_zero`, `left_distrib`, `mul_nonneg`.

**Next, for whoever picks this up.** (1) Fix the facade dispatch so an SMT-LIB
QF_LRA `unsat` reaches `ProofFragment::Lra` instead of the contentless `LraDpll`
shim — generalizing the shim would produce an axiom-free theorem that says
nothing, so the entry point is still the direct reconstructor. (2) Try the 5 MB
schedule-deadline core through the generalization and find out what it costs;
this lane did not, and does not imply it works. (3) The hypothesis-footprint gap
is still open: the binders are visible in the statement now, but nothing checks
that they are the rows they claim to be.

**Lane state (`DONE`, lra-dispatch, 2026-08-15).** Two lanes had measured that
`prove_unsat_to_lean_module` routed a pure-`Real` conjunctive `QF_LRA` `unsat`
through `ProofFragment::LraDpll`, whose Lean module is a 21-line structural shim
(`axiom P`, `axiom Not P`, apply) that kernel-checks, is `sorry`-free, and
contains no arithmetic — and that `ProofFragment::Lra`, the genuine Farkas
reconstructor, had **no test anywhere asserting a query reaches it**. Both are
now fixed, and the second half — a contentless module passing as a proof — was
the larger of the two, because **29** routes share that emitter.
(ADR-0458,
[`diary-lra-dispatch.md`](docs/refactor-2026-08/diary-lra-dispatch.md))

**Dispatch.** `scan_arithmetic_proof_fragment` tries a new
`lra_farkas_reconstruction_certifies` arm *before* the lazy-SMT arm. Its
predicate is two gates: a self-checked `lra_farkas_certificate`, then the
**reconstruction itself building and the kernel inferring it to `False`**. The
second gate means the reordering can only move a query from "shim" to
"arithmetic", never to "declined" — a certificate shape the reconstructor does
not cover keeps falling through to `LraDpll`. `lra_term_infers_false` is now
shared by the classifier and `gate_and_render_lra_module`, so the check that
routes a query is the check that later accepts it.

**Measured:** `x < 0 ∧ 0 ≤ x` and `x+y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y` reach
`ProofFragment::Lra` through both `scan_proof_fragment` and the front door, and
the emitted module carries `Real.add_le_add`, `Real.lt_irrefl`, one
`lra.hyp._N` per asserted row and one `lra.x._N` per variable. Seven new lib
tests; three existing `LraDpll` assertions flipped to `Lra`. The two cvc5
`QF_LRA` audit rows stay on `LraDpll` (genuinely Boolean-structured), so
`check-lean-gate.sh` is unchanged at 113.

**The shim: kept, marked, and excluded from the honest entry point.** Removing it
was not defensible — it is load-bearing for 29 routes and for those the Rust
certificate genuinely is the evidence. Four changes instead: every attestation
module opens with `-- axeyum-lean-module-content: structural-attestation` and a
warning naming its refuter; `LeanModuleContent` + `ProofFragment::lean_module_content()`
type it in an exhaustive match; `gate_module_content` cross-checks the table
against the rendered artifact on **every** call and refuses a mismatch
(`ReconstructError::ModuleContentMismatch`); and `prove_unsat_to_lean_theory_module`
returns a typed `ReconstructError::NoTheoryContent` decline instead of a module
with nothing in it. `axeyum_property::LeanModule` gained `content()` /
`theory_source()` and `LeanSummary` a `content` field.

**Honest residual:** `prove_unsat_to_lean_module` keeps `(ProofFragment, String)`
— 199 in-workspace call sites — so a caller who ignores the marker, the doc, the
classifier and the strict door still gets a shim. It is no longer possible to do
so without the fact being in hand in three places; it is not type-impossible.

**QF_LIA, scoped not built — and the recorded boundary was in the wrong place.**
Both integer infeasibility instances' **LP relaxations are infeasible**, and z3
4.13.3 returns the identical core from the relaxation (roster 5 rows, load plan
14 rows). Neither refutation needs integrality: each is a rational Farkas
combination, valid in any ordered commutative ring with 1 — the same 22-law
interface `generalize_over_ordered_ring` abstracts over, with ℤ as ADR-0456's
model. What blocks the route is a **sort gate**, not a theory gap:
`lra.rs::is_real` accepts only `Sort::Real` and the `Op::Real*` opcodes. The
slice is therefore "collect `Op::Int*` into the same `LinR` rows, reconstruct
over the ring interface, instantiate at `Int`" — plus a soundness-negative pass
so an LP-feasible integer-infeasible system keeps declining to
`Diophantine`/`IntInequality`.

**On the real instance.** `infeasibility_farkas_lean --require-kernel` on
`schedule-deadline.smt2` (60 rows, 5-row measured-irreducible core) now prints
`facade fragment Lra` / `carries ordered-field content` / `strict facade ACCEPTED
as Lra`, where the `infeasibility` lane had to print `LraDpll` / `STRUCTURAL
SHIM`. That example's own shim detector turned out to be **broken** — it matched
`axiom hyp` where the reconstructor mints `axeyum.reconstruct.lra.hyp._N`, so it
returned "no arithmetic" for a genuine module and had been right only for as long
as the answer was "shim". The second instrument caught it on the first run; it is
now classified on the declared name and type.

**`main` is red on three golden module pins, not this lane's.** The
`--no-fail-fast` sweep is **280 suites / 3,822 passing / 3 failed**:
`quant_affine_growth_lean` (79,801 -> **174,524** bytes),
`quant_eq_partition_lean` (51,989 -> **112,303**), `quant_residue_lean`
(33,339 -> **83,060**). All three reproduce **byte-for-byte in a
`git archive HEAD` snapshot with this lane's files restored from `HEAD`**, all
three assert on direct `int_reconstruct` calls this lane never touches, and all
three roughly double — one upstream change, likely `d326c74af` (WHNF cache key /
K-like reduction). Separately, `F:schedule-critical-chain-infeasible` records 30
axioms (21 prelude) where the example now measures **26 (17 prelude)**; its
`checker_command` still passes because it pins the *hypothesis* count, so the
stale number is in `notes`/`axiom_footprint`. All belong to other lanes.

**Hygiene incident, disclosed: `c391b36d4` carries one line that belongs to the
`axeyum-cas` lane** (`docs/reference/examples.md`, the `geometry_cofactor_routes`
row). Nothing lost — the line is committed exactly as written and their worktree
matches `HEAD` — but it is attributed to `lra-dispatch`. Not rewritten
(`ae589be97` precedent; no history rewrites in a shared checkout). **The
mechanism is new and the rule in CLAUDE.md has a hole:** I saw the foreign hunk,
did *not* `git add` the file, split the diff at `-U0`, and staged only my hunk
with `git apply --cached --unidiff-zero` — `git diff --cached --stat` confirmed
`1 insertion(+), 1 deletion(-)`. Then `git commit -m … -- <paths>` shipped two
lines, because **`git commit -- <pathspec>` commits the WORKTREE content of those
paths and discards what you staged for them.** Then I wrote that up recommending
the no-pathspec form and **used it**, and `172561568` swept five more of the
`axeyum-cas` lane's files — because a bare `git commit` commits the **whole
shared index**, which CLAUDE.md's first multi-agent bullet says in those words.
Both forms lose, in opposite directions: pathspec takes the worktree (loses
another lane's hunks *inside* a shared file), no-pathspec takes the index (loses
another lane's *staged files*). **There is no safe way to commit one hunk of a
file another lane is editing**; the surviving rule is the existing one —
`git add` + `git commit -- <paths>` on files where `git diff <path>` shows every
hunk is yours, and coordinate instead when it does not. My "control" was a
single-lane throwaway repo, which cannot exhibit the failure that matters.

**Next, for whoever picks this up.** (1) The 28 non-arithmetic structural routes
are marked, not fixed — marking turns a silent misreport into a visible gap.
(2) Multi-clause `DisjunctiveLra`: a two-clause Boolean `QF_LRA` row is outside
both the conjunctive Farkas path and today's one-clause disjunctive path.
(3) The trial reconstruction was not measured on the 60-row `schedule-deadline`
core (a 5 MB term); if it costs, return the built context from the classifier
rather than weakening the predicate. (4) The hypothesis-footprint gap both prior
lanes named is now reachable from the front door, which raises its priority.

**New lane — axeyum-proved mathematics (2026-08-12).** A full-day frontier
run produced two previously unknown four-colour Rado numbers,
`R_4(2(x-y)=3z) = 226` (closing an open entry of Chang-De Loera-Wesley,
ISSAC 2022) and `R_4(4(x-y)=3z) = 313`, both certified end to end by
axeyum alone: 8192 cube cells, ~250M DRAT steps, zero failures. Landed on
the way: streaming DRAT proofs (ADR-0381), the backward DRAT checker
(ADR-0382, 66x), and the claim ledger (ADR-0380). After the s1 → s4 machine
move all five interrupted lanes were re-verified and completed — the
three-valued evidence check (ADR-0384), zero-divisor-safe ground int
folding (ADR-0383), and the `axeyum-search` crate (SLS, offline cover
certification, `recertify_rado`) — and all 34 binary-DRAT ledger rows were
regenerated by axeyum's own core: the trusted path is axeyum-only, 38
claims / 0 errors, landed on main at `b5cc9e73d` with the complete 79-gate
`check.sh` aggregate green (s5, 2026-08-12). A new claim records
`R_4(5(x-y)=4z) > 740`, witness verified, the 741 refutation scoped in its
frontier block. Ordered follow-on work:
[`rado-session-diary-and-roadmap-2026-08-12.md`](docs/plan/rado-session-diary-and-roadmap-2026-08-12.md);
issue register:
[`findings-register-2026-08-12.md`](docs/plan/findings-register-2026-08-12.md).

**Alpha-equivalence exists now, and the canonicalizer is no longer
quantifier-blind (`WIP`, quant-duality, 2026-08-14).** Landed:
`F:quantifier-negation-duality` closed end to end, `open` to `proved` with a
certified `unsat-bool-simplification` certificate (`arena=ok`, z3 4.13.3
agreeing), which took the import backlog from 10 to 9. The handoff's one-rule
diagnosis was half right: `not (forall x. b) -> exists x. not b`
(`quant.negation_duality.v1`) is necessary but cannot close the file, because the
SMT-LIB front end mints a fresh arena symbol per binder occurrence, so the two
sides of the identity end up alpha-variant and hash-consed apart. The missing
capability was alpha-equivalence itself (`crates/axeyum-rewrite/src/alpha.rs`),
which did not exist anywhere in the tree; it also decides the negation duality
directly, by carrying a negation parity, so the `bool_simplify` certificate
checker re-derives the fact without rewriting anything.

Next, in priority order: (1) `F:barber-no-such-barber` already decides `unsat`
and agrees with z3 but reports `certified=0` — a decided fact waiting on a
certificate, not on a capability; (2) feed `alpha_equivalent` to the e-matching
and instantiation layers, where two alpha-variant triggers are still treated as
unrelated (gap #4 of the quantifier survey); (3) the canonicalizer still has no
vacuous-binder elimination and no miniscoping, and the duality push is the
standard first NNF step those would build on.

**Lane extension — from verification to proof (2026-08-12).** The general-`k`
shell lower bound became a **theorem with a written, reviewed proof** (for
`a >= 2`, `gcd(a,b) = 1`, `b < a`, `k >= 2`), which with a closed-form
monochromatic witness for every `b > a`, `k >= 3` gives the characterisation
**solution-free iff `b < a` or `k = 2`**. axeyum's in-tree Lean kernel checks
9 `forall`-quantified theorems over `N` with **zero axioms**, and the algebra
is verified by axeyum's own CAS. Not claimed: no upper bounds; not tight at
`k = 5`; the Lean export has **not** been checked by real Lean. Record, with
three retracted errors:
[`proof-approaches-2026-08-12/`](docs/plan/proof-approaches-2026-08-12/README.md).

**A new fact-ledger domain: FP kernel equivalence, settled exhaustively where
the width permits (`WIP`, fp-kernels, 2026-08-14).** Landed seven facts — four
`proved`, two `refuted` with pinned witnesses, one deliberately `open` —
answering the question compilers, GPU kernels and quantized ML pipelines
currently answer by sampling: *does the rewrite agree with its reference on ALL
inputs?* `F:fp16-doubling-add-equals-mul-two`,
`F:fp32-doubling-add-equals-mul-two`, `F:fp16-fp32-roundtrip-identity` (proved),
`F:fp8-add-monotone-rne` (proved, exhaustively and symbolically), `F:fp8-add-not-associative`
and `F:fp16-bf16-roundtrip-not-identity` (refuted), and
`F:fp16-add-monotone-rne` (`open`, see below). Every settled one carries two
evidence routes that share no code: axeyum's SMT front door (`fp.*` → fpa2bv →
CNF → re-checked DRAT) and `crates/axeyum-fp/examples/kernel_equivalence.rs`,
an exhaustive enumeration against `rustc_apfloat` (LLVM's APFloat, ADR-0028).
These are the ledger's first `smt-clausal` facts.

`F:fp16-add-monotone-rne` is `open` with `external_status: proved` and an
**empty evidence array**, on purpose: z3 4.13.3 proves it in 30.6s and bitwuzla
0.9.1 in 8.3s, and 2^48 triples rules out brute force, so binary16 has only the
symbolic route. For calibration, axeyum DOES settle the fp8 analogue — which
neither oracle can read — in 25m46s. This is a measured parity gap written down
as a target rather than dressed as a result;
`artifacts/facts/smt2/neg-fp16-add-monotone-rne.smt2` is the reproducible file.

Three measurements worth carrying forward. **(1)** At exactly the width where a
claim can be brute-forced, both industrial oracles decline: z3 4.13.3 returns
`unknown` on every fp8 E5M2 *addition* query (`ebits > sbits not supported` —
E5M2 is `(_ FloatingPoint 5 3)`), and bitwuzla 0.9.1 rejects the format as
experimental, its own suggested `--fpexp` escape being a build option the binary
refuses as a runtime flag. axeyum decides both, because ADR-0023 made the FP
builders generic over `(exp_bits, sig_bits)`. The gap runs the other way for
E4M3, which axeyum correctly refuses as non-IEEE and z3 accepts. **(2)** Arity,
not width, decides whether exhaustive settlement is available: all 2^32 binary32
values enumerate in 51s, while the ternary fp8 claims are exhaustive at 2^24 and
would be 2^48 at binary16. **(3)** On the symbolic route this stack is 2000x off
the specialised FP solvers — binary32 doubling: axeyum 202s, z3 0.1s, bitwuzla
0.1s on the identical file.

Also found, and general rather than FP-specific: the ledger's existing
`checker_command` convention is a bare `smtcomp_cli --evidence <file>`, which
exits **0 on any decided verdict**, so `scripts/check-fact-evidence-replay.sh`
was gating on "the binary ran", not on the recorded verdict. This lane's eleven
checkers wrap the verdict in a `test "$(… | tail -1)" = unsat`, with both
wrong-verdict controls measured non-zero. Pre-existing facts are other lanes' to
repair; the hole is worth knowing about.

Next, in priority order: (1) close `F:fp16-add-monotone-rne` — it is the
best-specified task here, nothing about the mathematics is in question and the
whole gap is throughput on a multi-operand FP comparison miter; (2) a Kahan
compensated-summation step versus naive addition at fp8 — the claim that would
actually certify a reduction kernel, and the ternary fp8 domain is already known
to enumerate in seconds; (3) fp8 **E4M3**, the format most fp8 inference
actually uses, which needs `axeyum-fp` to model non-IEEE `NonfiniteBehavior`
(APFloat already does) and where no external oracle can check us at all.

**Irreducibility is now measured, not asserted — three OR instances, three
irreducible cores, one of them kernel-checked (`WIP`, infeasibility,
2026-08-14).** The chain (deletion-minimized `get-unsat-core` -> Farkas
certificate -> Lean reconstruction) all existed and had never been pointed at a
real operations-research instance, and nothing anywhere re-solved a leave-one-out
subset — so "minimized core" was a hope, since `unsat_core` conservatively keeps
a row whose removal leaves the remainder `unknown`. Landed: three committed
instances under `artifacts/instances/infeasibility/` (nurse roster 5/102 = 4.9%,
hazmat load plan 14/90 = 15.6%, project schedule 5/60 = 8.3%), a measuring
example that re-solves every leave-one-out subset AND replays each returned model
through the IR evaluator, a z3 cross-check script that agrees on every core and
every leave-one-out, and four facts (0 validator errors). Each core's `unsat`
turned out to carry a **re-derived** arithmetic certificate
(`UnsatArithAletheProof` / `UnsatFarkas`, `check_outcome = verified`, trust step
`farkas` certified this run), not a bare verdict. The schedule core reconstructs
into the Lean kernel from its all-multipliers-1 Farkas certificate — the largest
LRA reconstruction in the tree (every existing exercise uses 2 or 3 constraints).
Two traps recorded in the diary: `prove_unsat_to_lean_module` routes this query
to `ProofFragment::LraDpll`, whose module is a **structural shim** that
kernel-checks and contains no arithmetic at all (`reconstruct_lra_proof` must be
called directly); and the proof term is **5.1 MB** for a five-row explanation,
because the arith prelude has no numerals.

Next, in priority order: (1) numerals in the arith prelude — 5.1 MB for five
rows is what stops a kernel-checked explanation being shippable; (2) a
hypothesis-footprint audit for the LRA route, binding each `lra.hyp._N` back to
its originating assertion (the propositional route has
`declared_assumption_clauses`; the arithmetic one has nothing, so the example can
only count the axioms, not check them); (3) facade dispatch order, so an SMT-LIB
QF_LRA `unsat` can reach `ProofFragment::Lra` instead of the shim — nothing in
the repository currently asserts `ProofFragment::Lra`; (4) an integer route: both
LIA cores have re-checked Alethe refutations and no kernel path; (5) a filtering
IIS algorithm, since the deletion loop costs O(n) full solves and is hopeless
past a few hundred rows.

Full reasoning, including what a commercial IIS gives that this does not:
[`docs/mathematics-2026-08/diary-infeasibility.md`](docs/mathematics-2026-08/diary-infeasibility.md).

**Lane extension — publishable result, replication, and evidence pinning
(2026-08-13).** Three sibling repositories brought to a submittable state:
both headline instances pinned by regeneration, the shipped arXiv bundle
made re-checkable, five-host clean-clone replication across three
toolchains, four review passes, and a monolithic refutation of F_313 that
removes the cover composition meta-argument for that value. Full record,
including three mistakes that cost real work:
[`rado-publishable-result-2026-08-13.md`](docs/plan/rado-publishable-result-2026-08-13.md).

**Parallel documentation action.** The comprehensive pass and 2026-08-09
README application/vision revision are closed. Continue only for a concrete
stale claim; keep application maturity and sub-document links aligned, but do
not duplicate generated capability tables or modify solver behavior to match
prose. The user/reference/internals/crate surfaces and all 69 Cargo examples are
indexed, and source guards reject universal proof claims.

**Gate scope and the wall-clock reference frame (`WIP`, gates, 2026-08-14).**
Landed: cargo's mtime-based freshness could let `cargo clippy` **and**
`cargo test` pass over source they never compiled (measured: `cargo test` printed
"1 passed" for a test that must fail), so both now run through wrappers that
touch content whose hash changed and then report how many targets/tests they
actually examined; the divergence between `just check` (145 steps) and
`./scripts/check.sh` (89) is pinned in
`scripts/check-aggregate-scope.expected` and fails when it grows; and the
`progress_frontier` ratchets now calibrate the machine before and after each
sweep, scale the budget, and refuse to enforce (`NOT COMPARABLE`) or to raise a
baseline (`ADVISORY ONLY`) outside their bands — the stock fixed-budget gate
reported `bv_reduction = 29` against a baseline of 30 on this box's efficiency
cores, four runs out of five, a REGRESSION that never happened.

Next, in priority order: (1) `MAX_N = 40` has turned `nra_degree`, `nia_unsat`
and now `string_bound` into constants — three of five ratchets can no longer show
progress; (2) apply `scripts/check-source-freshness.sh` to the remaining cargo
entry points (`scripts/check-scope.sh`, the `bench-*` recipes) and to the
snapshot instruction lanes are given; (3) one authoritative step manifest for the
aggregate gate, with a wrapper column, so the 66 recorded differences can shrink
instead of only being prevented from growing.

**The real-Lean gate now counts what it checked (`WIP`, lean-gate-honesty,
2026-08-14).** Landed: ten suites that hand generated modules to an external
`lean` binary used to print `ok` on a machine where Lean 4.30.0 was installed —
`elan` keeps toolchains under `~/.elan/toolchains/*/bin/lean` and puts nothing on
`PATH`, so every private `lean_bin()` concluded Lean was absent and skipped.
Discovery now lives in one place
(`crates/axeyum-lean-kernel/tests/support/lean_probe.rs`, shared by `#[path]`
into both crates), an unresolvable `AXEYUM_LEAN_BIN` is an error rather than a
fall-through (or the `/nonexistent` control proves nothing), a skip prints
`AXEYUM-LEAN-SKIPPED <tag> not_checked=<n>` with where discovery looked, and
`scripts/check-lean-gate.sh` sums the `AXEYUM-LEAN-CHECKED` markers and enforces
a floor. On this box, with no environment variables set at all: **10 suites, 33
tests, 40 real-Lean checks**, up from zero. Reverting `a5975725f`'s export fix
makes it fail with the pre-fix signature (11 passed / 3 FAILED).

Next, in priority order: (1) the defect this gate found on its first honest run —
`lean_crosscheck`'s `quant_bv_source_instance_set` family emits proof shares Lean
reads as `Prop`-valued statements where proof terms are required, plus
undeclared share names; 69 of 70 families pass, and the suite is excluded from
the gate by name until it is fixed; (2) fold `lean_crosscheck` into
`scripts/check-lean-gate.sh` once it is (~60 s); (3) nothing yet enforces that a
NEW suite shelling out to `lean` is added to the gate's manifest — the same
class of hole one level up.

**70 of 70 proof families now check in a real Lean; the gate's exclusion is gone
(`WIP`, quant-bv-shares, 2026-08-14).** `lean_crosscheck`'s
`quant_bv_source_instance_set` rejection was a **printer defect, not a
reconstruction defect** — the in-tree kernel's term was well typed throughout,
and the whole fix is in the Lean *writer*. The compact proof-sharing pass hoisted
a *proper prefix* of a recursor spine into its own definition
(`def axeyum_proof_share_149 := @Or.rec P`); Lean makes an inductive's parameters
and a recursor's motive implicit, so that definition inherits them as **leading
implicit binders** and the bare reference `axeyum_proof_share_149 Q` silently
re-inserted metavariables for both, putting `Q` in the `inl` minor-premise slot.
The unknown-identifier errors were the cascade — a `def` that fails to elaborate
never enters the environment. `lean_pp::hoisting_exposes_implicit_binders` now
refuses to hoist an under-applied application whose spine head is a constant Lean
regenerates; module size is unaffected (+2.2% bytes, −32% lines) because
saturated spines and their arguments stay shareable. Measured after: 70/70
representative modules and **163/163** exhaustive modules accepted by Lean
4.30.0, `#print axioms` clean. `scripts/check-lean-gate.sh` with no environment
variables set: **12 suites, 49 tests, 112 real-Lean checks** (was 40), floor
raised 35 → 105. No fact and no ADR are owed: nothing the kernel accepted was
ill-typed.

Next, in priority order: (1) nothing still enforces that a NEW suite shelling out
to `lean` reaches the gate's manifest — the hole `lean-gate-honesty` named, one
level up, and the only reason this defect needed a human to notice it; (2) the
`maxRecDepth 100000` these modules carry inline is a silent dependency on Lean's
elaborator bound — a Lean whose default changed would move the pass/fail line
without any of our gates saying so; (3) the same implicit-binder rule should be
audited for `write_decl_command_with_at`'s *local* `let` shares, which are
covered by the fix but have no dedicated fixture.

Found and repaired on the way, both `a5975725f`'s debt and both confirmed against
a `git archive HEAD` snapshot before being touched:
`lean_pp::tests::renders_self_contained_module` still asserted `axiom False :
Prop` (the only failing test in `axeyum-lean-kernel` on HEAD), and all 15
`crates/axeyum-solver/tests/fixtures/lean-modules/*.lean` byte-stability fixtures
were stale (7 failing `reconstruct::tests::*_is_byte_stable` on pristine HEAD).
Re-blessed and re-checked through real Lean; the fixture diff contains zero
`proof_share` lines, i.e. none of it came from this lane's change. Four
`(length, fnv1a)` pins over generated modules (`quant_affine_growth_lean`,
`quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean`)
were stale for the same reason — three of the four render byte-identically with
and without this lane's change, the fourth 513 bytes smaller. Re-pinned only
after each module was put through Lean 4.30.0 and accepted with a clean
`#print axioms`, because two integers cannot tell "the printer improved" from
"the printer broke".

**The importer is not the bottleneck; our kernel's definitional equality is
(`WIP`, formalized-collect, 2026-08-15).** The
[`docs/formalized-math-2026-08/`](docs/formalized-math-2026-08/README.md)
strand had zero landed work for as long as it existed. It is started, from a
measurement: 40 well-known Lean `Init`/`Std` theorems exported one at a time by
an official `lean4export` binary (commit `a3e35a58`, toolchain 4.30.0) and put
through `axeyum-lean-import` — **13 admitted, 27 declined, and every decline came
from `Kernel::add_declaration`, none from the reader**, at any size from 6 KB to
500 KB. The declines cluster into four causes, the largest being that `Nat.add`
is compiled through `Nat.brecOn`/`Nat.below`/`Nat.add.match_1` and does not
reduce for us — so **`Nat.add_comm`, the most cited theorem in our own fact
ledger, cannot be imported**. Landed with it: five facts on the new
`imported-kernel-lean` route (ADR-0454), each citing a SHA-256-pinned stream in
`artifacts/lean-imports/` and re-derived by two independent checkers (our kernel
and a real Lean 4.30.0 `#print axioms`); `01-collect.md` rewritten against
measured, cited figures with a table of nine things the first draft got wrong. A
sixth import was written and withdrawn: `Nat.not_succ_le_zero` is already proved
axiom-free in our own Nat prelude, so landing it as an import would have
understated what we hold — and the two are the same proposition under different
formal statements, which is the alignment problem arriving early.

Next, in priority order: (1) the **decline census** — export a few hundred `Init`
declarations, import each, report blocker clusters; a fail-closed importer at
13/40 reports only the first blocker in a stream, so this is the only way to size
the work, and it is minutes of compute; (2) hand the kernel lane the
**`brecOn`/`below` reduction** gap, which alone unblocks 15 of the 27 observed
declines; (3) re-pin the toolchain deliberately — `lean4export` HEAD tracks
`v4.34.0-rc1` while we are on 4.30.0, and moving re-exports every committed
stream and changes every pinned digest, so it is one decision made once.
**Not** blocked on a Mathlib clone: cloning before the census is collecting
ahead of the constraint.

**The `brecOn`/`below` blocker is closed, and it was one missing congruence rule
(`WIP`, import-brecon, 2026-08-15).** Taking over
[`formalized-collect`](docs/plan/status/85-formalized-collect.md)'s finding, the census came
first, because a fail-closed importer reports one blocker per stream and the
handed-over cluster table was 27 first-blocker samples, not a census.
`census_ndjson` (new, diagnostic-only: declines are recorded and the declaration
**skipped**, so the staging kernel still holds only gate-accepted declarations,
and it returns counts — never a `Kernel`) over a corpus that is now *written
down* (`scripts/lean-import-census.sh`, 40 named `Init`/`Std` declarations) said:
**22 of 40 streams clean, 93 declines, but only 10 distinct root blockers** —
61 of the 93 were cascades, and the "5 `noConfusion`" and "5 `HEq`" clusters were
each **one** declaration seen five times.

Then the fix, which was not in the reducer. δ/β/ζ/ι/projection reduction already
handle the whole `brecOn` encoding — `whnf` of `Nat.add n (succ m)` really does
return `Nat.succ ((Nat.rec … m).1 n)`. `def_eq` was missing **`Proj`/`Proj`
congruence** (`a.i ≡ b.i` when `a ≡ b`), which Lean has and our port dropped; two
stuck projections one δ-step apart compared as `false`. After it: **37 of 40
streams clean, 1 distinct root blocker**, and **`Nat.add_comm` imports** (52
declarations, empty Lean axiom footprint). Nine of ten root blockers closed by
one rule, because `noConfusion`, `match_n` and `casesOn` are all compiled through
the same machinery and `below` is built from `PProd`. No new fact:
`F:nat-add-comm` is already ours on `kernel-lean`, so the stream is pinned as a
**capability fixture** (`"fact": null`) with a replay test instead.

Next: **K-like reduction** (`to_cnstr_when_K`), which is the single remaining
root blocker — `eq_of_heq` needs `cast α α h a ≡ a` with `h : α = α` a variable,
and only K-like reduction gets there. Our kernel already computes the predicate
(`is_k_like_inductive`) and uses it **only** to emit the wire `k` flag;
`reduce_rec` never consults it. It is deliberately **not** started here, because
sizing it turned up two things the reference code does not show: (1) the guard
is `is_def_eq(infer_type(major), …)` and the major is an **fvar**, so reduction
needs the `LocalContext` it currently never receives — ~55 internal call sites,
and `pub fn whnf` is public API with users outside the crate; (2) that makes
`whnf_cache`, keyed on `(env revision, ExprId)`, **context-dependent and
unsound** — `LocalContext::new()` restarts fvar ids at 0 and `check_declaration`
builds two fresh contexts with no environment change between them, so the cache
spans both. Settle the cache key before writing the rule. It also needs its own
negative suite (one-constructor `Prop` *with fields*, non-`Prop` structure,
mutual group must each stay non-reducible), since it asserts a definitional
subsingleton rather than a congruence. Recorded, not blocking: we lack
`to_cnstr_when_structure`, and `reduce_projection` uses full `whnf` where Lean
uses `cheap_proj` (ordering, not correctness).

Also fixed here, found in my own tool: `lean4export` **exits 0** on a constant
it cannot find, panicking to stderr and writing a metadata-only stream — which
the census scored as a *clean* stream. Both the script and the census example
now reject a declaration-free export instead of counting it as a pass.

**The latent cache-key unsoundness is defused and K-like reduction landed; the
40-stream import census is 40/40 clean with zero root blockers (`WIP`,
whnf-cache-key, 2026-08-15).** Taking over the landmine
[`import-brecon`](docs/plan/status/86-import-brecon.md) stopped in front of. Full write-up:
[`docs/formalized-math-2026-08/diary-whnf-cache-key.md`](docs/formalized-math-2026-08/diary-whnf-cache-key.md).

**Was it real?** Yes, and it now runs as a test rather than an argument.
`tc_tests::whnf_cache_key_collision_is_constructible` builds two
`LocalContext`s that both mint fvar **0** — one recording it as `True`, one as
`False` — with no declaration admitted in between, so the environment revision
does not move either. The same `ExprId` (`True.rec … h`, `True` being K-like)
has two different correct normal forms in them. The pre-fix algorithm is kept
verbatim as `#[cfg(test)] whnf_core_context_free_cached` and the test runs it:
it answers the **first** context's normal form in the second. It was **latent,
not live** — nothing in reduction consulted a context before this commit — so no
fact and no ADR are owed; the fix ships in the same commit as the rule that
would have made it reachable.

**The key.** Split on `has_fvars`, because that boundary has a *structural*
argument rather than a disciplinary one. Closed expressions stay in the
kernel-global cache: β/ζ/ι/projection/δ build only from subterms of the input
and from (closed) environment declarations, so a reduction that did not start
with an `FVar` can never reach a context lookup. Open expressions are memoised
by the `LocalContext` itself, beside the `infer_cache`/`def_eq_cache` already
there and already cleared on `push`/`pop` — which is exactly the validity domain
an answer that depended on a local's type should have. The closed half's
argument is enforced, not asserted: `Kernel::reduction_ctx_reads` counts context
reads inside reduction and `whnf_no_unfolding` asserts it does not move while a
closed term is normalized, so a future context-consulting rule trips a check
instead of quietly invalidating the cache.

**Cost: nothing measurable.** `examples/prelude_build_timing.rs` (new) over the
two heavy preludes, release, both behaviours built from one tree — old key
22.3/22.9 ms `nat` and 39.5/40.8 ms `integer`; shipped split 22.5/22.8 and
39.6/40.0. Dropping open-term memoisation altogether would have cost 8–9%.
(My first "baseline" was a stale binary and made the split look like a speed-up;
an A/B has to be two builds of one tree.)

**`pub fn whnf` did not change.** It is now `whnf` in the empty local context,
delegating to `pub(crate) whnf_core(e, ctx)` — a restriction, never a widening,
since without a context K cannot fire on an open term. The threading stopped at
seven functions, not the ~55 call sites the handover estimated.

**K-like reduction** (`k_like_major`, Lean's `to_cnstr_when_K`) consults the
predicate we already computed and used only for the wire `k` flag. Guard is
Lean's, and every clause is load-bearing: removing each in turn flips exactly
one test. `eq_of_heq` imports; census **40 of 40 streams clean, 0 declines, 0
root blockers** (was 37/40 with 1). No new fact — a capability, pinned by tests.

The negative-suite controls also caught two of my own tests passing for the
wrong reason: a constructor-with-fields probe is refused by the def-eq guard
before the zero-fields clause is reached, and a mutual `Prop` group's recursor
is small-eliminating so the probe shape *cannot be built* for it
(`UniverseArityMismatch`). Those three clauses are now pinned directly on the
predicate in `inductive_tests::the_k_like_predicate_*`, where the controls do
flip them.

One caveat on the gates, recorded rather than smoothed over:
`check-fact-evidence-replay.sh` reports 83/85 re-derived with one timeout (the
known-expensive `F:sorting-network-optimal-size-n6`) and one failure,
`F:ordered-ring-farkas-refutation` — whose evidence is entirely in
`axeyum-solver`, a crate another lane is mid-edit in, including an *untracked*
example one of its checkers names. All four of its checkers pass when run
directly. That is the shared-worktree caveat the script's own header documents,
not a rotted fact; every kernel-lean fact backed by `axeyum-lean-kernel`
re-derived.

Next: the corpus has stopped measuring at 40/40 — replace it with one that
exercises what we know we lack (`to_cnstr_when_structure`; `cheap_proj`
ordering in `reduce_projection`). Still open across three diaries now: the
toolchain re-pin (4.30.0 → current).

**Exported all of `Init`+`Std` (96,591 declarations) and all of Mathlib
(680,925), measured a seeded random sample of each, fixed the binding constraint
— kernel `Nat` literal arithmetic — and located the next one (`String`
literals: 52% of `Init`+`Std`, 79% of Mathlib)** (`WIP`, import-scale,
2026-08-15). Continues [`whnf-cache-key`](docs/plan/status/87-whnf-cache-key.md), whose 40/40
corpus had stopped measuring. Full write-up:
[`docs/formalized-math-2026-08/diary-import-scale.md`](docs/formalized-math-2026-08/diary-import-scale.md).

**The corpus.** `lean4export` with no constant list dumps the whole environment:
`Init`+`Std` is 10.5M records / 96,591 declarations / 25 s / 552 MB, and Mathlib
v4.30.0 (`c5ea0035`, built on s5 from `lake exe cache get` in 77 s) is 680,925
declarations / 5.5 GB / ~4 min. Both under `/nas3/data/axeyum/lean-import-scale/`.
`scripts/lean-import-scale-census.sh` (new) samples that name list with a
recorded seed, exports each declaration's own closure, and censuses it under an
OS-enforced time and address-space bound — per stream, so a diverging declaration
costs one bucket instead of the run.

**The whole-environment stream cannot be censused in one pass, and the reason is
the first result.** Three minutes in, RSS was 22 GB and climbing; the process's
own `/proc/<pid>/fdinfo` offset was **frozen** at 0.4% of the file across a
minute in which it allocated another 3 GB. Stuck on one declaration, not slow —
`Nat.Linear.Expr.denote_toPoly_go`, which alone consumed 25 GB without answering.
A stream through the trusted gate has a third outcome besides admit and decline:
it can diverge, and a run that dies partway looks like a resource problem rather
than a located one.

**The constraint was literal `Nat` arithmetic.** The failing streams' literals
gave it away: `55296`, `57343`, `1114112`, `4294967296` — `Char`, `UInt*`,
`USize` and `Fin` are `Nat` under bounds like `2^32`, and this kernel had no rule
for `Nat.add` on literals, only `Nat.succ` folding. Reaching `2^32` by successor
steps is unbounded, not slow. `Kernel::reduce_nat_binop` is Lean's
`type_checker::reduce_nat` for the fourteen binary operations, arbitrary
precision, with Lean's totality conventions and Lean's `1 << 24` exponent bound.
`Nat.Linear.Expr.denote_toPoly_go` went from 25 GB/no answer to **clean in
0.04 s**; `Option.repr` from 8 GB exhausted in 95 s to the next wall in 0.05 s.

**Guards, because this widens definitional equality.** A `Definition` (never an
axiom or opaque), no universe parameters, exactly `Nat → Nat → Nat` or
`Nat → Nat → Bool`, and Lean's `Bool` (`[false, true]`, indices 0 and 1). Two
traps paid for: the type must be checked by *walking* the `Pi` layers, because
binder names are part of an interned node and the official export names them
(my first version compared ids, never fired, and the census was unchanged); and
the table must **look names up without interning them**, because name ids are
emitted in insertion order and minting `Bool.true` during a reduction renumbers
the whole subsequent export — `axeyum_built_prelude_round_trips` caught that.

**Our own preludes are untouched by mechanism, not by luck:** `build_logic_prelude`
declares `Bool` as `[true, false]`, which is not Lean's, so the table is refused
for every prelude-built environment and the 119-theorem `nat` inventory cannot
move. `tc_tests::the_reconstruction_prelude_is_not_accelerated` asserts all three
links of that argument.

**Controls, one clause at a time.** Rule off → 4 positives fail. Type check off,
kind check off, arity check off, `pow` bound off → each flips exactly one
negative test. The two `Bool`-order clauses are **individually redundant and
jointly load-bearing** — dropping either alone changes nothing, dropping both
flips the test. A one-line summary would have been wrong; the controls had to be
run separately to know which.

**The answers are checked by Lean.** `real_lean_nat_arithmetic_crosscheck` (new,
registered in the gate) generates its obligations *from this kernel's output* —
24 argument pairs including both totality conventions, truncated `sub`, `gcd`
with a zero, and values past `2^64` — and official Lean 4.30.0 accepts all 24.
Mutating `x % 0` from `x` to `0` makes Lean reject, so it discriminates. Floor
raised 105 → 107; measured 115.

**Distribution, 500 random `Init`+`Std` / 400 random Mathlib declarations:**
CLEAN 219 (43.8%) / 78 (19.5%); **UNSUPPORTED `literal-string-typing` 262
(52.4%) / 315 (78.8%)**; DECLINED 16 / 7; RESOURCE 3 / 0. Cascades separated:
265 declines → **6 distinct roots**, and 154 → **5** — of which four are the
same declarations. **Not one Mathlib-specific root blocker**: everything this
kernel refuses across a 400-strong Mathlib sample is in Lean's `Init`/`Std` core
(`Nat.bitwise._unary`, `Nat.Linear.*`, `Fin.*`). Category theory, measure theory,
affine geometry and functional analysis are in the clean set.

A fourth outcome class was also separated: some of the RESOURCE streams were
**stack overflow**, not memory. The census now runs on a 512 MB stack (what
`lean -s` does) — which fixed exactly **one** of the four; the other three run
longer, reach ~6.3 GB of heap and overflow that too. Runaway reduction, not
deep-but-finite. I had written "all four import in under two seconds" in that doc
comment before measuring the other three.

Next: **`String` literals**, sized in the diary against Lean's own call sites
(wire arm, `Lit::Str` typing behind a `String` bootstrap,
`string_lit_to_constructor`, the `whnf` and `def_eq` uses, the writer's
round-trip). Roughly 1.5× this lane's `Nat` work — one focused session. Note that
`String.ofList` is a *definition* in Lean 4.30, not a constructor, so the
expansion is δ-reducible; that is where a port goes wrong. It buys 52%/79% of
streams *reaching the next wall*, not 52%/79% clean — what is past strings for
those is unmeasured. Still open across four diaries: the toolchain re-pin.

**Implemented primitive Lean `String`-literal semantics end to end — checked
bootstrap, Unicode-scalar `String.ofList` expansion, projection and recursor
hooks, the `strVal` wire arm and the writer arm — and re-censused the seeded
samples the previous lane measured** (`WIP`, import-strings, 2026-08-15).
Continues [`import-scale`](docs/plan/status/88-import-scale.md), which sized this and left it.
Full write-up:
[`docs/formalized-math-2026-08/diary-import-strings.md`](docs/formalized-math-2026-08/diary-import-strings.md).
Decisions: [ADR-0366](docs/research/09-decisions/adr-0366-preregister-lean-string-literal-semantics.md)
accepted; [ADR-0461](docs/research/09-decisions/adr-0461-lean-string-literal-def-eq-hook-is-unreachable.md)
new.

**The bootstrap.** Official Lean inherits `String`/`String.ofList`/`Char.ofNat`/
`List` from its own boot; we import into a fresh environment, so spelling alone
would let the *stream* decide what a literal means. `String.ofList` must be a
`Definition` of exactly `List Char → String` with no universe parameters,
`Char.ofNat` one of exactly `Nat → Char` for the same `Char`, `List` the
one-parameter recursive family at universe zero with `[nil, cons]` at 0/2 fields,
and `Char`/`String` one-constructor structures named `Char.mk` and
`String.ofByteArray`. Nothing is interned: names are looked up and every
expression handle is read back out of a declared type, because minting a name
renumbers a subsequent export.

**The conversion is over Unicode scalars, never bytes:** `"é"` is one character
`0xE9`, `"🙂"` is `0x1F642`, `"e\u{301}"` stays two, and nothing is normalized.

**Lean's own def-eq hook cannot fire, and removing each hook in turn is how I
know.** `try_string_lit_expansion` keys on an immediate `String.ofList` head, but
`is_def_eq_core` runs lazy delta first and `String.ofList` is a *definition* in
4.30 — so the head is already `String.ofByteArray` by the time the hook looks.
The rule dates from when `String` was `structure String where mk :: (data : List
Char)` and that constant was a constructor. Controls: projection hook removed →
**3** tests fail; recursor hook removed → **1**; def-eq hook removed → **0**.
What identifies a literal with a constructor application is structure eta calling
the projection rule. The hook stays (it is in the pinned source and can only
accept *more*), and a test pins the *mechanism* so a toolchain re-pin that makes
`String.ofList` a constructor again fails loudly. ADR-0461.

**Negative tests.** Eleven bootstrap mutations each rejecting with
`StringLiteralBootstrapMismatch`, paired with the unmutated positive in the same
test; byte-split, reordered, truncated and composed/decomposed controls beside
every scalar positive; a bare constant and an `Opaque` alias both refused; a bare
literal not expanded by ordinary `whnf`. Our reconstruction prelude cannot
impersonate Lean's `String` **by mechanism** — its types live under
`axeyum.string.<n>` — and the test asserts the namespace, not just the refusal.

**A writer defect on the way.** `json_string` wrote `\t`/`\b`/`\f`; Lean's
`Json.escapeAux` short-escapes only quote, backslash, newline and carriage
return and writes every other sub-`0x20` character as `\u00xx`. Irrelevant while
only name components were emitted; load-bearing the moment `strVal` is, because
the difference parses identically and is not byte-identical to lean4export's.

**The ADR-0366 artifact, reproduced exactly.** That ADR froze an export it said
had never been retained or re-run. Re-exported twice from pinned Lean 4.30.0,
byte-identical, and matching all six frozen properties including SHA-256
`2404a6ca…0ab4`. It **imports clean** (290/290 records, 374 declarations, 0.04 s)
and the literal *computes*: a new probe example shows the imported
`importStringLiteral` definitionally equal to `String.ofList` over its scalars in
Lean's own environment — through the real `ByteArray`/`List.utf8Encode` — while
refusing the reordered list.

**Checked by Lean.** `real_lean_string_literal_crosscheck` (new, registered)
reads scalar lists back out of *this kernel's* reducts for ten payloads and has
Lean 4.30.0 confirm each; switching our conversion to bytes makes Lean reject.
Floor raised 107 → 109; measured 117.

**Re-census, same seeded samples, same bounds.** CLEAN `Init`+`Std` 219 -> **254
of 500**, Mathlib 78 -> **139 of 400**; `literal-string-typing` 262/315 -> **0**;
DECLINED 16 -> **242** and 7 -> **241**. So strings bought **7 and 15 points of
clean rate, not 52 and 79** — the previous lane was right to refuse to project.
What they really bought is that **18.6x and 86x more declarations reach the
trusted gate at all** (34,112 -> 634,291 records; 13,710 -> 1,181,015), because a
stream no longer stops at its first `strVal`.

Roots: 6 -> **50** (`Init`+`Std`) and 5 -> **267** (Mathlib), with 98%+ of the
97,341 / 256,297 declines being `UnknownConst` cascades. **Every root is a
definitional-equality failure** — `TypeMismatch`, `DeclarationValueMismatch`,
`NotAPi` — and none is a missing construct. A new fourteen-stream class is an
*importer* record cap, not a verdict.

**The previous lane's headline flips.** "Not one Mathlib-specific root blocker"
was true only because strings were hiding the Mathlib: `Pi.preorder`,
`Prop.partialOrder`, `DistribLattice.ofInfSupLe._proof_4`,
`Function.Injective.*`, `Nat.inst*`, `Int.instCommRing` now sit at the top of the
Mathlib table and are absent from `Init`+`Std`'s, which is containers and
`ByteArray`. Cumulatively, fixing the top 50 `Init`+`Std` roots clears **all 242**
of its declined streams; Mathlib's top 100 clear 142 of 241.

**Next binding constraint, located.** `Nat.bitwise._unary` is the top root in both
(236/500 and 186/400 streams); its stream admits 301 of 302 records and refuses
only the declaration, with `TypeMismatch`. It is the **well-founded-recursion
unary helper** shape — `WellFounded.Nat.fix` over a `PSigma`-packed argument with
an `InvImage` relation and a dependent `PSigma.casesOn` motive — and
`Nat.Linear.Poly.denote_reverse`, `…ExprCnstr.denote_toNormPoly` and the
`Std.DTreeMap.Internal.*.eq_def` roots are the same family. No new IR construct
and no new bootstrap: this is a def-eq gap on a shape the kernel already
represents, so the work is diagnosis first and the fix is unsized until the
mismatch is exhibited as one pair of terms. Budget a session for the diagnosis.

**Lane closed (`DONE`, examples-sweep, 2026-08-15).** Task was
`docs/refactor-2026-08` finding #4 ("documents assert what the code does
not"): `python3 scripts/check-parity-docs.py` was red because six landed,
git-tracked Cargo examples were missing from `docs/reference/examples.md`.
Added a catalog row for each, stating the boundary/question the example
answers rather than restating its name, verified against the example's `//!`
header, `main`, and (for the timing/measurement claims) the landing lane's own
status file. All three gates (`check-parity-docs.py`, `check-links.sh`,
`gen-plan.py --check`) are green. No other lane's untracked WIP was touched;
none was found among the flagged files.

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

**Next slice.** Restart and derive the complete V2 census from the fully gated
classifier repair. Only after a zero-loss
derivation may normalization failures,
unsupported difference shapes, disequalities, explanation blowups, and
ordinary search failures be classified across the three current ledgers. Treat
the repaired high-memory LRA normalization case and the rejected global 12/12
DL split as permanent controls before adding new DL syntax. The
[`v2 cross-division census preregistration`](docs/plan/qf-linear-a5-cross-division-census-v2-preregistration-2026-08-09.md)
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

## Workstream state

| Workstream | State | Current boundary / next action |
|---|---|---|
| Integration and gates | `DONE`; 2026-08-12 | Linear A5 through `4b6b76555` is on `main` by conflict-free fast-forward. Integrated code, frontier, CAS, rustdoc, Glaurung, resource, resume, Lean, and parity gates are green; volatile frontier timings were not credited. Verify the remote ref before resume; hosted CI is separate. |
| Arithmetic deadline reliability | `DONE` | Shared deadline, CAD polls, LRA ceilings, bounded DL probing, exact resume identity, and six fresh retained divisions are complete; see the 2026-08-06 closure note. |
| Full-library measurement | `WIP`; A2 readiness `DONE` | The R1--R5 readiness stack is integrated by `8ed5ad089` and focused/aggregate/scoped/topic/full-main green; the real registered offline-build smoke passed. No live run, preparation root, or launch authority exists. A later live C0/F2 step requires separate review. |
| QF_NIA breadth | `WIP`, yielded | Current clean result remains 34/200 versus 89/200. Reconstruction, large-core deletion, relevance activation, and bounded clause-estimate attribution are closed negatively without production solver code. The final diagnostic failed its exact pipeline-boundary record gate; no mechanism or 200-row run is authorized and the 64,000,000 ceiling remains. Move to A4 unless independent new NIA evidence appears. |
| QF_UFLIA breadth | `WIP`, yielded | Historical 94/180 remains; the exact-commit restart produced 93/200 because one SAT case is wall-clock unstable. No sidecar or new result was credited. |
| LRA/IDL/RDL | `WIP`; V2 failed | QF_LRA passed; QF_IDL lost two decisions. Replay confirmed both. B1 failed and was removed; G1 found a nearby existing DL boundary. Preregister separate follow-ups; QF_RDL is forbidden. |
| QF_BV/QF_SLIA/UF/QF_ABV | `WIP`, strong selected cells | Preserve current ledgers; do not prioritize small score gains above A2–A6. |
| Evidence and Lean reconstruction | `WIP` | A6 and A9; distinct certificate/check/reconstruction claims. |
| Route exploration | `BLOCKED` beyond catalogue work | Proposed track; T0.2/T0.6/T0.1/T2.3 precede T3.5. |
| SMT-LIB/API conformance | `WIP` | A8 then A10; S1 command/event IR first. |
| CAS parity | `BLOCKED` by deliberate pause | Wave-24 code `01d47334` and pause commit `245d8f25` are ancestors of current main. Do not start wave 25 until the user resumes it and retained specialized gate evidence is re-audited. |
| Consumer apps / verified systems | `WIP`, non-critical path | Existing EVM, verifier, property, reflection, and symbolic-execution slices remain useful; do not preempt A2–A7 without measured demand. |
| Foundational resources | `WIP`, separate content lane | Keep generated-resource gates green; record only project-level priority changes here. |
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; 69 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
| Worktree and build-cache hygiene | `WIP`, recovered | A11; only clean `main` is registered and published. A verified 2026-08-12 external Git bundle preserves the retired refs/stashes; all old branches, salvage stashes, inactive checkouts, and their large Cargo targets are removed. Next automate deterministic read-only inventory and exact-target cleanup classification. |

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
