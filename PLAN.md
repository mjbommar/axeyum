# Axeyum — Master Plan And Status

This is the single entry point for starting or resuming work. Read this file
first; it tells you what the project is, where it stands, what to do next, and
where everything else lives. Update the **Status** and **Next Actions**
sections at the end of every working session.

## What Axeyum Is

A Rust-first automated reasoning stack: typed term IR → rewriting → query
planning → solver backends (native SMT oracles + a growing pure Rust
bit-blast-to-SAT path) → models, proofs, and checkable evidence.

Identity in one sentence: **untrusted fast search, trusted small checking.**
Every `sat` gets a model checked by evaluation; every `unsat` eventually gets
a proof artifact or an independent oracle cross-check.

North star: a **complete framework for general reasoning, logic, and
proving**. The finite-domain core being built now is the foundation layer of
that framework, not the destination — the expansion ladder runs through
arithmetic, theory combination, quantifiers, and proof production
(see [north-star](docs/research/00-orientation/north-star.md)).

Full framing: [docs/research/00-orientation/mission-and-scope.md](docs/research/00-orientation/mission-and-scope.md)

## Status

Last updated: 2026-06-12

- Phase: **Phase 5 first pure-Rust backend slice.** M0, Phase 1, SMT-LIB
  ingestion/export, the micro-corpus benchmark harness, the public QF_BV
  baseline, and the Phase 3 query/rewrite/evidence entry contracts are
  implemented/recorded. The first default denotation-preserving canonicalizer
  is implemented in `axeyum-rewrite`, wired through the rewrite manifest, and
  checked against focused examples, deterministic generated evaluator
  equivalence, and the Z3 oracle path. Query planning has structural cache
  keys, replay-checked target-support slicing, and query-plan telemetry in
  benchmark artifacts. ADR-0006 records the Phase 4 bit-order convention and
  circuit/CNF entry contracts. The first Phase 4 code slice adds shared
  LSB-first value-to-bits helpers in `axeyum-ir` and an `axeyum-aig`
  graph/evaluator with deterministic structural hashing. The initial
  bit-lowering slice adds `axeyum-bv` for constants, symbols, Boolean
  connectives, BV bitwise operators, equality, `ite`, `bvcomp`,
  concat/extract, zero/sign extension, `bvneg`, `bvadd`, `bvsub`, and
  unsigned/signed comparisons, `bvshl`, `bvlshr`, `bvashr`, and constant
  rotates, with explicit term-bit and symbol-input maps. The CNF layer adds
  `axeyum-cnf` for simple Tseitin encoding from AIG, DIMACS I/O, CNF
  evaluation, and lift maps from CNF variables back through AIG literals. AIGER
  debug export is implemented as deterministic ASCII `aag`. The SAT adapter path
  chooses `rustsat-batsat` through RustSAT (ADR-0007), exposes a small Axeyum CNF
  SAT trait/result/assignment surface, solves raw CNF and the committed DIMACS
  micro corpus through BatSat, and replay-checks satisfying assignments through
  CNF variables, AIG node values, reconstructed symbol models, and original-term
  evaluator replay. The Phase 4 exit audit records completed gates and explicit
  deferrals: multiplication/division/remainder lowering, pure-Rust benchmark
  artifact telemetry until Phase 5, binary AIGER import/export, and proof-backed
  UNSAT. The first Phase 5 slice adds `SatBvBackend` in `axeyum-solver`: a
  native-free `SolverBackend` implementation for the supported QF_BV subset
  that composes query terms, `axeyum-bv` lowering, `axeyum-cnf` Tseitin
  encoding, `rustsat-batsat`, model reconstruction, deterministic model
  completion for unconstrained symbols, and evaluator replay before accepting
  `sat`. Unsupported lowering operators return structured
  `SolverError::Unsupported` with no oracle fallback. `axeyum-bench` now
  selects `--backend sat-bv|z3`; artifact version 11 records backend kind,
  node and CNF admission budgets, submitted query-plan mode, replay policy,
  replay-refinement round and batch limits, adaptive-batch policy/backoffs,
  refinement selection policy, optional Z3 oracle comparison, harness jobs,
  and per-instance backend stats including bit-blast/CNF timing, AIG
  nodes/inputs, and CNF variables/clauses.
  The Phase 5 public supported-slice
  differential
  baseline is recorded: under a
  1000-node admission budget, the current pure Rust path proves one public
  `sat` instance, classifies 112 larger instances as structured `unknown`, has
  zero unsupported/errors/soundness alarms, and agrees with Z3 on the one
  compared decision. A guarded-admission rerun raises the node budget to 5000
  only with explicit CNF variable/clause caps; it preserves the same one public
  decision and cleanly exposes the next candidate's CNF blow-up as
  `EncodingBudget`, so this is a diagnostics/safety improvement rather than a
  support expansion. A replay-refinement query-plan mode now solves sliced
  plans, replays models against the full query, adds failed assertions' support
  sets, and accepts `sat` only after full replay; on the public slice it
  recovers the same one decision but does not expand decisions. A
  legacy-guided encoding pass added directional signed comparisons plus sparse
  CNF encoding for private XOR and mux AIG shapes, following the same broad
  idea as Bitwuzla's AIG-to-CNF ITE recognition while keeping Axeyum's lift maps
  explicit. A follow-up sparse-CNF pass now encodes private AND trees and
  OR-of-private-AND shapes directly, tracks generated clause duplicates
  deterministically, encodes only the root-reachable AIG subgraph while still
  replaying all AIG nodes, and uses root-only polarity to omit redundant
  Tseitin directions where replay remains checkable. The next sparse-CNF pass
  now recognizes positive root-only AND trees whose leaves are private XOR
  helpers, emits bounded direct parity/equality clauses for those leaves, and
  replays the skipped XOR AIG nodes from their children. The immediate
  MobileDevice replay-refine target now advances through six replay failures
  to a seventh support set and stays below the variable cap at 5,353 variables,
  but still stops at 20,784 clauses against the committed 20,000-clause cap. A
  single-target relaxed-cap diagnostic shows this is close enough that
  admission can be raised deliberately: at 30,000 clauses and a 10s timeout,
  the MobileDevice target reaches a replayed `sat` result and agrees with Z3.
  The full public relaxed-admission artifact now expands the supported slice to
  two public `sat` decisions with no soundness alarms, but BatSat takes about
  6.4s on the MobileDevice SAT call in the 8-worker public run versus about
  0.9s for Z3. A follow-up exact-target relaxed replay-refinement diagnostic
  keeps the same two public decisions, records artifact version 9, eliminates
  node-budget unknowns in that profile, and leaves all 111 remaining unknowns
  as `EncodingBudget`; it improves the diagnostic surface but confirms the
  next work is still reducing clause/SAT cost so support expansion is not only
  bought with timeout and admission increases. An artifact version 10 adaptive
  exact-target diagnostic backs off the refinement batch when the added block
  exceeds encoding budgets; it keeps the same two public decisions and zero
  soundness alarms, but moves all remaining unknowns to precise near-cap
  `EncodingBudget` frontiers. A measured 8,500-variable sweep still leaves all
  111 remaining unknowns as `EncodingBudget`, so cap increases alone are now
  known to chase the frontier rather than expand support on this slice. A
  follow-up artifact version 11 selector diagnostic chooses failed replay
  assertions by smallest individual DAG shape instead of source order; it
  materially reduces several frontiers but still leaves the public slice at two
  decisions. Artifact version 12 now records the bounded plan-aware selection
  option and current root-direct assertion CNF encoder behavior. The
  root-direct pass removes assertion-only root variables, but same-cap and
  8,500-variable public sweeps still leave the public slice at two decisions,
  so the next support expansion still needs deeper encoding reduction, SAT cost
  reduction, or a stronger refinement-selection policy. A follow-up
  singleton budget-skip experiment was rejected: the close
  `StringMatching/string1x16.3._bit8_na6_nr3_paired.smt2` profile returned to
  the honest v12 frontier at 8,001 CNF variables after removing the skip loop,
  and a 12,000-variable/60,000-clause diagnostic still chased the frontier to
  12,063 variables rather than completing replay. Replay-refinement now maps
  full-query replay failures back to the corresponding rewritten assertion
  target, so `--rewrite default` can be combined with replay-refine planning
  without false replay-cycle soundness alarms; on the same close
  `StringMatching` diagnostic this is soundness-clean but still stops at the
  same 8,001-variable frontier. An AIG-local cleanup pass now simplifies
  absorption/consensus patterns and condition-aware mux branches before CNF
  encoding. It reduces some exposed pressure -- for example the MobileDevice
  decided target falls from 6,065 variables/24,631 clauses to 6,015
  variables/24,405 clauses, and `StringMatching/string1x16.3` advances from
  16 to 18 replay-refinement rounds before budget -- but the full public
  same-cap diagnostic remains at 2 `sat` decisions and 111
  `EncodingBudget` unknowns. A bounded CNF subsumption experiment was rejected
  after it failed to reduce the near-miss clause frontier and significantly
  increased CNF encoding time. Artifact version 13 now adds
  `--refine-select smallest-plan-greedy`, a bounded replay-refinement selector
  that rescans candidate failed assertions after each selected target so the
  adaptive-backoff prefix is planned as a growing batch. The exact-target
  scoring path now avoids rebuilding full `QueryPlan`s and uses direct target
  term statistics, which also keeps the existing plan-aware selector cheaper.
  Focused `StringMatching/string1x16.3` diagnostics show modest frontier
  pressure reduction (`8005` variables / `25518` clauses after 20 rounds vs.
  `8013` / `25958` for `smallest-plan-dag` and `8017` / `25687` for
  `smallest-dag` under the same 1s focused profile), but this is not yet a
  public support expansion.
- Git: work is on `main`. Check live cleanliness with
  `git status --branch --short` when resuming; the last packaged hardening
  commit before this planning pass was `49c3a83`.
- Supporting scaffold: corpus tier directories (`corpus/micro|client`
  committed, `corpus/public` gitignored), dependabot (cargo + actions
  weekly), CHANGELOG, .editorconfig, CITATION.cff, PR template, justfile
  (`just check`), docs link checker (`scripts/check-links.sh`, also a CI
  job); 23 reference repos cloned locally (incl. proving horizon: cvc5,
  vampire, eprover, lean4, ethos, lean-smt, nanoda_lib).
- Public corpus fetcher works: `scripts/fetch-corpus.sh` (verified Zenodo
  sources — SMT-LIB 2024 QF_BV/QF_ABV, HWMCC'24 BTOR2, SAT Comp 2024 main);
  QF_ABV fetched and extracted locally (3.4 GB under `corpus/public/`).
- Phase 2 public baseline recorded 2026-06-11:
  [bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json](bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json)
  over SMT-LIB 2024 non-incremental `QF_BV/20221214-p4dfa-XiaoqiChen`
  (113 files, timeout 1000 ms, Z3 4.13.3.0, corpus hash
  `021a6a885828fd6e`, config hash `149d3992edbc7617`, artifact version 3):
  3 sat, 0 unsat,
  110 unknown/timeouts, 0 unsupported, 0 errors, 3 status agreements,
  0 disagreements, 0 model replay failures, PAR-2 mean 1.960 s. The
  artifact includes source provenance, selected family list, shape metrics,
  query-plan telemetry, and empty unsupported/error triage lists. Its
  first-assertion slice probe records 113 sliced instances, 755,480 dropped
  terms, DAG nodes from 8,706,521 to 336,691, and tree nodes from 58,335,915
  to 2,307,699. Reproduce with `just bench-public-qfbv-baseline` after
  fetching `qf_bv`.
- Phase 3 rewrite baseline recorded 2026-06-11:
  [bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json](bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json)
  over the same public QF_BV slice with `--rewrite default` (artifact version
  3, config hash `017207bdf942f35b`): 113 files, 3 sat, 110 unknown/timeouts,
  0 unsupported, 0 errors, 3 status agreements, 0 disagreements,
  0 model replay failures, 0 rewrite decision changes, 0 sat/unsat conflicts,
  PAR-2 mean 1.961 s. The default canonicalizer changed all 113 instances,
  applied 255,551 `bool.and_identity.v1` rules, reduced total DAG nodes from
  8,706,521 to 8,450,857 (2.94%), and reduced total tree nodes from
  58,335,915 to 57,824,813 (0.88%). The artifact also carries the same
  query-plan telemetry as the no-rewrite baseline: 113 sliced first-assertion
  probes and 755,480 dropped terms. Reproduce with `just
  bench-public-qfbv-rewrite` after fetching `qf_bv`.
- Phase 5 public `sat-bv` differential baseline recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 5, backend
  `sat-bv`, Z3 comparison enabled, timeout 1000 ms, node budget 1000, corpus
  hash `021a6a885828fd6e`, config hash `de49a48fe0141b11`): 113 files, 1 sat,
  0 unsat, 112 structured unknowns from node-budget admission, 0 unsupported,
  0 errors, 0 status disagreements, 0 model replay failures, 1 Z3 oracle
  decision agreement, 0 oracle disagreements, 112 oracle skips, PAR-2 mean
  1.983 s. The decided instance is
  `Composition/simple_bit8_na1_nr1_twocond.smt2`, with 310 AIG inputs,
  6,761 AIG nodes, 6,760 CNF variables, 19,421 CNF clauses, 7.1 ms
  bit-blasting, and 2.2 ms CNF encoding. The first unknown is
  `Composition/compose.p2._bit8_na6_nr3_paired.smt2` with
  `NodeBudget: query has 22012 DAG nodes, budget 1000`. Reproduce with
  `just bench-public-qfbv-sat-bv-compare` after fetching `qf_bv`.
- Phase 5 guarded-admission `sat-bv` differential run recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 7, backend
  `sat-bv`, Z3 comparison enabled, timeout 1000 ms, full query plan, node
  budget 5000, CNF variable budget 7000, CNF clause budget 20000, corpus hash
  `021a6a885828fd6e`, config hash `bce5c5f92923baf7`): 113 files, 1 sat,
  0 unsat, 112 structured unknowns (111 `NodeBudget`, 1 `EncodingBudget`),
  0 unsupported, 0 errors, 0 status disagreements, 0 model replay failures,
  1 Z3 oracle decision agreement, 0 oracle disagreements, 112 oracle skips,
  PAR-2 mean 1.983 s. The decided instance remains
  `Composition/simple_bit8_na1_nr1_twocond.smt2`, with 310 AIG inputs,
  6,539 AIG nodes, 3,904 CNF variables, 12,170 CNF clauses, 6.8 ms
  bit-blasting, and 2.6 ms CNF encoding. The newly admitted next candidate is
  safely refused before SAT solve:
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` reports
  `EncodingBudget: CNF has 11906 variables, budget 7000` after 773 AIG
  inputs, 20,431 AIG nodes, 11,906 CNF variables, and 37,865 CNF clauses.
  Reproduce with `just bench-public-qfbv-sat-bv-guarded` after fetching
  `qf_bv`.
- Phase 5 replay-refinement diagnostic run recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 7, backend
  `sat-bv`, Z3 comparison enabled, timeout 1000 ms, query plan
  `replay-refine`, 16 refinement rounds, node budget 5000, CNF variable budget
  7000, CNF clause budget 20000, corpus hash `021a6a885828fd6e`, config hash
  `cfb590ef5acd7763`): 113 files, 1 sat, 0 unsat, 112 structured unknowns
  (95 `EncodingBudget`, 17 `NodeBudget`), 0 unsupported, 0 errors, 0 status
  disagreements, 0 model replay failures, 1 Z3 oracle decision agreement, 0
  oracle disagreements, 112 oracle skips, PAR-2 mean 1.984 s. The mode
  recovers the known `Composition/simple_bit8_na1_nr1_twocond.smt2` decision
  after 11 refinement rounds and full replay. It reduces submitted query shape
  substantially across the public slice (8,706,521 original DAG nodes to
  364,804 submitted DAG nodes; 753,562 dropped terms) but still does not decide
  the MobileDevice targets under the current CNF caps. On the immediate
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` target, sparse CNF
  lets replay-refinement expose a fourth support set before budget refusal:
  83 submitted terms, 881 DAG nodes, 374 AIG inputs, 13,033 AIG nodes, 7,888
  CNF variables, and 25,197 CNF clauses. A relaxed diagnostic at CNF caps
  9000/30000 exposes a fifth support set and still refuses at 9,414 variables,
  so the next bottleneck remains encoding growth rather than a SAT timeout.
  This closes the "replayable query-planning/model-extension" hypothesis for
  the immediate Phase 5 gate unless paired with additional encoding/SAT
  improvements.
  Reproduce with `just bench-public-qfbv-sat-bv-replay-refine` after fetching
  `qf_bv`.
- Phase 5 exact-target relaxed replay-refinement diagnostic run recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 9, backend
  `sat-bv`, Z3 comparison enabled, timeout 10000 ms, query plan
  `replay-refine-exact`, 64 refinement rounds, batch size 64, node budget
  5000, CNF variable budget 8000, CNF clause budget 30000, 8 corpus workers,
  corpus hash `021a6a885828fd6e`, config hash `51c2fa6f2d4029b2`): 113 files,
  2 sat, 0 unsat, 111 structured unknowns (all `EncodingBudget`), 0
  unsupported, 0 errors, 0 status disagreements, 0 model replay failures, 2
  Z3 oracle decision agreements, 0 oracle disagreements, 111 oracle skips, and
  PAR-2 mean 19.680 s. The mode reduces submitted public query shape from
  8,706,521 original DAG nodes to 237,924 submitted DAG nodes and removes
  `NodeBudget` unknowns from this diagnostic profile, but it does not expand
  the public decision count beyond the relaxed support-slice artifact. The
  MobileDevice decision reaches full replay with 6,302 CNF variables, 25,020
  clauses, 8 refinement rounds, 3,301 ms BatSat solve time, and 1,097 ms Z3
  oracle solve time. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact` after fetching `qf_bv`.
- Phase 5 adaptive exact-target replay-refinement diagnostic run recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 10, backend
  `sat-bv`, Z3 comparison enabled, timeout 10000 ms, query plan
  `replay-refine-exact`, adaptive batch enabled, 64 refinement rounds, maximum
  batch size 64, node budget 5000, CNF variable budget 8000, CNF clause budget
  30000, 8 corpus workers, corpus hash `021a6a885828fd6e`, config hash
  `a55c720512d0570b`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, 111 oracle skips, and PAR-2 mean 19.680 s. The run does not
  expand the public decision count, but all 111 remaining unknowns perform
  adaptive backoff (661 total backoffs, max 6 per instance) and end at precise
  near-cap encodings instead of coarse batch cliffs: the largest final unknown
  is `TCP/tcp_full_bit16_na13_nr4_paired.smt2` at 8,495 CNF variables and
  29,059 clauses. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive` after fetching
  `qf_bv`.
- Phase 5 adaptive exact-target 8,500-variable admission sweep recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k5-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k5-30k-r64-b64-j8.json)
  over the same public slice (artifact version 10, config hash
  `987a97e59bb26f91`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, and PAR-2 mean 19.680 s. Raising the variable cap from 8000
  to 8500 under adaptive batching did not move the bottleneck to BatSat
  timeouts or expand public decisions; the remaining cases again stop just past
  the new cap (for example `compose.p3` at 8,506 variables and `string1x16.3`
  at 8,501 variables), with one clause-cap near miss
  (`mobiledevice_bit8_na6_nr3_twocond.smt2` at 8,422 variables and 30,193
  clauses). This confirms that cap increases alone are now chasing the
  replay-refinement frontier and the next support expansion needs encoding
  reduction or a better refinement-selection policy. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-cnf8k5` after
  fetching `qf_bv`.
- Phase 5 root-direct/smallest-DAG adaptive exact-target replay-refinement
  diagnostic run
  recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  over the same public slice (artifact version 12, backend `sat-bv`, Z3
  comparison enabled, timeout 10000 ms, query plan `replay-refine-exact`,
  adaptive batch enabled, refinement selection `smallest-dag`, 64 refinement
  rounds, maximum batch size 64, node budget 5000, CNF variable budget 8000,
  CNF clause budget 30000, 8 corpus workers, config hash
  `7a3d9688adaa7703`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, and PAR-2 mean 19.734 s. Version 12 removes dedicated CNF
  variables for assertion-only AIG roots and records the bounded
  `smallest-plan-dag` selector option; the public run remains
  soundness-clean but still does not expand support. Final unknowns range from
  8,001 to 8,491 CNF variables; the largest same-cap frontier is
  `StringMatching/string4x16.4._bit16_na6_nr4_paired.smt2` at 8,491
  variables/29,191 clauses. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest` after
  fetching `qf_bv`.
- Phase 5 root-direct/smallest-DAG adaptive 8,500-variable admission sweep
  recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k5-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k5-30k-r64-b64-j8.json)
  over the same public slice (artifact version 12, config hash
  `ae175e9a94773059`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, and PAR-2 mean 19.736 s. With root-direct encoding and the
  selector enabled, raising the variable cap to 8,500 again moves rather than
  removes the frontier: the remaining unknowns range from 8,144 to 8,827
  variables, and no instance moves to `Timeout` or replayed `sat`. This keeps
  the next work centered on encoding reduction and stronger refinement
  selection rather than broader cap increases. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest-cnf8k5`
  after fetching `qf_bv`.
- Phase 3 exit audit recorded 2026-06-11:
  [phase3-exit-audit](docs/research/08-planning/phase3-exit-audit.md)
  ties the roadmap exit criteria to concrete evidence: generated rewrite
  equivalence coverage, manifest guards against default non-denotational
  rewrites, Z3 rewrite differential tests, public rewrite measurement, query
  structural-cache/slicing replay tests, and micro/public query-plan artifact
  telemetry.
- North star recorded 2026-06-10: complete framework for general
  reasoning/logic/proving — see
  [north-star](docs/research/00-orientation/north-star.md), the horizon
  ladder in logics-and-decidability, the roadmap's "Beyond Phase 7"
  markers, and the horizon section of the research-questions register.
  Key landscape facts: Vampire (BSD-3) swept CASC-30 2025; cvc5
  CPC/Eunoia/Ethos is the proof-production leader; nanoda is the Rust
  Lean-kernel precedent; no Rust superposition prover or general proof
  kernel exists — that gap is the opportunity.
- Foundational planning refinement recorded 2026-06-11: the roadmap is now
  subordinate to a step-by-step
  [foundational logic and math DAG](docs/research/08-planning/foundational-dag.md)
  from semantics to typed IR, evaluator, import/export, oracle baseline,
  rewrites, bit lowering, CNF, SAT, pure Rust BV, evidence, and later
  theories. Use that note before adding public operators, rewrites,
  encodings, backends, proof artifacts, or logic fragments.
- Workspace: `axeyum-ir`, `axeyum-aig`, `axeyum-bv`, `axeyum-cnf`,
  `axeyum-query`, `axeyum-rewrite`, `axeyum-solver`, `axeyum-smtlib`, and
  `axeyum-bench`, edition 2024, MSRV 1.85, workspace lints (`unsafe_code`
  denied, clippy pedantic). CI workflow covers fmt, clippy, tests,
  micro-corpus benchmark smoke, MSRV check, rustdoc, cargo-deny, and docs
  links.
- Project metadata: README, CONTRIBUTING, CLAUDE.md, dual MIT/Apache-2.0
  licenses, deny.toml, rustfmt.toml.
- References: 23 solver/checker repos shallow-cloned into `references/`
  (gitignored; reproducible via `scripts/fetch-references.sh`).
- Decisions: [ADR-0001 vertical slice first](docs/research/09-decisions/adr-0001-vertical-slice-first.md),
  [ADR-0002 ground-up identity, oracle as bootstrap](docs/research/09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md),
  [ADR-0003 M0 IR representation](docs/research/09-decisions/adr-0003-m0-ir-representation.md),
  [ADR-0004 defer the second native backend](docs/research/09-decisions/adr-0004-defer-second-native-backend.md),
  [ADR-0005 Phase 3 query/evidence/rewrite contracts](docs/research/09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md),
  [ADR-0006 Phase 4 bit-order/lowering entry contract](docs/research/09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md),
  and [ADR-0007 first pure Rust SAT adapter](docs/research/09-decisions/adr-0007-first-pure-rust-sat-adapter.md)
  are **accepted**. ADR-0002 settles the Z3 question: the pure Rust stack
  (including a custom SAT core) is the product; the linked oracle is
  scaffolding with a planned demotion path (backend → differential oracle →
  CI cross-check). ADR-0004 keeps Z3 as the only Phase 2/3 native oracle and
  defers Bitwuzla/other linked backends until Phase 5 needs concrete
  differential or trait-shape pressure. ADR-0005 makes `axeyum-query` the
  assertions/assumptions/scope boundary and `axeyum-rewrite` the manifest
  boundary; default rewrites must remain denotation-preserving until model
  projection is implemented and replay-tested. ADR-0006 makes BV wire vectors
  LSB-first, requires shared value/model conversion helpers, chooses AIG before
  simple Tseitin CNF, and requires explicit lift maps back to original-query
  replay. ADR-0007 chooses `rustsat-batsat` through RustSAT as the first
  pure-Rust CNF/SAT adapter and keeps UNSAT lower-assurance until proof output
  and checking exist.
- Ecosystem facts checked 2026-06-10: stable Rust 1.96; z3 crate 0.20
  removed the `'ctx` lifetime API; varisat unmaintained since 2019 (splr and
  rustsat are the maintained Rust SAT options).
- SAT adapter refresh checked 2026-06-11: `rustsat` 0.7.5 and
  `rustsat-batsat` 0.7.5 declare Rust 1.76 MSRV and fit Axeyum's Rust 1.85
  MSRV; `rustsat-batsat` is pure Rust and is now the first adapter
  (ADR-0007). `splr` and `varisat` remain benchmark/proof-path candidates, not
  the default adapter.
- Local verification for the 2026-06-11 Phase 3 exit hardening pass:
  `cargo fmt --all --check`, `cargo clippy --workspace --all-targets
  --all-features -- -D warnings`, `cargo test --workspace --all-features`,
  `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features
  --no-deps`, `./scripts/check-links.sh`, `git diff --check`, `cargo run -p
  axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite
  default --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The micro
  query-plan summary records 3 files, 1 sliced instance, 1 dropped term, and
  original-to-sliced DAG/tree totals of 14→12 and 15→12. The public QF_BV
  baseline and rewrite artifacts above were regenerated with the current
  schema and both pass with 0 disagreements and 0 model replay failures.
  `cargo deny check` was not run locally because `cargo-deny` is not
  installed; `just --list` was not run because `just` is not installed in this
  environment.
- Local verification for the 2026-06-11 Phase 4 entry-contract pass:
  `./scripts/check-links.sh` and `git diff --check` pass. No Rust code changed
  in this pass.
- Local verification for the 2026-06-11 Phase 4 first implementation slice:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro query-plan summaries remain stable: 3 files, 1 sliced
  instance, 1 dropped term, and original-to-sliced DAG/tree totals of 14→12
  and 15→12. `cargo deny check` was not run locally because `cargo-deny` is
  not installed; `just --list` was not run because `just` is not installed in
  this environment.
- Local verification for the 2026-06-11 Phase 4 structural bit-lowering pass:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro artifacts record 3 files, 2 sat, 1 unsat, 3 status
  agreements, 0 disagreements, 0 model replay failures, 1 sliced instance, 1
  dropped term, and original-to-sliced DAG/tree totals of 14→12 and 15→12.
  The rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 arithmetic/comparison
  bit-lowering pass: `cargo fmt --all --check`, `cargo check --workspace`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro artifacts record 3 files, 2 sat, 1 unsat, 3 status
  agreements, 0 disagreements, 0 model replay failures, 1 sliced instance, 1
  dropped term, and original-to-sliced DAG/tree totals of 14→12 and 15→12.
  The rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 shift/rotate bit-lowering
  pass: `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro artifacts record 3 files, 2 sat, 1 unsat, 3 status
  agreements, 0 disagreements, 0 model replay failures, 1 sliced instance, 1
  dropped term, and original-to-sliced DAG/tree totals of 14→12 and 15→12.
  The rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 CNF layer pass: `cargo fmt
  --all --check`, `cargo check --workspace`, `cargo clippy --workspace
  --all-targets --all-features -- -D warnings`, `cargo test --workspace
  --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
  --all-features --no-deps`, `./scripts/check-links.sh`, `git diff --check`,
  `cargo run -p axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000
  --out /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite
  default --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The micro
  artifacts record 3 files, 2 sat, 1 unsat, 3 status agreements,
  0 disagreements, 0 model replay failures, 1 sliced instance, 1 dropped term,
  and original-to-sliced DAG/tree totals of 14→12 and 15→12. The
  rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 SAT adapter pass: `cargo fmt
  --all --check`, `cargo check --workspace`, `cargo clippy --workspace
  --all-targets --all-features -- -D warnings`, `cargo test --workspace
  --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
  --all-features --no-deps`, `./scripts/check-links.sh`, `git diff --check`,
  `cargo tree -p axeyum-cnf --edges normal`, `cargo run -p axeyum-bench
  --features z3 -- corpus/micro --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite default
  --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The `axeyum-cnf`
  dependency tree contains `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and
  `batsat` 0.6.0 with no native solver or C/C++ build-tool dependency in that
  crate's default tree. The micro artifacts record 3 files, 2 sat, 1 unsat,
  3 status agreements, 0 disagreements, 0 model replay failures, 1 sliced
  instance, and 1 dropped term. The rewrite-default micro artifact records
  1 changed instance, 1 rewrite application, 0 decision changes, and 0 sat/unsat
  conflicts. `cargo deny check` was not run locally because `cargo-deny` is not
  installed; `just --list` was not run because `just` is not installed in this
  environment.
- Local verification for the 2026-06-11 Phase 4 exit hardening/audit pass:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo tree -p axeyum-cnf --edges normal`, `cargo run -p
  axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite
  default --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The
  `axeyum-aig` suite has 6 tests including deterministic ASCII AIGER export;
  `axeyum-cnf` has 9 tests including the committed DIMACS micro-corpus
  SAT-trait pass and full SAT-to-original-term replay. The `axeyum-cnf`
  dependency tree contains `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and
  `batsat` 0.6.0 with no native solver or C/C++ build-tool dependency in that
  crate's default tree. The micro artifacts record 3 files, 2 sat, 1 unsat, 3
  status agreements, 0 disagreements, 0 model replay failures, 1 sliced
  instance, and 1 dropped term. The rewrite-default micro artifact records 1
  changed instance, 1 rewrite application, 0 decision changes, and 0 sat/unsat
  conflicts. `cargo deny check` was not run locally because `cargo-deny` is not
  installed; `just --list` was not run because `just` is not installed in this
  environment.
- Local verification for the 2026-06-11 Phase 5 first pure-Rust backend slice:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, and `cargo tree -p axeyum-solver --edges normal` all pass.
  The default `axeyum-solver` dependency tree includes `axeyum-bv`,
  `axeyum-cnf`, `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and `batsat` 0.6.0
  with no Z3/native SMT dependency. The new `sat_bv` solver test target has 8
  all-feature tests covering supported SAT/UNSAT, query assertions plus
  assumptions, deterministic model completion, explicit unsupported `BvMul`
  errors, node-budget admission control, layer stats, and Z3 decision
  differential checks. `cargo run -p axeyum-bench -- corpus/micro --backend
  sat-bv --timeout-ms 1000 --out /tmp/axeyum-bench-micro-sat-bv.json`,
  the same run with `--rewrite default --out
  /tmp/axeyum-bench-micro-sat-bv-rewrite.json`, `cargo run -p axeyum-bench
  --features z3 -- corpus/micro --backend z3 --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro-z3.json`, and the same Z3 run with `--rewrite
  default --out /tmp/axeyum-bench-micro-z3-rewrite.json` all pass. Each micro
  run records 3 files, 2 sat, 1 unsat, 3 status agreements, 0 disagreements,
  and 0 model replay failures; rewrite-default runs record 1 changed instance,
  1 rewrite application, 0 decision changes, and 0 sat/unsat conflicts. The
  `sat-bv` artifact is version 4 and includes backend stats such as
  `bit_blast_ms`, `cnf_encode_ms`, `aig_nodes`, `aig_inputs`, `cnf_variables`,
  and `cnf_clauses`; that schema later became version 5 with node-budget
  provenance and optional Z3 oracle comparison, and version 6 with CNF-budget
  and query-plan provenance. `cargo deny check` was not run locally because
  `cargo-deny` is not installed; `just --list` was not run because `just` is
  not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 public supported-slice
  differential baseline: `cargo fmt --all --check`, `cargo check
  --workspace`, `cargo clippy --workspace --all-targets --all-features` with
  `-D warnings`, `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The micro `sat-bv` run with `--compare-z3`,
  `--timeout-ms 1000`, and `--node-budget 1000` passes with 3 files, 2 sat,
  1 unsat, 0 unknown, 0 unsupported/errors, 3 Z3 oracle agreements, 0 oracle
  disagreements, and 0 model replay failures. The public baseline artifact
  above was generated with the new `just bench-public-qfbv-sat-bv-compare`
  command body and passed with 113 files, 1 sat, 112 unknown, 0
  unsupported/errors, 1 Z3 oracle agreement, 0 oracle disagreements, and 0
  model replay failures. `cargo deny check` was not run locally because
  `cargo-deny` is not installed; `just --list` was not run because `just` is
  not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 guarded-admission/CNF-budget
  diagnostics pass: `cargo fmt --all --check`, `cargo check --workspace`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. Focused `cargo check -p axeyum-bench --features
  z3` and `cargo test -p axeyum-solver --test sat_bv --features z3` pass; the
  `sat_bv` target has 11 tests including timeout classification and CNF-budget
  refusal before SAT solve. The micro v6 `sat-bv` run with `--compare-z3`,
  `--timeout-ms 1000`, `--node-budget 1000`, `--cnf-var-budget 7000`, and
  `--cnf-clause-budget 20000` passes with 3 files, 2 sat, 1 unsat, 0 unknown,
  0 unsupported/errors, 3 Z3 oracle agreements, 0 oracle disagreements, and 0
  model replay failures. The guarded public artifact above was regenerated with
  the current version 6 schema and passed with 113 files, 1 sat, 112 unknown
  (111 `NodeBudget`, 1 `EncodingBudget`), 0 unsupported/errors, 1 Z3 oracle
  agreement, 0 oracle disagreements, and 0 model replay failures. `cargo deny
  check` and the `just` wrapper targets were not run locally because
  `cargo-deny` and `just` are not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 replay-refinement diagnostic
  pass: `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The micro v7 full-plan `sat-bv` run with
  `--compare-z3`, `--timeout-ms 1000`, `--node-budget 1000`,
  `--cnf-var-budget 7000`, and `--cnf-clause-budget 20000` passes with
  3 files, 2 sat, 1 unsat, 0 unknown, 0 unsupported/errors, 3 Z3 oracle
  agreements, 0 oracle disagreements, and 0 model replay failures. The same
  micro run with `--query-plan replay-refine --refine-rounds 16` also passes
  with 3 files, 2 sat, 1 unsat, 3 Z3 oracle agreements, 0 disagreements, and
  0 model replay failures, while exercising one sliced/refined instance. The
  guarded full public artifact was regenerated under artifact version 7 and
  still records 113 files, 1 sat, 112 unknown (111 `NodeBudget`, 1
  `EncodingBudget`), 0 unsupported/errors, 1 Z3 oracle agreement, 0 oracle
  disagreements, and 0 model replay failures. The replay-refine public
  diagnostic artifact records 113 files, 1 sat, 112 unknown (95
  `EncodingBudget`, 17 `NodeBudget`), 0 unsupported/errors, 1 Z3 oracle
  agreement, 0 oracle disagreements, and 0 model replay failures. `cargo deny
  check` and the `just` wrapper targets were not run locally because
  `cargo-deny` and `just` are not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 legacy-guided sparse-CNF pass:
  reviewed cvc5's ITE simplification/removal path and Bitwuzla's AIG-to-CNF
  ITE detection, added directional signed-comparison lowering, a developer
  replay-refinement profile example, and sparse CNF encoding for private
  XOR/mux AIG helper nodes. `cargo fmt --all --check`, `cargo check
  --workspace`, workspace clippy with all targets/all features and
  `-D warnings`, `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"` and `--workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` all pass. Focused
  `cargo test -p axeyum-bv`, `cargo test -p axeyum-cnf`, `cargo test -p
  axeyum-solver --test sat_bv --features z3`, and `cargo check -p
  axeyum-bench --examples --features z3` also pass. The micro full-plan
  `sat-bv` vs Z3 run and the micro replay-refine `sat-bv` vs Z3 run pass. The
  guarded and replay-refine public artifacts above were regenerated and remain
  soundness-clean: 113 files, 1 `sat`, 112 `unknown`, 0
  unsupported/errors/model replay failures/oracle disagreements. The immediate
  MobileDevice replay-refine target improved to 7,888 CNF variables and 25,197
  clauses at the fourth support set, but still exceeds the committed CNF caps.
  `cargo deny check` and the `just` wrapper targets were not run locally because
  `cargo-deny` and `just` are not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 reachable/sparse-CNF follow-up:
  added private AND-tree flattening, direct OR-of-private-AND encoding,
  deterministic generated-clause normalization/deduplication, root-reachable
  CNF planning/allocation/encoding, full-AIG replay for unencoded dead nodes,
  root-only polarity clause trimming, and constant-sign signed-comparison
  simplification. `cargo fmt --all --check`, `cargo check --workspace`,
  workspace clippy with all targets/all features and `-D warnings`,
  `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"` and `--workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` pass. Focused
  `cargo test -p axeyum-bv`, `cargo test -p axeyum-cnf`, and
  `cargo test -p axeyum-solver --test sat_bv --features z3` also pass. The
  immediate MobileDevice replay-refine profile now advances through four
  replay failures to a fifth support set: 141 planned terms, 1,026 submitted
  DAG nodes, 677 AIG inputs, 14,845 AIG nodes, 5,727 CNF variables, and 21,637
  clauses. A single-target benchmark with the committed
  7000-variable/20000-clause caps remains soundness-clean but still returns
  structured `EncodingBudget`, now on the clause cap rather than the variable cap:
  1 file, 0 sat, 1 unknown, 0 unsupported/errors/model replay failures/oracle
  disagreements. Full public artifact regeneration remains pending until the
  next reduction can plausibly expand the public decision count.
- Local verification for the 2026-06-12 Phase 5 positive-root equality CNF
  pass: added direct bounded parity/equality clauses for positive root-only
  AND-tree leaves backed by private XOR helpers, while keeping skipped XOR AIG
  nodes replayable from their children. `cargo fmt --all --check`, `cargo
  check --workspace`, workspace clippy with all targets/all features and
  `-D warnings`, `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"` and `--workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` pass. Focused `cargo
  test -p axeyum-bv`, `cargo test -p axeyum-cnf`, and `cargo test -p
  axeyum-solver --test sat_bv --features z3` also pass. The micro
  replay-refine `sat-bv` vs Z3 run passes with 3 files, 2 `sat`, 1 `unsat`, 3
  oracle agreements, 0 disagreements, and 0 model replay failures. The full
  public replay-refine run remains soundness-clean but does not expand the
  public decision count: 113 files, 1 `sat`, 112 `unknown` (95
  `EncodingBudget`, 17 `NodeBudget`), 0 unsupported/errors/model replay
  failures/oracle disagreements, and 1 Z3 oracle agreement. The immediate
  MobileDevice target now advances through six replay failures to a seventh
  support set before the committed clause cap stops it: 175 planned terms,
  1,084 submitted DAG nodes, 773 AIG inputs, 16,341 AIG nodes, 5,353 CNF
  variables, and 20,784 clauses. This is encoding progress and better
  diagnostics, not a public support expansion yet.
- Local diagnostic for the 2026-06-12 Phase 5 relaxed-cap check: the immediate
  MobileDevice replay-refine target was rerun as a one-file corpus with node
  budget 5000, CNF variable budget 7000, Z3 comparison enabled, and unchanged
  replay checking. At 25,000 clauses and a 1s timeout it builds a
  6,292-variable/24,963-clause SAT instance but returns structured `Timeout`.
  At 25,000 clauses and a 10s timeout it advances one more replay failure and
  then hits `EncodingBudget` at 25,046 clauses. At 30,000 clauses and a 10s
  timeout it reaches checked `sat` after 9 replay failures/10 rounds with
  6,312 CNF variables, 25,054 clauses, 19,351 AIG nodes, 47 ms model lift,
  5,295 ms BatSat solve time, full replay, and Z3 agreement. This proves
  raising the clause cap is a viable admission lever, but does not by itself
  close the performance gap.
- Local diagnostic for the 2026-06-12 Phase 5 benchmark parallelism and
  relaxed public run: `axeyum-bench` now has an explicit `--jobs N` corpus
  worker knob. `--jobs 1` remains the default; `--jobs 2` on the committed
  micro corpus preserved sorted file order, outcomes, oracle agreements, and
  replay cleanliness compared with `--jobs 1` apart from expected timing/hash
  changes. The committed artifact
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json)
  records the full public relaxed-admission profile: artifact version 8,
  113 files, 2 `sat`, 111 `unknown` (94 `EncodingBudget`, 17 `NodeBudget`),
  0 unsupported/errors/model replay failures/oracle disagreements, 2 Z3 oracle
  agreements, 8 corpus workers, 10s timeout, node budget 5000, CNF variable
  budget 7000, and CNF clause budget 30000. The newly decided public instance
  is `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2`, with 6,312 CNF
  variables, 25,054 clauses, 10 replay-refinement rounds, 6,429 ms BatSat
  solve time in the contended public run, and 923 ms Z3 oracle solve time.
  Local validation for this pass: `cargo fmt --all --check`, `cargo check -p
  axeyum-bench --examples --features z3`, `cargo clippy -p axeyum-bench
  --all-targets --features z3 -- -D warnings`, micro `sat-bv` vs Z3 runs with
  `--jobs 1` and `--jobs 2`, `cargo clippy --workspace --all-targets
  --all-features -- -D warnings`, `cargo test --workspace --all-features`,
  `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` all pass. `cargo deny
  check` was not run locally because `cargo-deny` is not installed.
- Local diagnostic for the 2026-06-12 Phase 5 exact-target relaxed
  replay-refinement run: `axeyum-bench` now supports
  `--query-plan replay-refine-exact`, which submits only exact target
  assertions per refinement round and relies on full original-query replay
  before accepting `sat`. `--refine-batch N` can add multiple failed original
  assertions from the same candidate model to the next round. The committed
  artifact
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  records the full public exact-target relaxed profile: artifact version 9,
  113 files, 2 `sat`, 111 `unknown` (all `EncodingBudget`), 0
  unsupported/errors/model replay failures/oracle disagreements, 2 Z3 oracle
  agreements, 8 corpus workers, 10s timeout, node budget 5000, CNF variable
  budget 8000, CNF clause budget 30000, 64 refinement rounds, and batch size
  64. The run reduces submitted public query shape to 237,924 DAG nodes and
  removes the node-budget unknown class for this diagnostic profile, but does
  not expand decisions beyond the version 8 relaxed support-slice artifact.
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` reaches full replay
  with 6,302 CNF variables, 25,020 clauses, 8 refinement rounds, 3,301 ms
  BatSat solve time, and 1,097 ms Z3 oracle solve time. Local validation for
  this pass: `cargo fmt --all --check`, `cargo check -p axeyum-bench
  --examples --features z3`, `cargo test -p axeyum-query`, `cargo clippy -p
  axeyum-bench --all-targets --features z3 -- -D warnings`, micro
  `replay-refine-exact` `sat-bv` vs Z3 with `--jobs 2`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The exact public artifact was regenerated with
  the current harness and remains soundness-clean with the same config hash and
  outcome profile. `cargo deny check` and `just` wrapper targets were not run
  locally because `cargo-deny` and `just` are not installed in this
  environment.
- Local diagnostic for the 2026-06-12 Phase 5 adaptive exact-target
  replay-refinement pass: `axeyum-bench` now supports
  `--refine-adaptive-batch` for replay-refinement modes. The policy is purely
  an admission/refinement heuristic: after a newly added failed-assertion batch
  trips `EncodingBudget`, the harness halves that last addition and retries,
  while still accepting `sat` only after full original-query replay. Artifact
  version 10 records the adaptive flag and per-instance `adaptive_backoffs`;
  the config hash includes the flag. The developer profile helper gained the
  matching `AXEYUM_PROFILE_ADAPTIVE_BATCH=1` mode. Focused diagnostics on
  `StringMatching/string4x16.3._bit16_na6_nr4_paired.smt2` show the static
  batch-64 exact plan jumps to 32,133 CNF variables/74,010 clauses, while
  adaptive batch-64 under the same 8000-variable/30000-clause caps ends at a
  precise 8,147-variable/26,723-clause `EncodingBudget`. The full public
  same-cap adaptive artifact remains soundness-clean but does not expand the
  supported slice: 113 files, 2 `sat`, 111 `unknown`, all unknowns
  `EncodingBudget`, 2 Z3 agreements, 0 model replay failures/oracle
  disagreements. The full public 8,500-variable sweep likewise remains
  soundness-clean with 2 `sat` and 111 `EncodingBudget` unknowns, proving this
  cap increase is not enough to expand support. Local validation for this
  pass: `cargo fmt --all --check`, `cargo check -p axeyum-bench --examples
  --features z3`, `cargo clippy -p axeyum-bench --all-targets --features z3
  -- -D warnings`, adaptive exact micro `sat-bv` vs Z3 with `--jobs 2`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The one-file StringMatching adaptive run and
  both full public adaptive sweeps above pass with zero unsupported/errors,
  model replay failures, or oracle disagreements.
- Local diagnostic for the 2026-06-12 Phase 5 root-direct CNF and
  refinement-selection pass: `axeyum-bench` now supports
  `--refine-select first|smallest-dag|smallest-plan-dag`.
  `first` preserves the artifact version 10 source-order behavior; the new
  `smallest-dag` mode scans replay-failed original assertions, scores them by
  individual `TermStats` (`dag_nodes`, then `tree_nodes`, then `ite_count`,
  then term ID), and chooses the cheapest failed assertions for the next
  refinement batch. The new bounded `smallest-plan-dag` diagnostic first keeps
  a deterministic 64-candidate cheap-score frontier, then re-scores those
  candidates by the resulting sliced plan shape. It is heavier and did not
  diverge usefully from `smallest-dag` through the first eight rounds of the
  close `StringMatching/string2x16.6._bit8_na6_nr3_paired.smt2` diagnostic, so
  it is not the current public default. The config hash includes the selector
  and artifact version 12 records it. The developer profile helper gained
  matching `AXEYUM_PROFILE_REFINE_SELECT` support. Focused profiles show real
  frontier reduction on expensive source-order choices: TCP full falls from
  8,495 variables/29,059 clauses to 8,095 variables/21,622 clauses under the
  same caps, and `compose.p2` falls from 8,068 variables/18,814 clauses to
  8,029 variables/18,632 clauses before the root-direct pass. The root-direct
  CNF encoder removes dedicated variables for assertion-only roots and keeps
  AIG replay intact; focused unit tests cover positive and negative direct
  roots. The full public same-cap v12 artifact remains soundness-clean but
  still records 2 `sat` and 111 `EncodingBudget` unknowns, with remaining
  unknowns from 8,001 to 8,491 variables. The full public 8,500-variable v12
  sweep likewise leaves 2 `sat` and 111 `EncodingBudget` unknowns, with
  remaining unknowns from 8,144 to 8,827 variables and no SAT timeouts. This
  confirms root-direct encoding, smallest-DAG selection, and a moderate cap
  increase are useful diagnostics/pressure reductions but not a support
  expansion. Local validation for this pass: `cargo test -p axeyum-aig -p
  axeyum-cnf`, `cargo check -p axeyum-bench --examples --features z3`,
  micro `sat-bv` vs Z3 replay-refine-exact with
  `--refine-select smallest-plan-dag`, `cargo clippy --workspace
  --all-targets --all-features -- -D warnings`, `cargo test --workspace
  --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
  --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. `cargo deny check` was attempted but
  `cargo-deny` is not installed in this environment.
- Local verification for the 2026-06-12 replay-refinement rewrite-target fix
  and singleton budget-skip rejection: `cargo fmt --all`,
  `cargo check -p axeyum-bench --examples --features z3`, `cargo test -p
  axeyum-cnf`, `cargo test -p axeyum-bench --features z3`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`, and
  `cargo test --workspace --all-features` all pass. The micro
  replay-refine-exact `sat-bv` vs Z3 run passes both with rewrite off and
  with `--rewrite default`, and the one-file rewritten
  `StringMatching/string1x16.3._bit8_na6_nr3_paired.smt2` diagnostic now ends
  as a structured `EncodingBudget` unknown with 0 model replay failures instead
  of a false replay-cycle alarm.
- Local diagnostic for the 2026-06-12 AIG simplification pass: `axeyum-aig`
  now simplifies AND absorption, OR-consensus, and condition-aware mux branches
  while preserving deterministic structural hashing and AIG replay. Focused
  tests cover the new Boolean identities. The final full public
  smallest-DAG/adaptive/exact-target diagnostic at 10s / 5000 nodes /
  8000 CNF variables / 30000 CNF clauses / 8 jobs remains soundness-clean:
  113 files, 2 `sat`, 111 `EncodingBudget` unknowns, 0 unsupported, 0 errors,
  0 model replay failures, and 2 Z3 agreements. Notable frontier changes:
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` is still `sat` with
  6,015 variables and 24,405 clauses; `StringMatching/string1x16.3` reaches
  18 replay-refinement rounds before stopping at 8,017 variables; and
  `StringMatching/string4x8.7._bit8_na6_nr3_paired.smt2` remains a clause
  near-miss at 7,990 variables and 30,003 clauses. The rejected bounded CNF
  subsumption experiment left this clause frontier unchanged while raising
  CNF encode time, so it was removed. Local validation: `just check` could
  not run because `just` is not installed; the underlying gates
  `cargo fmt --all --check`, `cargo clippy --workspace --all-targets
  --all-features -- -D warnings`, `cargo test --workspace --all-features`,
  `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps`,
  and `./scripts/check-links.sh` all pass.
- Local diagnostic for the 2026-06-12 greedy refinement-selector pass:
  `axeyum-bench` now accepts `--refine-select smallest-plan-greedy`, the
  replay-refine profile accepts
  `AXEYUM_PROFILE_REFINE_SELECT=smallest-plan-greedy`, and artifact version 13
  records the new selection policy. A regression test proves the greedy
  selector rescans after each selected failed assertion and can prefer a larger
  individual assertion when it reuses the already-selected subgraph. Focused
  `StringMatching/string1x16.3._bit8_na6_nr3_paired.smt2` diagnostics at
  exact/adaptive/batch-64, 1s timeout, node budget 5000, and CNF caps
  8000/30000 completed quickly after the exact-target scoring shortcut:
  `smallest-plan-greedy` stops at 8,005 variables / 25,518 clauses after 20
  rounds, compared with 8,013 / 25,958 for `smallest-plan-dag` and
  8,017 / 25,687 for `smallest-dag`. The user requested commit/push before a
  full public v13 artifact run, so this remains focused evidence only. Local
  validation after the final selector cleanup: `cargo fmt --all --check`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, and `./scripts/check-links.sh`
  all pass.

## Next Actions

In order; check off and date as completed.

- [x] Review and accept (or amend) ADR-0001 — accepted 2026-06-10.
- [x] Initial commit of `docs/` + `PLAN.md` — 2026-06-10.
- [x] Phase 0: Cargo workspace skeleton (`axeyum-ir`, `axeyum-solver`),
      licenses, CI — 2026-06-10.
- [x] Push `main` to GitHub and confirm CI is green there — 2026-06-10.
- [x] Scaffolding complete — 2026-06-10. All pre-code work is done:
      infrastructure, metadata, documentation, ADRs,
      north-star, LLM integration points), Cargo workspace, CI green,
      CLAUDE.md, corpus skeleton, 20 reference clones. **Everything below
      this line is implementation, not scaffolding** — deliberately deferred
      to the next working session.
- [x] **Milestone M0 (vertical slice) — 2026-06-10.** The ADR-0001 doctest
      passes: `x + 1 == 5` over `BV(8)` solves via `Z3Backend` and the
      ground evaluator confirms the lifted model. `axeyum-ir` has the M0
      operator subset, hash-consed arena, sort-checked builders, and the
      evaluator with exhaustive small-width tests; `axeyum-solver` has the
      trait, symbol-keyed models, and the feature-gated Z3 backend
      (`z3` = system libz3 via pkg-config, `z3-static` = hermetic prebuilt).
      Representation decisions in ADR-0003. All sat results in the test
      harness replay through the evaluator.
- [x] **Phase 1 (typed term core broadened) — 2026-06-10.** Full scalar
      QF_BV operator set (40 operators: arithmetic incl. sdiv/srem/smod,
      shifts, all 8 comparisons, nand/nor/xnor/comp, extensions, rotates,
      implies) with SMT-LIB edge-case semantics; SMT-LIB-style pretty
      printer (`render`); exhaustive small-width evaluator tests (22 IR
      tests); and a differential suite where Z3 confirms the evaluator on
      *every* input at width 3 for every operator — three independent
      implementations (evaluator, i64 test reference, Z3) agree.
- [x] **Observability & resource governance — 2026-06-11.** Per the
      query-cost-control and observability notes: `TermStats` sharing
      metrics in `axeyum-ir` (DAG vs saturating tree size — the 2^k blowup
      detector — depth, support, ite/mul-div counts); structured
      `Unknown(UnknownReason{kind, detail})` so budget exhaustion can never
      read as unsat; `SolverConfig` budgets (timeout, deterministic
      `resource_limit`→Z3 rlimit, `memory_limit_mb`, `node_budget`
      admission control); `SolveStats` layer-attributed telemetry via
      `last_stats()` incl. Z3 statistics. Tested: 2^200 chain saturates,
      node budget refuses with diagnosis, rlimit yields classified Unknown.
- [x] **Phase 2, SMT-LIB leg — 2026-06-11.** New `axeyum-smtlib` crate:
      iterative QF_BV-slice parser (declare/define-fun, let scoping, n-ary
      and indexed operators, hex/bin/indexed literals, `:status` ground
      truth, clear Unsupported errors for arrays/UF/incremental) and
      sharing-preserving writer (shared nodes as 0-ary define-funs; the
      2^100 bomb exports linearly — tested). Parse→Z3→evaluator-replay and
      export round-trip conformance tests; corpus smoke test ingests real
      local SMT-LIB files (runtime-skipped on CI).
- [x] **Phase 2 benchmark harness and hardening pass — 2026-06-11.**
      `axeyum-bench` runs `.smt2` corpora through `Z3Backend`, replays every
      `sat` model through the evaluator, checks `:status` agreement, reports
      PAR-2, emits versioned JSON artifacts with config/corpus hashes,
      backend version, hardware note, seed, shape metrics, and layer timings.
      Committed `corpus/micro/*.smt2` fixtures now run in CI. Review fixes
      also made SMT-LIB parsing stricter, escaped writer identifiers, avoided
      generated-name collisions, made extension-width arithmetic overflow-safe,
      scoped Z3 memory limits, and added model-lift telemetry.
- [x] **Planning refinement: foundational DAG — 2026-06-11.** Added the
      logic/math dependency DAG, support matrix, phase gates, web/reference
      refresh gates, and Z3-demotion criteria to make future work proceed from
      semantics and evidence obligations rather than broad milestones alone.
- [x] **Phase 2 public baseline — 2026-06-11.** Recorded
      `bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json` for the
      SMT-LIB 2024 non-incremental QF_BV `20221214-p4dfa-XiaoqiChen` family:
      113 parsed/solved-through-trait files, 0 unsupported, 0 errors,
      0 status disagreements, 0 model replay failures. Timeouts are classified
      as structured `unknown`, not failures. State-retention conformance stays
      deferred until the incremental/query lifecycle API exists.
- [x] **Phase 3 entry contracts — 2026-06-11.** Added `axeyum-query` for
      assertions, assumptions, and scopes; added `axeyum-rewrite` for the
      stable manifest contract; added `SolverBackend::check_query`; accepted
      ADR-0005 for the layered evidence envelope and the rule that
      equisatisfiability-only rewrites remain disabled until model projection is
      implemented and replay-tested.
- [x] **Phase 3 first canonicalizer — 2026-06-11:** implemented the first
      denotation-preserving rewrite rules in `axeyum-rewrite` (start with
      simple Boolean/BV identities and constant folds), registered them in the
      manifest, proved evaluator equivalence with focused tests, and added a
      Z3 oracle differential check for rewritten queries.
- [x] **Phase 3 rewrite measurement and corpus gate — 2026-06-11:** run the default
      canonicalizer through benchmark/corpus plumbing, record nodes-in/out and
      rule-application counts in artifacts, compare Z3 answers and model replay
      against original assertions on the public QF_BV baseline slice, and
      record measured rewrite effect before assuming a win.
- [x] **Phase 3 query planning — 2026-06-11:** add structural cache keys and
      constraint slicing against `axeyum-query`, with projection/replay tests
      proving planned models satisfy the original query contract.
- [x] **Phase 3 exit hardening — 2026-06-11:** added deterministic generated
      rewriter equivalence coverage, exercised query-planner cache/slice
      metrics on micro and public corpus artifacts, and recorded the Phase 3
      exit audit before starting Phase 4 bit-order/circuit work.
- [x] **Phase 4 entry contract — 2026-06-11:** recorded the bit-order convention,
      shared value-to-wires conversion plan, circuit/AIG entry shape, and
      CNF/lift-map evidence obligations before implementing public
      bit-lowering APIs in
      [ADR-0006](docs/research/09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [x] **Phase 4 first implementation slice — 2026-06-11:** added shared LSB-first
      value-to-bits/bits-to-value helpers, an AIG graph skeleton with
      deterministic structural hashing, and evaluator tests before adding
      public bit-lowering APIs.
- [x] **Phase 4 initial bit lowering — 2026-06-11:** added the first term-to-AIG
      lowering module for Bool/BV constants, symbols, and cheap bitwise
      operators, with evaluator-vs-AIG tests and explicit term-bit lift-map
      data.
- [x] **Phase 4 structural bit lowering — 2026-06-11:** added `eq`, `ite`,
      concat/extract, zero/sign extension, and `bvcomp` lowering with
      evaluator-vs-AIG tests and lift-map replay.
- [x] **Phase 4 arithmetic/comparison bit lowering — 2026-06-11:** added `bvneg`,
      `bvadd`, `bvsub`, and the unsigned/signed comparison operators with
      evaluator-vs-AIG tests and lift-map replay.
- [x] **Phase 4 shift/rotate bit lowering — 2026-06-11:** added `bvshl`, `bvlshr`,
      `bvashr`, `rotate_left`, and `rotate_right` lowering with
      evaluator-vs-AIG tests and lift-map replay; keep multiplication,
      division, and remainder deferred until their encoding gate is explicit.
- [x] **Phase 4 CNF layer — 2026-06-11:** added `axeyum-cnf` with simple Tseitin
      encoding from AIG, DIMACS I/O, CNF evaluation, and lift maps from CNF
      variables back through AIG literals to original term bits.
- [x] **Phase 4 SAT adapter path — 2026-06-11:** refreshed/evaluated RustSAT,
      `rustsat-batsat`, direct BatSat, splr, and varisat; accepted ADR-0007 for
      `rustsat-batsat` through RustSAT as the first pure-Rust adapter; added a
      CNF SAT trait/result/assignment surface; solved raw DIMACS/CNF through the
      adapter; and replayed satisfying assignments through CNF variables, AIG
      node values, reconstructed symbol models, and original terms.
- [x] **Phase 4 exit hardening and audit — 2026-06-11:** added deterministic
      ASCII AIGER debug export and smoke tests, added a committed DIMACS micro
      corpus solved through the SAT trait, recorded default dependency evidence
      for the pure-Rust SAT path, explicitly deferred benchmark artifact layer
      telemetry to Phase 5 where real pure-Rust backend timings exist, and wrote
      the Phase 4 exit audit.
- [x] **Phase 5 first SAT-backed BV backend slice — 2026-06-11:** added
      `SatBvBackend` in `axeyum-solver`, composing supported term-to-AIG
      lowering, Tseitin CNF, the BatSat adapter, model reconstruction,
      deterministic model completion, evaluator replay, structured unsupported
      errors for unsupported lowering operators, Z3 differential tests for
      supported decisions, and `axeyum-bench --backend sat-bv|z3` artifact
      version 4 backend layer telemetry, later extended by artifact version 5
      oracle-comparison and node-budget provenance.
- [x] **Phase 5 public supported-slice differential baseline — 2026-06-12:**
      ran the pure Rust backend against the public
      `QF_BV/20221214-p4dfa-XiaoqiChen` slice with Z3 comparison, recorded
      unsupported/error triage separately from soundness failures, and wrote
      artifact version 5 evidence with 1 compared-and-agreeing public `sat`
      instance, 112 node-budget `unknown`s, 0 unsupported/errors, 0 oracle
      disagreements, and 0 model replay failures.
- [x] **Phase 5 guarded admission and CNF-budget diagnostics — 2026-06-12:**
      added explicit CNF variable/clause budgets, cooperative BatSat timeout
      classification, artifact version 7 query-plan/replay-policy provenance,
      and regenerated the public `sat-bv` vs Z3 guarded run at node budget 5000
      with CNF caps. The run still decides one public `sat`; it classifies the
      next admitted candidate as `EncodingBudget` before SAT solve and keeps
      unsupported, unknown, and soundness triage distinct.
- [x] **Phase 5 replay-refinement diagnostic — 2026-06-12:** added
      `axeyum-bench --query-plan replay-refine`, which iteratively solves a
      sliced support plan, replays each `sat` model against the full original
      query, adds the failed assertion support, and accepts `sat` only after
      full replay. The public diagnostic artifact still decides one public
      `sat`, but it proves replayable slicing alone is not enough to expand the
      supported public slice under current CNF caps and BatSat timeout.
- [x] **Phase 5 legacy-guided sparse-CNF pass — 2026-06-12:** reviewed cvc5
      ITE simplification/removal and Bitwuzla AIG-to-CNF ITE recognition,
      implemented directional signed comparisons plus sparse CNF for private
      XOR/mux AIG helper nodes, added a replay-refine profiling example, and
      regenerated guarded/replay-refine public artifacts. The pass materially
      reduces CNF size and lets the immediate MobileDevice target refine one
      support round further, but it still does not expand public decisions under
      the committed 7000-variable/20000-clause caps.
- [x] **Phase 5 reachable/sparse-CNF follow-up — 2026-06-12:** added private
      AND-tree flattening, direct OR-of-private-AND encoding, deterministic
      clause normalization/deduplication, root-reachable CNF encoding with
      full-AIG replay for dead nodes, root-only polarity clause trimming, and
      constant-sign signed-comparison simplification. The immediate
      MobileDevice replay-refine target now reaches the fifth support set and
      stays below the variable cap at 5,727 variables, but still stops at
      21,637 clauses against the committed 20,000-clause cap; this is progress
      on encoding growth, not a public support expansion yet.
- [x] **Phase 5 positive-root equality CNF pass — 2026-06-12:** added bounded
      direct parity/equality clauses for positive root-only AND-tree leaves
      backed by private XOR helpers, with skipped XOR AIG nodes reconstructed
      by replay. The immediate MobileDevice replay-refine target now passes the
      fifth and sixth support sets under the committed caps, then stops at the
      seventh support set with 5,353 variables and 20,784 clauses. The full
      public replay-refine run remains soundness-clean but still decides one
      public instance, so this is not a support expansion yet.
- [x] **Phase 5 relaxed-cap diagnostic — 2026-06-12:** verified that simply
      raising the committed clause cap is technically sound on the immediate
      MobileDevice target when paired with replay/model checking: 30,000
      clauses and a 10s timeout reaches `sat` with Z3 agreement. Keep the
      default public caps unchanged until a full public-slice run justifies the
      admission change.
- [x] **Phase 5 relaxed public support-expansion diagnostic — 2026-06-12:**
      added deterministic corpus-level `--jobs` support to `axeyum-bench` and
      recorded the full public replay-refine run at 10s / 5000 nodes /
      7000 CNF variables / 30000 CNF clauses / 8 jobs. The run expands the
      public pure-Rust supported slice to 2 `sat` decisions with Z3 agreement
      and no soundness alarms, while leaving 94 `EncodingBudget` and
      17 `NodeBudget` unknowns.
- [x] **Phase 5 exact-target relaxed replay-refinement diagnostic —
      2026-06-12:** added exact-target replay-refinement planning and
      `--refine-batch`, recorded artifact version 9 at 10s / 5000 nodes /
      8000 CNF variables / 30000 CNF clauses / 64 rounds / batch 64 / 8 jobs,
      and regenerated the public artifact with the current harness. The run
      keeps the supported public slice at 2 `sat` decisions with Z3 agreement
      and no soundness alarms, removes `NodeBudget` unknowns from this
      diagnostic profile, and leaves all 111 remaining unknowns as
      `EncodingBudget`.
- [x] **Phase 5 adaptive exact-target replay-refinement diagnostic —
      2026-06-12:** added explicit `--refine-adaptive-batch`, artifact version
      10 adaptive-policy/backoff telemetry, matching developer profile support,
      and reproducible public just targets. The same-cap public run keeps the
      supported slice at 2 `sat` decisions but converts the remaining
      `EncodingBudget` failures from coarse batch cliffs into near-cap final
      encodings; an 8,500-variable sweep still leaves 111 `EncodingBudget`
      unknowns, so this is diagnostic precision, not support expansion.
- [x] **Phase 5 smallest-DAG refinement-selection diagnostic — 2026-06-12:**
      added explicit `--refine-select first|smallest-dag`, artifact version 11
      selector telemetry, matching developer profile support, and reproducible
      public just targets. The selector reduces several source-order
      `EncodingBudget` frontiers but the same-cap and 8,500-variable public
      runs remain at 2 `sat` decisions and 111 `EncodingBudget` unknowns, so
      this is useful pressure reduction, not support expansion.
- [x] **Phase 5 root-direct assertion CNF and plan-aware selector diagnostic —
      2026-06-12:** removed dedicated CNF variables for assertion-only AIG
      roots while preserving full AIG/original-term replay, added
      `--refine-select smallest-plan-dag` as a bounded 64-candidate
      plan-aware diagnostic, bumped artifacts to version 12, and regenerated
      the public smallest-DAG 8,000- and 8,500-variable sweeps. Both remain
      soundness-clean at 2 `sat` decisions and 111 `EncodingBudget` unknowns,
      so this is not a support expansion.
- [x] **Phase 5 replay-refinement cleanup and rewrite-safe targeting —
      2026-06-12:** rejected the singleton budget-skip experiment after
      focused 8,000- and 12,000-variable diagnostics showed it chases the
      frontier rather than completing replay; kept artifact schema at version
      12; added rewrite-safe replay-refinement target mapping so original
      replay failures refine the corresponding rewritten assertion; and added
      a regression test for that mapping. The close rewritten `StringMatching`
      diagnostic is now soundness-clean but still stops at the same
      `EncodingBudget` frontier, so this is correctness/diagnostic hardening,
      not support expansion.
- [x] **Phase 5 AIG simplification diagnostic — 2026-06-12:** added
      condition-aware mux cleanup plus OR-consensus/absorption simplifications
      in `axeyum-aig`, measured the closest StringMatching frontiers, rejected
      a bounded CNF subsumption experiment that only slowed CNF encoding, and
      reran the full public smallest-DAG adaptive exact-target profile. The
      pass reduces selected AIG/CNF pressure but leaves the public slice at
      2 `sat` decisions and 111 `EncodingBudget` unknowns, so it is not a
      support expansion.
- [x] **Phase 5 greedy selector diagnostic — 2026-06-12:** added
      `--refine-select smallest-plan-greedy` and matching profile support,
      fast-pathed exact-target plan scoring, bumped artifacts to version 13,
      and measured a modest focused `StringMatching/string1x16.3` frontier
      reduction. The user requested commit/push before a full public v13 run,
      so this is focused selector evidence, not a support expansion.
- [ ] **NEXT: Phase 5 supported-slice expansion:** use the version 11
      smallest-DAG selector artifacts, the version 12 root-direct selector
      artifacts, the version 13 greedy selector diagnostic, the version 10
      adaptive exact-target artifacts, the version 9 static exact-target
      artifact, the version 8 relaxed support-slice artifact, and the version 7
      conservative artifacts
      to expand beyond two decided public instances without merely raising
      timeouts or caps. Reduce the remaining AIG/CNF/SAT cost exposed by
      replay-refinement, especially the near-cap `EncodingBudget` frontiers in
      StringMatching, TCP, MobileDevice, VideoConf, and Composition; optimize
      the current lowering/encoding; improve refinement-target selection beyond
      single-assertion shape; or implement the next missing high-value BV
      encoding. Rerun the public `sat-bv` vs Z3 comparison and keep
      unsupported, unknown, performance, and soundness triage distinct.
- [ ] Then follow the roadmap phase by phase; each phase has explicit
      exit criteria.

## How To Resume Work (for a human or an agent)

1. Read **Status** and **Next Actions** above.
2. Read the [roadmap](docs/research/08-planning/roadmap.md) for the current
   phase and its exit criteria.
3. Read the
   [foundational DAG](docs/research/08-planning/foundational-dag.md) before
   adding operators, rewrites, encodings, backends, evidence artifacts, or
   logic fragments.
4. Before changing architecture, check
   [open questions](docs/research/08-planning/research-questions.md) and
   [decision records](docs/research/09-decisions/README.md) — decisions close
   as ADRs, not as silent code choices.
5. New research notes start from
   [templates/research-note.md](docs/research/templates/research-note.md).
6. When a session ends: update **Status**, re-order **Next Actions**, and
   note any new ADRs here.

## Standing Rules

- The pure Rust core builds with no C/C++ dependency; native backends
  (Z3, Bitwuzla) are feature-gated leaf crates.
- Semantics, model/proof lifting, and replay/checker routes must be explicit
  before a new operator, rewrite class, encoding, backend, or logic fragment
  becomes public surface.
- Every transformation layer ships with its check (evaluator equivalence,
  round trips, lift maps) and a differential test once an oracle exists.
- Expensive bets are gated by the
  [benchmarking methodology](docs/research/08-planning/benchmarking-and-performance-methodology.md)
  — no custom CDCL core until its gate fires.
- `unknown` is a first-class result. Determinism (same input, same seed, same
  output) is a public API promise.

## Map

| Where | What |
|---|---|
| [docs/research/README.md](docs/research/README.md) | Research index and reading order. |
| [docs/research/08-planning/roadmap.md](docs/research/08-planning/roadmap.md) | Phased plan with exit criteria and gates. |
| [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md) | Logic/math dependency DAG and layer contracts. |
| [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md) | Open question register. |
| [docs/research/09-decisions/](docs/research/09-decisions/README.md) | ADRs: how questions get closed. |
| `crates/` | Cargo workspace: `axeyum-ir`, `axeyum-aig`, `axeyum-bv`, `axeyum-cnf`, `axeyum-query`, `axeyum-rewrite`, `axeyum-solver`, `axeyum-smtlib`, `axeyum-bench`. |
| [CLAUDE.md](CLAUDE.md) | Agent guidance: session protocol, commands, hard rules. |
| [references/](references/README.md) | Gitignored reference clones; `scripts/fetch-references.sh`. |
