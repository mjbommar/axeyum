# CryptoMiniSat, MiniSat, varisat, and splr — XOR reasoning and the Rust SAT field (2026-09-09)

Scope: four clones.

| Solver | Path | SHA | Commit/release date seen | Language | LOC (src, rough) | License |
|---|---|---|---|---|---|---|
| CryptoMiniSat | `references/cryptominisat/` | `7ae1b4a74259cdce223a584281fb8f090bbd3eed` | 2026-09-02 (HEAD) | C++ | ~70,000 | MIT (build/no-copyright-header files); GPL-ish elsewhere per `LICENSE.txt` header — see file |
| MiniSat | `references/minisat/` | `37dc6c67e2af26379d88ce349eb9c4c6160e8543` | 2013-09-25 (HEAD) | C++ | ~2,900 | MIT |
| varisat | `references/varisat/` | `33e876937c5d22305664e9ae5601484b25cec23f` | 2022-11-02 (HEAD, shallow clone — single commit visible) | Rust | ~13,000 | dual MIT/Apache-2.0 |
| splr | `references/splr/` | `90fa3ad3ee3aa352ac1df1e9aa03a748315ebcb7` | 2026-08-22 (HEAD) | Rust | ~12,500 | MPL-2.0 |

All four clones are `--depth 1`; for varisat and splr the single visible commit
date is the tip of the default branch at fetch time, not full history — noted
where it matters below.

## Summary

- **CryptoMiniSat is architecturally two solvers glued together**: a MiniSat/
  CaDiCaL-lineage CDCL core over ordinary clauses, plus a second reasoning
  system — occurrence-list XOR recovery (`xorfinder.cpp`) feeding an
  incrementally-watched Gaussian-elimination engine (`gaussian.cpp`,
  `matrixfinder.cpp`) that is wired directly into unit propagation
  (`propengine.cpp:164-290`), not run as a one-shot preprocessing pass.
- **XOR recovery (`xorfinder.cpp`) reconstructs XOR gates from plain CNF
  clauses** by combinatorial matching: for a clause of size k it looks for the
  complementary `2^(k-1) - 1` other clauses needed to certify an XOR
  constraint, using occurrence lists sorted by watch-list size
  (`xorfinder.cpp:180-229`, `findXorMatch` at `:255`).
- **Gaussian elimination is the Han & Jiang (CAV 2012) "simplex way" design**
  (`gaussian.h:1-8` cites the paper by name): each connected component of XOR
  constraints becomes one matrix (`matrixfinder.cpp`), rows are packed as
  64-bit-word bitsets (`packedrow.h`/`packedmatrix.h`), and propagation uses a
  row-watching scheme directly analogous to two-watched-literal — each row
  tracks one responsible pivot column plus one non-responsible watched column
  (`gausswatched.h`, `gaussian.h:104-107`).
- **XOR reasoning is NOT justified in plain DRAT.** CryptoMiniSat's proof
  output is its own extended format, "FRAT", with native rules for XOR steps
  (`addx`, `delx`, `implyclfromx`, `implyxfromcls`, `finalx`, `finalcl` —
  `frat.h:38`). Turning that into something a standard checker can verify is a
  **three-tool external pipeline outside CryptoMiniSat itself**: FRAT →
  `frat-xor` (a *separate* repo, `meelgroup/frat-xor`) elaborates to XLRUP →
  `cake_xlrup` (CakeML-verified) checks it (`README_VERIFIER.md`). Plain
  `drat-trim` cannot check a CryptoMiniSat XOR proof.
- **Even FRAT logging has known holes around XOR/occurrence passes in this
  source tree**: `xorfinder.cpp:104` has `assert(false && "TODO FRAT")` inside
  `clean_equivalent_xors` (called only when FRAT is *disabled* —
  `find_xors():150-152` — so equivalent-xor dedup and FRAT logging are
  mutually exclusive), and `occsimplifier.cpp:2404-2408` marks `occ-lit-rem` as
  "TODO FRAT -- broken UNSAT actually!! :(" and disables it outright when
  `frat->enabled()`. Two occurrence-simplification passes are silently skipped,
  not proof-gapped-but-run, when proof logging is on.
- **XOR finding runs strictly after BVE in both default schedules**
  (`solverconf.cpp:281-296`: `startup = "...,occ-bve,occ-xor"`;
  `nonstartup = "...,occ-bve,occ-bva,occ-ternary-res,occ-xor,card-find,..."`).
  Variable elimination can destroy XOR structure before the XOR finder ever
  sees it; CryptoMiniSat accepts that ordering cost deliberately.
- **CLAUDE.md's varisat claim is half stale.** "varisat is effectively
  unmaintained (last release 2019)" undercounts by a year — varisat's own
  `CHANGELOG.md` shows a 0.2.2 release on 2020-09-09, and this shallow clone's
  HEAD commit (a merged PR) is dated 2022-11-02 — but the *unmaintained*
  characterization still holds relative to splr. "The only Rust SAT solver
  with DRAT/LRAT proof output" is now **false**: splr (`references/splr/`,
  MPL-2.0) ships a `--certify` flag that writes DRAT
  (`src/config.rs:4,51,122`, `src/solver/conflict.rs:157-161`) and is under
  active development — `ChangeLog.md`'s latest entry is version 0.19.0 dated
  2026-08-22, the same month as this comparison. splr does not do LRAT, only
  DRAT, so varisat is still the only one of the two with an LRAT/native-format
  route and an in-tree checker.
- **varisat's proof story is the richest of the four projects that produce
  proofs at all** (CryptoMiniSat's is richer in reasoning power — XOR-native —
  but needs an external repo to check). varisat has its own native proof
  format (hash-based, "inspired by LRAT" —
  `manual/src/formats/varisat-proofs.md`), exports DRAT and LRAT/CLRAT from
  it, and ships an in-tree checker crate (`varisat-checker`). Converting its
  own format to LRAT is cheap because the native format already carries most
  of what LRAT needs; converting arbitrary DRAT to LRAT (what a DRAT-only
  producer forces on a downstream checker) is the expensive direction the
  format was designed to avoid (`manual/src/formats/lrat-proofs.md:15-20`).
- **varisat's engine is classic MiniSat-2.1-lineage**: blocking-literal
  watchlists (`prop/watch.rs:1-33`, citing the MiniSat 2.1/SAT Race 2008 paper
  by name) and textbook VSIDS with exponential decay
  (`decision/vsids.rs:28-104`). splr's engine is materially more modern:
  Learning-Rate-Based (LRB) variable rewarding as the default scheme with a
  VMTF fallback (`assign/learning_rate.rs:5-9`), trail-saving
  (`assign/trail_saving.rs`), and an EMA-driven Luby restart/reduce/vivify/
  rephase trigger unified under one O(1) Luby iterator whose correctness was
  proved in Lean4 (`ChangeLog.md`, 0.19.0 entry) — a proof-adjacent detail
  worth noting given this project's own kernel work.
- **axeyum's native CDCL core sits architecturally between the two**: VSIDS +
  Luby restarts + LBD-tiered `reduce_db` + blocking-literal watches + 1-UIP
  analysis (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:74`) is the
  same *family* of design as varisat (MiniSat/CaDiCaL lineage) rather than
  splr's LRB/VMTF/trail-saving line. axeyum emits DRAT/LRAT natively
  (`proof_sat.rs`, ADR-0012) and has its own backward-checking LRAT elaborator
  (`drat_backward.rs`, ADR-0382), which is closer in *shape* to varisat's
  DRAT→LRAT-from-native-format economy than to a plain DRAT-only producer —
  but axeyum, unlike varisat, has no in-tree independent proof-format
  documentation and no dedicated checker crate; `check_lrat`/`check_drat` live
  in the same crate as the producer.
- **MiniSat (2013 clone) is the ancestor everything here still cites by
  name**: two-watched-literal propagation with blocking literals, VSIDS
  activity-heap decisions, 1-UIP conflict analysis with `litRedundant`
  minimization, geometric/Luby restarts, activity-based `reduceDB`. No proof
  output of any kind (`grep -rn "drat\|proof\|certif" references/minisat` —
  zero hits outside this search's own absence). `SimpSolver` adds occurrence-
  list subsumption, self-subsuming resolution ("asymm"), and bounded variable
  elimination — the direct ancestor of CryptoMiniSat's `occsimplifier.cpp` and
  (independently, per lane C1) of CaDiCaL's inprocessing. Lane C1 covers
  CaDiCaL/Kissat depth; this file only notes MiniSat as their and
  CryptoMiniSat's shared root.

## Schema

### A — Input front end

| Solver | Format(s) | Parser | Rejected / silently ignored |
|---|---|---|---|
| CryptoMiniSat | DIMACS CNF, extended with native XOR lines (`x -1 2 3 0`) | `dimacsparser.h` (templated streaming parser) | n/a — not determined here; not the focus axis for this file |
| MiniSat | DIMACS CNF only | `core/Dimacs.h`, header-only | No XOR, no incrementality format |
| varisat | DIMACS CNF via `varisat-dimacs` crate; also a programmatic `CnfFormula` API | `varisat-dimacs/src/lib.rs` | No XOR extension |
| splr | DIMACS CNF | `src/cnf/` | No XOR extension found (`grep -rn "^x \| x " references/splr/src` not run — n/a, out of scope for this axis) |

### B — Preprocessing (before search)

| Solver | Passes, in order | Model reconstruction |
|---|---|---|
| CryptoMiniSat | Schedule strings, e.g. startup: `sub-impl, occ-backw-sub, scc-vrepl, breakid, occ-bve, occ-xor` (`solverconf.cpp:281-286`); nonstartup adds `occ-bva, occ-ternary-res, card-find` before `occ-xor` (`:288-296`). BVE always precedes XOR recovery in both schedules. | `OccSimplifier::extend_model`/`SolutionExtender` (`occsimplifier.cpp:209`) reconstructs eliminated variables from saved elimination clauses (`print_elimed_clauses_reverse`, `:112`) |
| MiniSat (`SimpSolver`) | Asymmetric-branching clause shrink ("asymm"), subsumption, self-subsuming resolution, bounded variable elimination, one round, no XOR (`simp/SimpSolver.h:71-105`) | `eliminated` bitmap + saved elimination clauses, extended at model time |
| varisat | Not inventoried in depth here (out of this file's XOR/Rust-field focus); `varisat/src/unit_simplify.rs` exists | n/a — not read |
| splr | `src/processor/simplify.rs`, `eliminate.rs`, `subsume.rs`, `vivify.rs` (`src/cdb/vivify.rs`) | not read in depth |

### C — Core SAT engine

| Solver | Decision heuristic | Restarts | Clause-DB reduction | Watches | Phase saving | Chrono backtrack |
|---|---|---|---|---|---|---|
| CryptoMiniSat | VSIDS-family (not re-derived here beyond confirming `activity` fields exist; out of this file's depth budget) | glucose-style, config-driven | occurrence-based + activity, `clean_clause`/`complete_clean_clause` (`occsimplifier.cpp:304,400`) | blocking-literal watchlists (same lineage as MiniSat 2.1) | present (not cited to line) | present, not cited to line — `[undetermined]`, would need `searcher.cpp` restart/backtrack section |
| MiniSat | VSIDS activity heap (`Solver.h:196,205`) | Luby or geometric, `restart_first`/`restart_inc` (`:141-142`) | activity-based `reduceDB` (`:253`) | two-watched-literal (`watches`, `:203`) | not in this 2013 snapshot's `Solver.h` decl list — `[undetermined]` | none |
| varisat | Classic VSIDS, `f32` activity, exponential decay (`decision/vsids.rs:28-104`) | not read in depth | `clause/db.rs:48` `ClauseDb`, LBD/glue-based (`glue.rs` present) — not fully re-derived | blocking-literal watchlists explicitly modeled on MiniSat 2.1/SAT Race 2008 (`prop/watch.rs:1-33`) | not read | not found — no `chrono` module |
| splr | LRB (Learning-Rate-Based) default, VMTF fallback, both variants live side by side and are selectable (`assign/learning_rate.rs:5-9`) | Luby, unified O(1) iterator also driving reduce/vivify/rephase (`ChangeLog.md` 0.19.0) | `cdb/db.rs`, "revise `ClauseDB::reduce` to remove much more clauses, can run at any decision level" (0.19.0 changelog) | `cdb/watch_cache.rs` | `assign/trail_saving.rs` — a distinct, more recent phase-saving variant | not found |

### D — Inprocessing (during search)

| Solver | Passes | Schedule trigger | Proof survival |
|---|---|---|---|
| CryptoMiniSat | Full `execute_simplifier_strategy` re-run (`occsimplifier.cpp:2341`), which includes `occ-xor` — XOR recovery itself is periodically re-run as inprocessing, not only preprocessing | `max_num_simplify_per_solve_call = 25` (`solverconf.cpp:280`), `num_conflicts_of_search` geometric increase (`:277-278`) | FRAT entries per pass; two passes (`occ-lit-rem`, and dedup inside `xorfinder`) are **disabled** rather than proof-gapped when FRAT logging is on (see Summary) |
| MiniSat | None beyond initial `SimpSolver::eliminate` (no periodic re-simplification found) | n/a | n/a — no proof output |
| varisat | Not read in depth (out of scope for this file's focus) | — | — |
| splr | `processor/` passes are scheduled by the same unified Luby trigger as restarts (0.19.0 changelog) | Luby-sequence based | DRAT `d`/add lines ordered so deletion is logged "before you garbage-collect what justified it" (`solver/conflict.rs:157-161` comment) — a correctness invariant stated inline, not proven by a distinct checker in this crate |

### E — Encoding / bit-blasting

n/a for all four — these are propositional CDCL solvers with a native XOR
extension (CryptoMiniSat) or none (MiniSat, varisat, splr). None does
term-level bit-blasting; that is axeyum's `axeyum-bv`/`axeyum-aig` layer, with
no counterpart in this lane's four solvers.

### F — Theory solvers

n/a in the SMT sense — all four are pure SAT engines. CryptoMiniSat's "theory"
in the loose sense is GF(2) linear algebra for XOR/parity constraints
(`gaussian.cpp`), detailed under Gaussian elimination in the Summary. None of
the four has arithmetic, array, or string theory solvers.

### G — Theory combination

n/a — no theory combination layer in any of the four; CryptoMiniSat's XOR
reasoning is combined with CDCL directly inside `propengine.cpp`
(`gmatrices[matnum]->find_truths` called from the same propagation loop as
clause watches, `propengine.cpp:164-290`), not through a Nelson-Oppen-style
interface. It is closer to axeyum's `xor_cdcl.rs` (a competitive in-search
XOR decider) than to a CDCL(T) theory-combination loop.

### H — Quantifiers

n/a for all four — propositional only.

### I — Model production

| Solver | Mechanism | Self-validation |
|---|---|---|
| CryptoMiniSat | `SolutionExtender` walks saved elimination/gate clauses in reverse to fix eliminated/gate variables (`occsimplifier.cpp:112,209`) | not determined here |
| MiniSat | Direct trail read (`SimpSolver` extends via saved elim clauses) | not determined here |
| varisat | not read in depth | — |
| splr | `src/solver/validate.rs` exists as a distinct module — suggests a dedicated self-check step, not read in depth | plausible but `[undetermined]` at this budget — would need `solver/validate.rs` read |

### J — Proof / certificate production

| Solver | Format(s) | Route | Granularity |
|---|---|---|---|
| CryptoMiniSat | FRAT (native extended DRAT with `addx`/`delx`/`implyclfromx`/`implyxfromcls`/`finalx`/`finalcl` — `frat.h:38`) | `Solver::frat` object threaded through CDCL, occurrence simplification, and Gaussian elimination (`gaussian.cpp` frat call sites listed above) | Per-clause and per-XOR-row, with an `XLRUPFile` class also present in `frat.h:430` for direct XLRUP emission |
| MiniSat | none | — | — |
| varisat | Native format, DRAT (ASCII+binary), LRAT/CLRAT | `varisat-internal-proof` crate defines the native format; exported to DRAT/LRAT | Per-clause, incremental-solving-aware ("Proofs for incremental solving", `CHANGELOG.md` 0.2.1) |
| splr | DRAT only (`--certify`, `config.rs:4,51,122`) | Written during conflict analysis / clause deletion (`solver/conflict.rs:157-161`) | Per-clause |

### K — Proof checking

| Solver | Checker |
|---|---|
| CryptoMiniSat | None in-tree for FRAT. External 3-tool pipeline: `frat-xor` (elaborator, separate repo) → `cake_xlrup` (CakeML-verified checker, same repo) — `README_VERIFIER.md` |
| MiniSat | n/a — no proof |
| varisat | In-tree `varisat-checker` crate, works over the native/hash-based format directly | 
| splr | None found in-tree for DRAT; presumably external (`drat-trim`), per `ChangeLog.md`'s 0.1.0 verification notes citing drat-trim explicitly |

### L — Interpolation

Not found in any of the four. `[undetermined]` beyond a `grep -rn interpolat`
returning nothing in any of the four trees (positive control: the same grep
against `crates/axeyum-cnf` finds `propositional_interpolant*`, so the pattern
is not silently failing).

### M — Optimization

CryptoMiniSat: not inventoried at this budget beyond noting `main.cpp`/
`main_common.cpp` exist as separate concerns; no MaxSAT-specific source file
name found under `src/`. MiniSat/varisat/splr: none — plain SAT only.

### N — Incrementality

| Solver | Mechanism |
|---|---|
| CryptoMiniSat | `ipasir.cpp`/`ipasir.h` — implements the IPASIR incremental interface |
| MiniSat | None in the 2013 core; assumptions exist (`analyzeFinal`) but no push/pop |
| varisat | Explicit "Proofs for incremental solving" (`CHANGELOG.md` 0.2.1) — incrementality with proof support was a specific design goal |
| splr | Not read in depth — `[undetermined]`, would need `src/solver/mod.rs` |

### O — Parallelism

CryptoMiniSat: `main_mpi.cpp`, `datasync.cpp`/`datasyncserver.cpp` present —
portfolio/clause-sharing infrastructure exists. Not read in depth. MiniSat:
none. varisat/splr: none found.

### P — Resource limits and determinism

CryptoMiniSat: extensive per-pass time limits as config fields
(`xor_finder_time_limitM`, `maxTime`, `global_timeout_multiplier` —
`solverconf.h:279`, referenced throughout `occsimplifier.cpp`). Not compared
line-for-line against axeyum's own budget model here — out of this file's
depth budget; see lane C1/L1 area files for axeyum's own resource-limit
inventory.

## Gaps against axeyum

### They have, we do not

| Capability | Their implementation (cited) | Our status (cited) | Rough gap size |
|---|---|---|---|
| XOR extraction wired into the *default*, always-on search path, re-run as inprocessing | CryptoMiniSat `occ-xor` token runs both at startup and non-startup schedule points (`solverconf.cpp:281-296`), inside `execute_simplifier_strategy` | `xor_extract.rs` is `WIRED` but only reached inside `maybe_xor_cdcl_fallback`, gated on `config.xor_cdcl_fallback` (default `false`, `backend.rs:397`) — off by default (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:134`) | Large — this is a config-default gap, not a missing-code gap: the machinery exists on our side but is never reached unless a non-default flag is set |
| Gaussian elimination integrated as a first-class propagation source inside the CDCL loop itself (row-watching, on every unit-propagate call) | `propengine.cpp:164-290`, `gaussian.cpp` `find_truths`/`eliminate_col` | `xor_propagate.rs` runs as a CONFIG-GATED (`cnf_inprocessing`, also default `false`) *pass*, appending Gaussian-implied units to the formula rather than participating in the watch/propagate loop; explicitly **skipped when `prove_unsat` is set** because a Gaussian-implied unit is not RUP (`01-sat-core-and-cnf.md:133`) | Large — architectural, not just a default-off flag: CryptoMiniSat's Gaussian engine is inside propagation; ours is a separate pre-pass that must step aside from proof mode |
| A watched-row incremental Gaussian elimination structure comparable to `xor_matrix.rs`'s `IncrementalXorMatrix`, but actually reachable from production | `gaussian.cpp`/`packedrow.h`, wired (above) | `xor_matrix.rs`'s `IncrementalXorMatrix` (1,595 lines) is **BENCH-ONLY** (`01-sat-core-and-cnf.md:137`) | Large — near-equivalent code exists on our side and is unreachable |
| A dedicated, richer proof-format ecosystem for XOR steps (even if external): native `addx`/`delx` proof rules, plus a from-scratch elaborator+checker toolchain | `frat.h:38`, `README_VERIFIER.md` | `xor_drat.rs` proves XOR-derived unsat by reducing to a **width-capped** (`MAX_XOR_WIDTH`, ADR-0035) plain-DRAT refutation of a Gaussian conflict subset — no native XOR proof step type; large XOR widths cannot be certified this way at all | Medium — different strategy (avoid the problem vs. solve it with a bespoke format), each with its own ceiling; CryptoMiniSat's ceiling is proof-checker availability (an external repo must exist and build), ours is `MAX_XOR_WIDTH` |
| An LRB/VMTF-class modern variable-activity heuristic as an available option | splr `assign/learning_rate.rs` | axeyum's core is VSIDS-only per `01-sat-core-and-cnf.md:74` | Medium |
| Trail-saving phase-saving variant | splr `assign/trail_saving.rs` | Not found in axeyum's core description | Small-medium |
| A dedicated, documented native proof format cheaper to convert to LRAT than raw DRAT | varisat native format (`manual/src/formats/varisat-proofs.md`) | axeyum emits DRAT/LRAT directly from the CDCL core (ADR-0012) with its own backward LRAT elaborator (`drat_backward.rs`, ADR-0382) — different design, not a strict subset, see Not comparable | n/a as a gap — different approach, not absence |

### We have, they do not

This table is honestly short: these are four narrowly-scoped propositional
solvers (three of them SAT-only with no theory layer at all), and axeyum is a
multi-theory SMT stack sitting on top of a comparable propositional core. A
feature-by-feature list would mostly restate "we have SMT-LIB parsing,
arithmetic, arrays, strings, quantifiers, a proof kernel — they don't", which
is a scope difference, not a capability finding. Narrowed to the propositional
layer these four actually compete on:

| Capability | Evidence |
|---|---|
| A DRAT *backward* (core-first) checker as a distinct, documented module | `drat_backward.rs`, 2,866 lines, ADR-0382 — none of the four here has a distinct backward-checking mode; CryptoMiniSat's checking is entirely external, varisat's checker works forward over its native format, splr apparently relies on external `drat-trim` |
| An LRAT elaborator/checker living in the same crate as the SAT core, so the trust anchor and the producer are co-located in one dependency-light Rust crate with no C/C++ leaf and no external-repo round trip | `lrat.rs` (2,026 lines), `crates/axeyum-cnf` has zero required non-workspace dependencies for this path | CryptoMiniSat needs `frat-xor` + `cake_xlrup`, both external; splr has no in-tree LRAT at all |
| A DRAT memory/resource model with an explicit route-choice and decline mechanism (`DratMemoryModel`, `MemoryBudget`, `BackwardCheckOutcome`) | `drat_resource.rs`, 1,000 lines | No equivalent named module found in any of the four |
| Alethe proof export/check for cross-checking against an independent (Carcara) toolchain, from the same propositional core | `alethe.rs`, 5,152 lines | None of the four targets Alethe |

## Not comparable

- **CryptoMiniSat's FRAT vs. axeyum's DRAT/LRAT are different bets on the same
  problem** (how to prove search steps that are not naturally RUP, XOR chief
  among them). CryptoMiniSat extends the *proof format* with native rules and
  pushes the burden onto an external elaborator+checker toolchain it does not
  control the release cadence of (`meelgroup/frat-xor`, a separate repo not
  cloned here). axeyum keeps the format plain DRAT/LRAT and instead
  *restricts* what it will certify (`MAX_XOR_WIDTH`, and the outright decline
  to emit a Gaussian-implied unit when `prove_unsat` is set). Neither
  dominates: CryptoMiniSat can certify wider XOR reasoning but the checking
  story leaves the CryptoMiniSat repo entirely; axeyum's checking story stays
  fully in-tree but caps what it will attempt.
- **MiniSat is not a fair peer on almost any axis** — it is a 2013,
  ~2,900-line teaching/research core with no proof output, no incrementality
  beyond assumptions, and no XOR support. It is included here only as the
  shared ancestor CryptoMiniSat's `occsimplifier.cpp` and varisat's
  `prop/watch.rs` both cite by name and design.
- **varisat's and splr's "engine" is not directly size-comparable to
  axeyum's `proof_sat.rs`** (8,333 lines) because both Rust solvers split the
  same functionality across many small files/crates (varisat: 7 workspace
  crates; splr: `assign/`, `cdb/`, `processor/`, `solver/` as separate
  modules) rather than one flat file. A line-count comparison would
  mischaracterize modularity as capability difference.
- **CryptoMiniSat's occurrence-simplification suite (`occsimplifier.cpp`,
  5,433 lines) is far broader than what this file evaluated** (BVE, BVA, gate
  detection, ternary resolution, cardinality-constraint finding, SLS,
  breakid-based symmetry breaking) — this file covers only the XOR-adjacent
  slice (schedule ordering, BVE-before-XOR) relevant to Job 1; a full
  occurrence-simplifier comparison against axeyum's CNF inprocessing
  (`inprocess.rs`, ADR-1750) is lane-C1/L1 territory and is not duplicated
  here.

## Confidence

**Solid source reads** (function/struct bodies read directly, not inferred):
XOR recovery combinatorics (`xorfinder.cpp:52-260`); Gaussian elimination's
propagation-loop wiring (`propengine.cpp:164-290`) and its citation of Han &
Jiang CAV 2012 (`gaussian.h:1-8`); the FRAT proof-rule enum and per-callsite
XOR proof emission (`frat.h:38`, `gaussian.cpp` frat call sites);
`README_VERIFIER.md`'s external three-tool pipeline (read in full); the two
`TODO FRAT` disablement sites (`xorfinder.cpp:104`, `occsimplifier.cpp:2404-
2408`); the default simplification schedules (`solverconf.cpp:281-296`);
varisat's watch-list design and citation (`prop/watch.rs:1-33`) and VSIDS
(`decision/vsids.rs`); splr's LRB/VMTF choice and DRAT `--certify` flag
(`config.rs`, `learning_rate.rs`); both repos' commit/release dates (`git log`
+ `CHANGELOG.md`/`ChangeLog.md`, read directly); MiniSat's absence of proof
output (grep with a positive-control pattern check against axeyum's own tree).

**Inferences from naming/structure, not fully read**: CryptoMiniSat's
restart/chrono-backtracking policy in `searcher.cpp` (named but not traced);
varisat's clause-DB reduction policy (`clause/db.rs` read only at struct
level); splr's incrementality and model-validation modules
(`solver/validate.rs` exists, not read); CryptoMiniSat's MaxSAT/parallelism
surface (`main_mpi.cpp`, `datasync*.cpp` — named, not traced).

**Explicitly `[undetermined]`**: MiniSat 2013's phase-saving presence in
`Solver.h`'s visible declarations; splr's incrementality mechanism; axeyum's
own restart/chrono-backtracking policy is cited from the coordinator's
existing inventory (`01-sat-core-and-cnf.md`) rather than re-derived here —
that file is the authority for axeyum internals in this comparison, per the
method brief.
