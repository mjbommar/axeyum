# ABC and AIGER — AIG-level reasoning (2026-09-09)

Scope: two clones, read-only, no build.

| Project | Path | SHA | Language | Size | LOC (src, `.c`+`.h`) | License |
|---|---|---|---|---|---|---|
| ABC | `references/abc/` | `fbaae01487b05982739a5636df30687f41a10a2d` | C | 56 MB, 1,424 `.c` files | 1,134,209 | Berkeley/Regents-of-UC BSD-style (`references/abc/copyright.txt`) |
| AIGER | `references/aiger/` | `039ec1a2cc37d3093ac35c4b6df65336b346f409` | C | 1.8 MB, 43 `.c` files (top level) | 23,032 | MIT-style, one file (`bliftoaig.c`) under the more restrictive CUDD/BSD license (`references/aiger/LICENSE`) |

ABC bundles several external SAT engines wholesale under `src/sat/`: `cadical`,
`kissat`, `glucose`, `glucose2`, `satoko`, `xsat`, plus its own `bsat`/`bsat2`.
This is not comparable to axeyum's default-build promise of zero C/C++
dependency (ADR-0002) — ABC is a C application that vendors multiple C/C++ SAT
solvers as first-class internal engines, not optional oracles.

## Summary

- **axeyum's AIG layer (`crates/axeyum-aig`, 1,046 lines) does structural
  hashing and *local* algebraic simplification only** — an `AndUniqueTable`
  for hash-consing (`lib.rs:131-233`), constant folding and absorption
  (`simplify_and_by_absorption`, `lib.rs:380-398`), and OR-consensus
  (`simplify_and_by_or_consensus`, `:398-407`). There is no global rewrite
  pass, no cut enumeration, no subgraph library, no refactoring, and no
  balancing command — everything ABC does *after* construction, axeyum does
  only *during* construction, one node at a time, with no re-optimization
  pass over an already-built graph.
- **ABC's DAG-aware AIG rewriting (`src/opt/dar/`, 17,070 lines) is a distinct,
  separately invoked global pass**, not a construction-time simplification:
  `Dar_ManRewrite` (`darCore.c:79`) enumerates k-feasible cuts per node
  (`nCutsMax = 8`, `darCore.c:54`), matches each cut's function against a
  precomputed library of near-optimal small subgraphs
  (`darLib.c`, "Library of AIG subgraphs used for rewriting"), and
  substitutes when the replacement provably saves nodes
  (`nMinSaved`, `darCore.c:56`). `darRefact.c` does a second, complementary
  transform — window extraction + Boolean (bi-)decomposition into a new
  factored form (`Bdc_Man_t`) — that can restructure logic rewrite's
  library-lookup approach cannot reach. `darBalance.c` ("Algebraic AIG
  balancing") restructures the AND-tree to reduce depth between rewrite
  passes. `darResub.c` adds resubstitution against existing nodes. These
  compose into named scripts in `abc.rc`: `resyn` (`"b; rw; rwz; b; rwz; b"`,
  `abc.rc:110`), `resyn2` (`abc.rc:111`), and `compress2`
  (`abc.rc:115`); `dc2` (`Abc_CommandDc2`, `abc.c:18436`, doc string "performs
  combinational AIG optimization") wraps balance+rewrite+refactor in one
  command. None of `resyn`/`resyn2`/`compress2`/`dc2`/rewrite/refactor/balance
  has any counterpart in axeyum.
- **This lane could not find a quantified circuit-size reduction number in the
  source or any in-tree doc.** `darCore.c`/`darLib.c` state parameters
  (`nCutsMax=8`, `nSubgMax=5`) but not benchmark results; ABC ships no
  `doc/` directory in this clone. The technique is the one published as
  "DAG-Aware AIG Rewriting: A Fresh Look at Combinational Logic Synthesis"
  (cited by title in `references/aiger/FORMAT:737`, the AIGER format doc's own
  bibliography) — this lane did not read that paper and is not quoting its
  numbers. **Marked `[undetermined]`**: what % node reduction `resyn2`
  typically achieves; would need the paper or an actual run.
- **ABC's CNF generation for SAT (`src/sat/cnf/`) is technology-mapping-based,
  not per-gate Tseitin.** `Cnf_Derive` (`cnfCore.c`) computes K-input cuts over
  the AIG (`Cnf_Cut` carries an `aArea`/mapping-area field, `cnf.h:70-88`),
  then looks up each cut's exact Boolean function in a precomputed clause
  table derived from minimum sum-of-products forms of all 4-variable functions
  (`cnfData.c`, 4,789 lines; `"Prepares the data for MSOPs of 4-variable
  functions"`, `:4528`). One mapped cut becomes one CNF sub-formula sized to
  its own minimal clause count, covering what would otherwise be several
  chained 2-input AND gates each getting 3 Tseitin clauses. **axeyum's
  encoding is the opposite end of this space**: `tseitin_encode`
  (`crates/axeyum-cnf/src/lib.rs`, called from
  `sat_bv_backend.rs:164`) emits exactly 3 clauses per 2-input AND node with
  no cut-based grouping (per `docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:150-177`,
  the AIG layer's only entry points are the AND/OR/XOR/MUX basis plus
  hash-consing). **This lane could not find a stated numeric comparison
  between the two encodings in ABC's source** (no comment states "N% fewer
  clauses"), so the gap is qualitative and structural, not quantified here:
  fewer auxiliary Tseitin variables (one per cut instead of one per AND gate)
  and clause sets sized to the mapped function's exact minimum rather than the
  Boolean-basis decomposition's clause count. Flagged in the brief as
  possibly the most actionable gap in the whole comparison; this lane confirms
  the mechanism is real and unimplemented in axeyum, but cannot hand a
  measured percentage to back a priority call — that needs a benchmark, not a
  read.
- **Even the plain per-gate encoder in the AIGER project itself
  (`aigtocnf.c`) beats naive Tseitin** by pattern-matching XOR/MUX/ITE shapes
  reconstructed from 3 chained AND gates and emitting the compact 3-clause
  encoding for the *whole* XOR/MUX rather than 3×3 clauses for the 3 ANDs that
  implement it (`aigtocnf.c:414-441`). axeyum's `tseitin_encode` does not do
  even this cheaper, gate-pattern-only optimization — it has no AIG-side
  concept of "this AND subgraph is really an XOR" once `Aig::xor`/`Aig::mux`
  have lowered to the AND/INV basis (`crates/axeyum-aig/src/lib.rs:425-497`).
- **SAT sweeping / FRAIG is the ABC capability with the most direct relevance
  to axeyum's `bitblast_miter.rs`, and the two are not doing the same thing.**
  ABC's `fra/` package ("New FRAIG package") forms *candidate* equivalence
  classes among **all internal AIG nodes** by random simulation
  (`fraClass.c:24-33` describes the class data structure), then resolves each
  candidate pair with a SAT call (`fraSat.c`) and merges proven-equivalent
  nodes, refining classes on any counterexample; this runs repeatedly as an
  *internal, incremental* graph-shrinking pass, feeding straight back into
  further rewriting and the `dch`/choice-node machinery
  (`src/proof/dch/`, 2,840 lines, builds structural "choices" — alternative
  equivalent substructures kept for the technology mapper to pick from later).
  **axeyum has no internal SAT sweeping at all** — `axeyum-aig` only
  hash-conses and folds locally at construction time (no re-simulation, no
  post-hoc merge of nodes proven equal by SAT). `bitblast_miter.rs`
  (1,030 lines, `crates/axeyum-solver/src/bitblast_miter.rs`) is structurally
  different: it builds **one miter AIG holding two whole independently-coded
  bit-blasters** and refutes the single top-level XOR-OR miter with the
  DRAT-producing CDCL core — a one-shot, whole-circuit differential
  equivalence check between two encoders, not a node-by-node internal sweep
  that shrinks the graph being optimized. Per
  `docs/solver-inventory-2026-09/11-wiring-and-integration.md:56` and
  `00-README.md:231`, `bitblast_miter` is reachable only from
  `axeyum-bench/src/main.rs:5782` and `certificate_process.rs:170` — off the
  default solve path.
- **ABC's combinational/sequential equivalence checking (`cec`, 26,969 lines
  across `src/proof/cec/`) is a whole verification subsystem**: simulation
  (`cecSim.c`), several generations of SAT-sweeping-based solve loops
  (`cecSatG.c`/`cecSatG2.c`/`cecSatG3.c`), structural isomorphism shortcuts
  (`cecIso.c`), incremental and correspondence-based sequential variants
  (`cecCorr*.c`, `cecSeq.c`), and miter synthesis (`cecSynth.c`). axeyum has
  nothing at this scale; the closest axeyum artifact
  (`bitblast_miter.rs`) is about 40x smaller and answers one narrower
  question (does our bit-blaster agree with a reference bit-blaster), not
  general two-network equivalence.
- **ABC's PDR/IC3 (`src/proof/pdr/`, 8,063 lines across 12 files, plus a
  dedicated per-frame incremental SAT engine `gipsat/`, 7 more files) directly
  credits its lineage**: `pdrIncr.c:805` and `pdrCore.c:1872` both have (commented-out
  print statements reading) `"Running PDR by Niklas Een (aka IC3 by Aaron
  Bradley)"`. It does ternary simulation for counterexample-to-implicant
  generalization (`pdrTsim.c`/`pdrTsim2.c`/`pdrTsim3.c`, "Ternary
  simulation"), clause propagation and subsumption across frames, and its own
  incremental multi-frame SAT solver (`gipsat/gipMain.c` etc.) rather than
  reusing a generic decision procedure per query. **axeyum's `pdr.rs`
  (987 lines) is term/SMT-level, not gate-level**: it calls the generic
  `check_auto` decider per obligation instead of a dedicated incremental SAT
  engine with frame-local clause databases, and has no ternary-simulation
  generalization step. It compensates with something ABC's PDR does not have:
  a **trusted post-hoc check** — every candidate invariant is independently
  re-verified by three separate `check_auto` calls (initiation, consecution,
  safety) before being trusted (`pdr.rs:1-31`); ABC's PDR trusts its own
  search directly. Per
  `docs/solver-inventory-2026-09/04-arithmetic-theories.md:65,177,180`,
  axeyum's LIA variant, `pdr_lia.rs` (1,106 lines) and `imc_lia.rs`
  (665 lines), have **no production caller at all** — shipped public API,
  dead from the inside — and `bmc.rs` (1,149 lines) is the only one of the
  five model-checking modules with a non-test consumer
  (`axeyum-verify/src/bmc.rs:260`, `04-arithmetic-theories.md:174,189`). ABC's
  BMC infrastructure alone (`src/sat/bmc/`, 29,491 lines across ~50 files:
  multiple engine generations, counterexample minimization, care-set
  analysis) is about 25x the size of axeyum's whole BMC+IMC+PDR family
  combined.
- **ABC has its own McMillan interpolation-based model checker**
  (`src/proof/int/`, "Interpolation engine", `intCore.c`/`intMan.c` etc.),
  directly comparable to axeyum's `imc.rs` (553 lines, cites McMillan, CAV
  2003, in its own doc comment). This is one of the few places the two
  projects implement the *same named algorithm* at comparable conceptual
  granularity, even though ABC's is gate-level (interpolates SAT resolution
  proofs from its own `bsat` solver via `satInterP.c`) and axeyum's is
  term/SMT-level (interpolates over `qf_bv_interpolant`/LRA/LIA).
- **ABC's own SAT engines have no independent, checkable proof output by
  default.** `bsat/satProof.c` builds and self-checks a resolution trace
  ("Checks the proof for consistency", `:515`) consumed directly by the
  interpolation engine — an internal, trusted-by-construction trace, not an
  externally checkable DRAT/LRAT certificate. DRAT and LRAT tracers/checkers
  exist only inside the **vendored** CaDiCaL copy
  (`src/sat/cadical/cadical_drattracer.cpp`, `cadical_lratchecker.cpp`), i.e.
  only when that specific bundled solver is the one used. axeyum, by
  contrast, produces and independently checks DRAT/LRAT from its own native
  core on every unsat by default (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:85-104`).
  This is a place axeyum's trust story is stronger than ABC's own-engine
  story, even though ABC's overall AIG capability is far larger.
- **AIGER format compatibility is real but not zero-hop.** axeyum's
  `to_aiger_ascii` (`crates/axeyum-aig/src/lib.rs:628-666`) emits a
  standards-conformant ASCII AIGER (`aag M I L O A` header, dense node IDs,
  node 0 reserved as the constant per `AigLit::FALSE`/`TRUE`
  (`lib.rs:57-64`), acyclic by construction because `Aig::and` only ever
  references already-created nodes) — this lane checked its literal-encoding
  convention (`aiger_literal`/`aiger_node_literal`, `lib.rs:760-765`, `var*2 +
  sign`) against `references/aiger/FORMAT` and it matches, and the ASCII
  format has no LHS/RHS ordering restriction (`FORMAT:288-291`, only the
  binary format does), so our dense-topological node order is legal input.
  **But ABC's own readers accept only the binary AIGER format**, not ASCII:
  `Gia_AigerRead`/`Gia_AigerReadFromMemory`
  (`references/abc/src/aig/gia/giaAiger.c:168-320`) discard the format token
  without checking it and unconditionally binary-varint-decode the AND-gate
  section (`Gia_AigerReadUnsigned`, `:293-295`); the standalone `Aiger_Read`
  helper in the same file explicitly rejects anything that isn't the binary
  magic (`"Aiger_Read(): Can only read binary AIGER.\n"`, `:1980`); and
  `references/abc/src/aig/ioa/ioaReadAig.c` and
  `references/abc/src/base/io/ioReadAiger.c` are both headed "Procedures to
  read **binary** AIGER format." Feeding our ASCII output straight to
  `abc -c "read_aiger our.aag; ..."` would not produce a graceful rejection
  — it would misparse ASCII decimal digits as binary varint bytes. **The
  concrete, cheap win is real but needs one hop**: pipe our ASCII output
  through the AIGER project's own `aigtoaig` converter
  (`references/aiger/aigtoaig.c`, confirmed to read/write both `aiger_ascii_mode`
  and `aiger_binary_mode` via `aiger_open_and_read_from_file`, `:242` and mode
  flags `:350-352`) to get a binary `.aig`, which ABC's readers accept as-is.
  That converter is a single small C file with no dependency beyond
  `aiger.c`/`aiger.h`. Building `aigtoaig` (or a native binary-AIGER writer in
  `axeyum-aig`, comparable in size to the existing ASCII writer) is the
  missing piece, not a format incompatibility in our export.

## Schema

### A — Input front end

- **ABC**: accepts BLIF, Verilog (structural subset), AIGER (binary only, both
  packages checked above), BENCH, PLA, and its own `.bench`/`.cba` variants,
  dispatched by file-extension sniffing in the `read`/`&r` command family
  (`src/base/abci/abc.c`, `Cmd_CommandAdd` table around `:1100-1350`). No SMT-LIB.
- **AIGER**: `aiger.c`/`aiger.h` — one C library, both ASCII (`aag`) and binary
  (`aig`) AIGER, auto-detected by magic on read
  (`aiger.c:1291`/`:1720` write the two format tokens; the reader dispatches
  on them, unlike ABC's binary-only readers). A family of ~40 small CLI tools
  built on it (`aigtoaig`, `aigmiter`, `aigsim`, `aigbmc`, `aigfuzz`, …).
- **axeyum**: SMT-LIB2 term-level front end (`axeyum-smtlib`); the AIG layer is
  purely an internal lowering target, not a user-facing input format. n/a for
  direct comparison on "front end" beyond the AIGER export axis already
  covered above.

### B — Preprocessing (before search)

- **ABC**: word-level netlist preprocessing (constant propagation, sweep of
  dangling nodes `Aig_ManCleanup`, `darCore.c:98`) happens as part of each
  named script (`resyn2`, `dc2`, …), not as one fixed pass before a single
  SAT call — ABC's "preprocessing" for a `sat`/`cec` run is whichever
  synthesis script the user chose to run first. n/a to compare directly
  against axeyum's fixed pipeline order.
- **axeyum**: fixed order documented in
  `docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:178-241` (admission →
  bit lowering → Tseitin → inprocessing (off by default) → search). Not
  cited further here; owned by the SAT-core lane.

### C — Core SAT engine

- **ABC**: multiple vendored engines (`bsat`/`bsat2` in-tree, `cadical`,
  `kissat`, `glucose`, `glucose2`, `satoko`, `xsat` bundled under `src/sat/`),
  selectable per command. n/a for a single "ABC's decision heuristic" — it
  depends entirely on which bundled solver a given command links.
- **axeyum**: one native CDCL core (`proof_sat.rs`, VSIDS + Luby restarts +
  LBD-tiered clause DB + phase saving; owned by the SAT-core lane's own file).

### D — Inprocessing (during search)

- **ABC**: n/a in the axeyum sense (no single core to inprocess inside); its
  equivalent capability is the SAT-sweeping/FRAIG family covered under
  Summary — a between-runs, not during-search, simplification loop.

### E — Encoding / bit-blasting

Covered in depth under Summary (AIG rewriting, cut-based CNF mapping). Key
citations: `crates/axeyum-aig/src/lib.rs:131-233` (structural hashing),
`:345-420` (constant fold + absorption + consensus, all local); ABC:
`src/opt/dar/darCore.c`, `darLib.c`, `darRefact.c`, `darBalance.c` (global
rewrite/refactor/balance); `src/sat/cnf/cnfCore.c`, `cnfMap.c`, `cnfData.c`
(cut-based technology-mapped CNF).

### F — Theory solvers

n/a. ABC has no first-order theories — it reasons over Boolean/AIG-level
circuits and word-level netlists (bit-vectors as buses of AIG bits, not an
SMT bit-vector *theory* with `bvadd`/`bvmul` semantics). axeyum's theory
solvers are out of scope for this lane; see
`docs/solver-inventory-2026-09/04-05-06-07-*.md`.

### G — Theory combination

n/a for the same reason as F.

### H — Quantifiers

n/a. ABC has no first-order quantifier support. (It has "don't-care"
conditions and universal/existential *don't-care* computation in some
optimization passes — e.g. `src/opt/mfs` — but that is a different, circuit
notion of "don't care," not FOL quantification, and citing it here would
mislead.)

### I — Model production

- **ABC**: produces counterexample **traces** (sequences of input vectors)
  for BMC/CEC failures, and satisfying assignments from `sat`/`&sat`. Ternary
  simulation (`pdrTsim.c`) is used to *generalize* a counterexample into a
  cube, not to validate a model against source semantics the way axeyum's
  `replay_model` does. No "evaluate the original term against the lifted
  model" step comparable to axeyum's replay gate
  (`docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:230-241`), because
  ABC's model *is* the circuit-level witness — there is no higher-level term
  to replay against.
- **axeyum**: see the SAT-core lane's file, `sat_bv_backend.rs:2347` onward.

### J — Proof / certificate production

Covered under Summary. ABC: internal, self-checked resolution trace in
`bsat/satProof.c` feeding `int/` interpolation; externally-checkable DRAT/LRAT
only via the vendored CaDiCaL (`src/sat/cadical/cadical_drattracer.cpp`,
`cadical_lrattracer.cpp`). axeyum: native DRAT/LRAT/Alethe by default from its
own core; see `01-sat-core-and-cnf.md:85-104`.

### K — Proof checking

- **ABC**: an in-tree LRAT checker exists but only inside the vendored
  CaDiCaL copy (`src/sat/cadical/lratchecker.hpp`,
  `cadical_lratchecker.cpp`) — it checks CaDiCaL's own proofs, not ABC's
  native `bsat` resolution traces, which are only self-consistency-checked
  (`satProof.c:515`), not independently verified against an external
  checker format.
- **axeyum**: `check_drat`/`check_drat_backward`/`check_lrat`/`check_alethe`,
  all in-tree, all independent of the producing search
  (`01-sat-core-and-cnf.md:85-104`).

### L — Interpolation

- **ABC**: `src/proof/int/` ("Interpolation engine"), McMillan-style, over
  resolution proofs from its own SAT solver (`intInter.c`, `satInterP.c`).
  Used by ABC's own IMC-style model checking.
- **axeyum**: `qf_bv_interpolant` + theory-specific interpolants
  (`lra_interpolant_cnf.rs`, `bv_interpolant.rs`), consumed by `imc.rs`. Same
  algorithm family (McMillan, CAV 2003, cited by both — `imc.rs:1-13` cites
  it directly), different granularity (gate-level vs. term-level).

### M — Optimization (MaxSAT, OMT)

n/a for both in the comparable sense: ABC's "optimization" is circuit-area/
delay optimization (rewrite/refactor/balance/technology mapping), not
MaxSAT/OMT over a Boolean/SMT objective. axeyum's MaxSAT is a separate
subsystem (`docs/solver-inventory-2026-09/05-*.md`) not covered by this lane.

### N — Incrementality

- **ABC**: per-command; some engines maintain incremental SAT internally
  (`gipsat` inside PDR is a genuinely incremental, per-frame solver: new
  frames add clauses, never remove). No general push/pop API across the tool
  the way axeyum's `IncrementalSat`/`Solver` façade offers at the term level.
- **axeyum**: `IncrementalSat`/`IncrementalCnf`/`IncrementalBvSolver`
  (`01-sat-core-and-cnf.md:242-272`); `Solver` itself is watermark-only, not
  truly incremental (`11-wiring-and-integration.md`, gap 4).

### O — Parallelism

- **ABC**: some newer commands take an explicit `nProcs`/parallel-solver
  count (`src/base/abci/abc.c:53098`, `:53240`, doc string "-P num : the
  number of parallel solvers"), default `1`. This lane did not read far
  enough into which specific commands (found near PDR/BMC-family option
  parsing) to give per-command citations beyond the two line numbers found;
  **`[undetermined]`** which commands actually wire it end to end.
- **axeyum**: `portfolio::FusedGroup`, gated on
  `AXEYUM_PORTFOLIO_WORKERS >= 2`, default `1`
  (`11-wiring-and-integration.md`, gap 8) — same shape (parallel capability,
  off by default) as ABC's `nProcs`.

### P — Resource limits and determinism

- **ABC**: per-command timeouts/conflict limits exist in individual engines
  (e.g. PDR/BMC option structs carry time budgets), not audited exhaustively
  by this lane — **`[undetermined]`** as a project-wide statement; would need
  a pass over every `*Pars` struct in `src/proof/*` and `src/sat/bmc/*`.
- **axeyum**: `config.resource_limit` (conflicts), `config.timeout`, documented
  centrally (`01-sat-core-and-cnf.md`, `04-arithmetic-theories.md`).

## Gaps against axeyum

### 1. They have, we do not

| Capability | Their implementation (cited) | Our status (cited) | Rough size of gap |
|---|---|---|---|
| Global DAG-aware AIG rewriting (library-based cut substitution) | `src/opt/dar/darCore.c:79` (`Dar_ManRewrite`), `darLib.c` (subgraph library), params `nCutsMax=8`/`nSubgMax=5` (`darCore.c:54-55`) | `axeyum-aig` does only construction-time hash-consing + local constant/absorption/consensus folding (`crates/axeyum-aig/src/lib.rs:131-420`); no post-hoc global rewrite exists | Large — 17,070 lines of nothing-equivalent |
| AIG refactoring (window + Boolean decomposition resubstitution) | `src/opt/dar/darRefact.c` (`Bdc_Man_t` bi-decomposition) | None | Large, no partial coverage |
| Algebraic AIG balancing (depth reduction between passes) | `src/opt/dar/darBalance.c` | None | Medium |
| Named optimization scripts composing the above (`resyn`, `resyn2`, `compress2`, `dc2`) | `abc.rc:110-116`; `Abc_CommandDc2`, `abc.c:18436` | None — no equivalent circuit-size-reduction command exists at all | Large (depends entirely on the above) |
| Cut-based, technology-mapped CNF generation (smaller var/clause count than per-gate Tseitin) | `src/sat/cnf/cnfCore.c` (`Cnf_Derive`), `cnfData.c:4528` (4-var MSOP clause tables) | `tseitin_encode` — plain per-AND-gate Tseitin, no cut grouping (`crates/axeyum-cnf/src/lib.rs`, called `sat_bv_backend.rs:164`; `docs/solver-inventory-2026-09/01-sat-core-and-cnf.md:150-177`) | Large; flagged in the brief as possibly the most actionable — mechanism confirmed, magnitude `[undetermined]` without a benchmark |
| Even gate-pattern (XOR/MUX) collapsing in plain Tseitin encoding | `references/aiger/aigtocnf.c:414-441` | Not present — `tseitin_encode` has no notion of a reconstructed XOR/MUX shape once lowered to AND/INV | Small-to-medium, cheap to add |
| Internal SAT sweeping / FRAIG (simulation + SAT merges functionally-equivalent internal nodes, feeds back into rewriting) | `src/proof/fra/` (`fraClass.c`, `fraSat.c`); choice nodes in `src/proof/dch/` (2,840 lines) | None — `bitblast_miter.rs` is a one-shot whole-circuit differential check between two *whole* bit-blasters, not an internal per-node merge pass, and is off the default solve path (`docs/solver-inventory-2026-09/11-wiring-and-integration.md:56`) | Large, and structurally different in purpose, not just scale |
| General combinational/sequential equivalence checking (`cec`) | `src/proof/cec/`, 26,969 lines: simulation, multi-generation SAT sweeping, structural isomorphism, sequential correspondence | `bitblast_miter.rs` only, 1,030 lines, one narrow purpose (bit-blaster faithfulness), bench-only reachability | Very large |
| Gate-level PDR with dedicated per-frame incremental SAT and ternary-simulation generalization | `src/proof/pdr/` (8,063 lines) + `gipsat/` (7 files); ternary sim `pdrTsim.c` | `pdr.rs` (987 lines) calls the generic `check_auto` decider per obligation, no dedicated frame-local SAT engine, no ternary-sim generalization | Large in engineering depth; axeyum compensates with a trusted post-hoc invariant re-check ABC lacks (see below) |
| Large, mature BMC infrastructure (multiple engine generations, CEX minimization, care-set/fault analysis) | `src/sat/bmc/`, 29,491 lines, ~50 files | `bmc.rs` (1,149) + `axeyum-verify/src/bmc.rs` (268) = 1,417 lines total | Very large (≈20x) |
| Binary AIGER read/write | `giaAiger.c`, `ioaReadAig.c`, `ioReadAiger.c` (binary only); `aiger.c` (both formats) | `axeyum-aig` writes ASCII only (`to_aiger_ascii`, `lib.rs:628`); no reader at all, no binary writer | Medium — blocks feeding ABC directly without the `aigtoaig` conversion hop |

### 2. We have, they do not

This table is short. ABC is a mature synthesis/verification system with far
more AIG-level capability than axeyum in almost every axis this lane checked;
the honest exceptions are narrow and about *trust*, not circuit capability.

| Capability | Our implementation (cited) | Their status |
|---|---|---|
| Independent, in-tree DRAT/LRAT/Alethe checking of every native `unsat`, by default | `check_drat`/`check_lrat`/`check_alethe`, no feature flag needed (`01-sat-core-and-cnf.md:85-104`) | ABC's own `bsat` solver only self-checks its resolution trace (`satProof.c:515`); independent LRAT checking exists only for the vendored CaDiCaL's own proofs (`src/sat/cadical/lratchecker.hpp`), not for ABC's native engine |
| Trusted post-hoc re-verification of a PDR-discovered invariant (three independent decision-procedure calls before trusting `Safe`) | `pdr.rs:1-31` (initiation/consecution/safety, each via `check_auto`) | ABC's PDR trusts its own search's conclusion directly; no equivalent gate found in `pdrCore.c`/`pdrInv.c` |
| A model checker that operates over SMT theories (LIA/LRA/BV) rather than only bit-level circuits | `imc_lia.rs`, `imc_lra.rs`, `pdr_lia.rs`, `pdr_lra.rs` (even though two of the four have no production caller today — `04-arithmetic-theories.md:65,177,180`) | Not applicable — ABC has no term-level theories to model-check over at all |

## Not comparable

- **ABC is not an SMT solver and axeyum's AIG layer is not a synthesis tool.**
  Comparing "capability count" head to head would mislead: ABC's entire
  purpose is circuit-level synthesis and verification (mapping, retiming,
  physical-design-adjacent passes under `src/phys/`), none of which axeyum
  has any reason to have, because axeyum's AIG is a bit-blasting
  *intermediate representation* consumed once per query, not a persistent
  artifact anyone re-optimizes, maps to a technology library, or hands to
  place-and-route.
- **ABC's PDR/BMC/CEC operate on sequential circuits with latches**; axeyum's
  `pdr.rs`/`bmc.rs`/`imc.rs` operate on symbolic transition systems expressed
  as SMT terms over `init`/`trans`/`bad` predicates. "Lines of code" is not a
  fair proxy for capability here — ABC's model-checking size partly reflects
  handling arbitrary industrial RTL-derived netlists (retiming interactions,
  constant propagation through latches, multiple CEX-minimization heuristics
  for debug), problems axeyum's term-level engines do not face by
  construction.
- **The CNF-encoding comparison (axis E) is apples-to-oranges in one specific
  way**: ABC's mapped CNF trades preprocessing time (cut enumeration +
  library/table lookup over the whole AIG) for a smaller, more solver-friendly
  formula; axeyum's plain Tseitin trades that preprocessing cost away for a
  direct, easy-to-audit gate-to-clause mapping that keeps the
  `variable_bindings`/replay story simple
  (`01-sat-core-and-cnf.md:178-241`). Whether the trade is worth it depends on
  formula shape and is not answerable by reading source; needs a
  benchmark.
- **DRAT/LRAT/Alethe production and checking is not a fair comparison of "who
  is better"** — ABC was never designed around a checkable-certificate trust
  model for its native engine; CaDiCaL's DRAT/LRAT machinery is CaDiCaL's,
  vendored, not ABC's own design choice. Framing this as "ABC lacks proof
  checking" would misstate ABC's design intent, which is solve-fast synthesis
  tooling, not a trust-anchored proof pipeline.

## Confidence

**Solid source reads** (specific line citations, function bodies read):
`axeyum-aig` construction-time simplification (`lib.rs:131-497`); the ASCII
AIGER export and its conformance to `FORMAT` (`lib.rs:628-666`, cross-checked
against `references/aiger/FORMAT:271-291`); ABC's binary-only AIGER readers
(`giaAiger.c:168-320`, `:1980`; `ioaReadAig.c:1-50`; `ioReadAiger.c` header);
`aigtoaig.c`'s dual-mode read/write (`:242`, `:350-352`); ABC's `dar` package
structure and `resyn`/`resyn2`/`compress2`/`dc2` scripts (`abc.rc:110-116`,
`abc.c:18436`); ABC's `cnf` package being cut/mapping-based, with the
MSOP-table comment in `cnfData.c:4528`; `fra`/`dch`/`cec` package structure
and their file-level `Synopsis` headers; `pdr`/`gipsat` file inventory and the
Een/Bradley attribution comment; the DRAT/LRAT-only-in-CaDiCaL finding
(`satProof.c:515` vs. `cadical_lratchecker.cpp`).

**Inferences from naming, comments, and structure, not full function reads**:
the exact algorithmic content of `darRefact.c`'s bi-decomposition; the
`cnfMap.c` area-flow cut-selection heuristic's precise cost function; the
`cec` package's internal SAT-sweeping variants beyond their filenames and
`Synopsis` lines; which commands actually wire the `nProcs` parallel-solver
option end to end (flagged `[undetermined]` in the schema, axis O).

**Explicitly not claimed**: any quantified circuit-size reduction number for
`resyn2`/`dc2`, and any quantified clause/variable-count reduction for
mapped-CNF vs. Tseitin. Both are widely cited results in the AIG-optimization
literature (the DAG-aware-rewriting paper referenced by `references/aiger/FORMAT:737`,
and the Een/Mishchenko/Sorensson SAT-2007 CNF-mapping paper this lane knows by
reputation but did not locate or read inside either clone), and repeating
those numbers here without reading the paper itself would violate the
brief's "no invented numbers" discipline. Getting a real number requires
either finding the paper or running `resyn2`/`cnf` on a shared benchmark and
counting.
