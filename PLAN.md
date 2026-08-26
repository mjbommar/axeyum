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
**WIP**. Trusted surface, re-derived by `gen-lean-axiom-ledger.py --check`
rather than authored, 2026-08-19: `complex 0 · creal 0 · integer 0 · logic 0 ·
nat 0 · rat 0 · string 0 · real 30` — `real`, the axiomatized package, is the
only nonzero row. "Int reconstruction remains assumption-bearing" was true until
that day and is not.

**Declared is not reached; both are published**
([ADR-0509](docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)).
The 30 stay declared, reached by no shipped route. The package is kept as the
negative control those measurements are read against — delete it and no such
measurement can fail — now one assumed law over a constructed carrier
([ADR-0515](docs/research/09-decisions/adr-0515-a-negative-control-is-one-assumed-law-over-a-constructed-carrier.md)).

Exact pushed repairs for the A5 (linear-arithmetic), A3 (string/integer) and
A2 (stale-branch) streams — commit-by-commit, with the non-credited partial
streams retained — are in the
[A5/A3/A2 repair journal](docs/plan/a5-a3-repair-journal-2026-08.md). The
current release returns typed `unknown` on each former abort trigger; A3 yields
to A4.
### A1 arithmetic resource closure — `DONE`, archived

The two measured resource defects and their pushed repairs are in
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md).
Moved 2026-08-19: it is closed work, and this file is for what is true
now. Nothing was deleted.

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
| 2026-08-26 | `a88fa732f` | Redact all 37 held-out identities from agent-readable rankings and censuses; replace them with count/hash receipts, derive exclusions independently, and restore the 1,881-test Python authority to green. |
| 2026-08-26 | `7e8fe9b3b` | Restore the standard-library-only script boundary with typed package implementations and stable launchers; fix seven newly exposed diagnostics and refresh honest bounded yield from 6/109 to 6/111. |
| 2026-08-26 | `f1e1724e2` | Add held-out-safe tier-R retrieval for reusable target-owned capsule roots, preserving capsule identity, empty footprints, semantic-analogue qualification, and zero operation authority. |
| 2026-08-26 | `81b5bae31` | Repair the typed agent read surface so structural statement floors, proof-reconstruction eligibility, and clean-definition routing survive the generated index boundary. |
| 2026-08-26 | `e56f1b339` | Root-export the three clean bitwise siblings as one reproducible external NDJSON capsule; fresh import admits 116 declarations, no axioms, and the same generic dependency for every root. |
| 2026-08-26 | `282235e82` | Connect the three clean bitwise siblings to their open Mathlib development facts as non-authoritative semantic analogues, preserving zero exact-match and operation credit. |
| 2026-08-26 | `76817cc3b` | Specialize the clean generic bitwise construction into AND, OR, and difference; all three sibling theorems reuse the same generic proof and retain empty footprints. |
| 2026-08-26 | `cca5f9678` | Split proof-reconstructible candidate debt from structural statement trust floors; route the exact imported bitwise theorem to clean-definition reconstruction instead of futile proof retries. |
| 2026-08-26 | `fe531ca30` | Prove with two theorem-free `Eq.refl` controls that exact imported `Nat.testBit` and `Nat.bitwise` statements inherit `propext` from their definition closures, making the empty-footprint boundary structural and explicit. |
| 2026-08-26 | `32802405d` | Construct a total target-owned bitwise operation and prove its all-index Boolean semantics axiom-free under exactly `f false false = false`. |
| 2026-08-26 | `08d4da396` | Prove axiom-free that every observation beyond a low-digit reification's width is false, closing the output-side tail of the unbounded bitwise theorem. |
| 2026-08-26 | `448fc8431` | Prove universal low-digit reification round-trip and specialize it into the first axiom-free bounded bitwise semantic theorem. |
| 2026-08-26 | `05b92a924` | Prove axiom-free quotient and remainder equations for a Boolean low digit plus twice an arbitrary tail, supplying the recursive decoder for component uniqueness. |
| 2026-08-26 | `d89a192b7` | Compose the universal reification bound with native bit-sum reconstruction to prove an axiom-free numeric round trip, isolating component uniqueness. |
| 2026-08-26 | `04ca04a3d` | Prove universally and axiom-free that every bounded Boolean-bit reification is strictly below `2^k`, leaving only observation uniqueness. |
| 2026-08-26 | `a00743663` | Prove every Boolean reification digit is at most one constructively and axiom-free, supplying the local bound for the universal reifier induction. |
| 2026-08-26 | `e6d798c06` | Exhaustively validate bounded reification over all 8,191 Boolean vectors through width 12 while preserving the oracle's non-proof authority boundary. |
| 2026-08-26 | `b1405eff6` | Prove one-bit weighted-sum normalization and its Boolean observation round trip axiom-free; narrow the open theorem to the general bounded case. |
| 2026-08-26 | `fcdcab1b3` | Prove the Boolean-digit map round-trips through bit zero axiom-free and expose weighted-sum normalization as the next non-definitional arithmetic seam. |
| 2026-08-26 | `75baf4b2c` | Expose the bounded reifier's axiom-free successor equation as a stable induction interface for the missing observation round trip. |
| 2026-08-26 | `3bb1207e8` | Construct bounded Boolean-bit reification as a binary weighted sum and check its zero-length base axiom-free; retain the round-trip theorem as missing. |
| 2026-08-26 | `f0782cc25` | Construct the axiom-free pointwise bitwise observation algebra and isolate Nat reification as the remaining mathematical obligation. |
| 2026-08-26 | `8935a4045` | Describe imported transparent definitions by exact body/type identities, closure, and footprint; both bitwise operations reach `propext`, ruling out clean grafting. |
| 2026-08-26 | `b4d64c3ea` | Make the refuted generalized capsule fail closed at emission time unless the caller explicitly opts into diagnostic-only output. |
| 2026-08-26 | `6eb41d48b` | Construct an axiom-free Boolean view of native numeric bits and prove its successor equation by reflexivity, while withholding imported-definition equivalence credit. |
| 2026-08-26 | `af86b673a` | Bind existing axiom-free numeric `testBit` analogues while refusing their Bool-valued imported use until a checked observation-transport seam exists. |
| 2026-08-26 | `99f7b4e32` | Bind five bitwise semantic-law obligations to exact candidate and operation identities, with a checked witness that the interface excludes the prior countermodel. |
| 2026-08-26 | `70ca259b5` | Refute and execution-block the unconstrained proof-free bitwise target with a checked finite countermodel; require a law-bearing semantic interface before reconstruction. |
| 2026-08-26 | `0554b6b86` | Materialize the assumption-bearing imported bitwise candidate as a proof-free, axiom-free generalized reconstruction target with exact external receipt validation. |
| 2026-08-26 | `2397eb08f` | Expose exact imported candidates through a separate ninth tier-R agent tool that preserves footprint-aware reconstruction routing and refuses invalid query shapes. |
| 2026-08-26 | `1c7cb953e` | Add a machine-readable imported-candidate descriptor and separate footprint-aware search index; assumption-bearing candidates route to reconstruction before execution. |
| 2026-08-26 | `6e0f87c2d` | Export and independently audit upstream `Nat.testBit_bitwise`; preserve its exact 29-dependency, five-assumption footprint as reconstruct-required guidance rather than contract evidence. |
| 2026-08-26 | `48ae785e2` | Derive the exact four-target bit-observation contract slice: 103 shared transparent nodes, explicit target deltas, and a non-circular lower-level theorem boundary. |
| 2026-08-26 | `95587054fd` | Preserve stream-context declaration identities, compact the imported graph through dense node IDs, and derive a checked 113-node reverse-reachability frontier for multi-sibling contract design. |
| 2026-08-26 | `ebcfd3fb88` | Derive the proof-isolated imported implementation-demand graph for all 14 sliced source identities, retaining structural variants and the checked `Nat.mod` decision/subtraction spine without proof or ledger authority. |
| 2026-08-26 | `d2d6fc0d0` | Add axiom-free native `Nat.mod_self`, alpha-stable structural retrieval, and a checked native-composition control; fresh imported replay preserves zero credit and exposes the implementation-bound `Nat.mod` transport boundary. |
| 2026-08-26 | `73800a902` | Project all 51 retrieved-induction outcomes into a digest-bound typed capability backlog; false controls remain observation-only and one-target operation registration is refused. |
| 2026-08-26 | `e82a1b002` | Replay all 25 import-blocked positive targets through checked type slices, exposing 14 exact semantic-contract demands without proof or ledger credit. |
| 2026-08-26 | `1e7b3acdf` | Join 14 sliced source identities to exact kernel and durable contract evidence; `Nat.testBit` becomes the first measured multi-sibling contract target. |
| 2026-08-26 | `882dc1a63` | Reduce transparent relation terminals before equality search; ten ModEq goals cross the grammar boundary with zero false accepts, exposing typed relation-premise composition as the next gap. |
| 2026-08-26 | `228494275` | Expose bounded retrieved-lemma application through the typed Python producer surface with full Python, stub, and type-gate coverage. |
| 2026-08-26 | `0c261718f` | Add the fail-closed candidate-capsule import boundary required for theorem-composition dispatch. |
| 2026-08-26 | `ebe2b7b2e` | Re-derive the kernel projection and lemma-search artifacts at 1,242 theorems after rebasing concurrent mathematics work. |
| 2026-08-26 | `fa821fc54` | Merge the next constructive-real theorem and advance the same generated search population to 1,243 without clobbering either lane. |
| 2026-08-26 | `5916d47cc` | Publish stable all-kind direct declaration dependencies through Rust, Python, and the generated kernel projection, with direct-versus-transitive controls. |
| 2026-08-26 | `17b0c1163` | Split proof-isolated type dependencies from type-plus-value evidence before premise selection could leak a finished theorem's proof. |
| 2026-08-26 | `710b7cf04` | Publish the reproducible proof-isolated bounded-application census: 6/109 accepted, 103 typed declines, zero accepted axiom footprints. |
| 2026-08-26 | `bf484f355` | Add a reusable proof-isolated capsule materializer and hash-bound receipts for the three accepted arithmetic controls without vendoring NDJSON. |
| 2026-08-26 | `8b54237ab` | Teach the agent export/producer boundary to resolve exact candidate-capsule receipts and execute bounded application without widening operation authority. |
| 2026-08-26 | `30bfc8991` | Make generated statement-adapter names unique across arbitrarily many normalized slug collisions. |
| 2026-08-26 | `1be7e79b1` | Promote the accepted command-faithful SMT-LIB driver to the named `axeyum` binary while preserving the checked example surface. |
| 2026-08-26 | `1d4eed93a` | Regenerate the merged theorem graph at 1,250 theorems and 7,184 direct edges after concurrent CReal construction. |
| 2026-08-26 | `eb38cf63a` | Exclude 23 held-out goals before open-census capsule access, disclose the superseded contaminated run, and remeasure 0/57 train/development conversion. |
| 2026-08-26 | `680952a5d` | Rank 1,704 proof-isolated kernel-lemma candidates for 142 train/development open goals while excluding all 37 held-out IDs before statement tokenization. |
| 2026-08-26 | `2b6020af2` | Compare closed propositions across independently owned kernels without confusing their shared outer `Prop` type or granting proof/admission authority. |
| 2026-08-26 | `dc71a97a1` | Add a proof-free multi-candidate audit and demonstrate exact native equivalence can be distinguished from nearby topical mismatches. |
| 2026-08-26 | `16de20475` | Publish the hash-bound 57-goal ranked proposition census: six exact native equivalents, 678 declines, and zero held-out access. |
| 2026-08-26 | `18ccc487e` | Add six independently checked, non-authoritative fact-to-kernel proposition-match links and document the reconciliation boundary. |
| 2026-08-26 | `83b3694e8` | Register two missing native binomial facts from kernel inventories and regenerate all dependent knowledge views at 1,253 theorems. |
| 2026-08-26 | `cd02dbb57` | Add a fail-closed, operation-free proposition-reconciliation transaction with mutation controls and explicit zero autonomous credit. |
| 2026-08-26 | `3d4bb31eb` | Materialize six live hash-bound reconciliation proposals with zero writes, operations, and autonomous credit. |
| 2026-08-26 | `6a348363b` | Extend the crash-safe applier with live-rebuilt, operation-free reconciliation events and recovery controls at every durable boundary. |
| 2026-08-26 | `4e025a444` | Preserve the pre-reconciliation ranking and bind the 57-goal census to its immutable path and hash. |
| 2026-08-26 | `9230d9666` | Reconcile six exact native propositions crash-safely, preserve zero production credit, and publish the clean 51-goal / zero-match remainder. |
| 2026-08-26 | `2e060c8e6` | Add exact axiom-free native-candidate transport and demonstrate 8/12 ranked premises executable on a real imported modular goal. |
| 2026-08-26 | `ba3f4acdd` | Expose native transport through Python and measure 210 executable ranked premises reaching 0/24 bounded-application conversion. |
| 2026-08-26 | `2c86c0604` | Preserve ranked premise order through bounded search; the full census reproduces unchanged, ruling out alphabetical budget starvation as the active limiter. |
| 2026-08-26 | `b852c4e89` | Compose graph-retrieved equalities through bounded induction and convert the first immutable open-population target axiom-free with zero false-control accepts. |
| 2026-08-26 | `bdfe77340` | One `DEEP_STACK_BYTES` (256 MiB) and one `on_a_deep_stack` replace seven verbatim copies at three unexplained sizes. `examples/kernel_stack_envelope` builds one prelude on an exact stack and answers with its exit status (0/134/2), refusing to run with the prelude cache on because a cache hit type-checks nothing and would report a requirement of ~0. `scripts/check-kernel-stack-envelope.sh` pins the table and halves every budget until the probe FAILS, so a green run has demonstrated it can go red. Six controls; each of the five guards mutation-verified to kill exactly one. |
| 2026-08-25 | `beb27f1ba` | **The trusted-core ceiling, raised the way the gate demanded.** Guard C failed at 5,508 past 5,500 with "say why before raising it." The baseline was RE-DERIVED by `git archive` rather than trusted, giving a per-file table summing to exactly +379 (`tc.rs` +347, `inductive.rs` +30, `env.rs` +2). Verdict: real and necessary — a universe-parameter closure fixing declarations **official Lean 4.30.0 refuses but this kernel wrongly admitted**, and `whnf_core` memoisation (138× cost, 1,857 s → 13.4 s) inside `def_eq`. Ceiling 5,900 with headroom matching the original's character; guard C re-verified to fire by injecting 500 lines in a scratch copy. The file's own comment said "5,110" where the real baseline was 5,129 — wrong from day one. |
| 2026-08-25 | `0f2fb5fcd` | A doc line beginning with `+` is a Markdown list bullet, so ten `doc_list_item` errors pointed at ordinary prose one line below the cause. |
| 2026-08-25 | `6de1d88f8` | Salvage: **the irrationality of √2** (`Nat.no_rational_sqrt_two`) and **`CReal.geom_tail_within`**, committed on behalf of two lanes killed mid-run by a spend limit. Both verified here: 695 tests, clippy `--all-targets`, axiom-free. |
| 2026-08-25 | `03385d2f7` | **`CReal.monotone_of_nonneg_deriv`** — global from local, constructively, no MVT. Four lanes. The congruence is needed at BOTH endpoints, not just the one the handoff named. |
| 2026-08-25 | `dd1ba4808` | `clippy --all-targets` was red on `main` in a doc comment I wrote; four lanes each reported it and each routed around it to the narrower `--lib --tests`. |
| 2026-08-25 | `9703044b7` | `perfect.rs` shipped unformatted behind a green clippy and a green 679-test sweep; `hooks/pre-push`'s `cargo fmt --all --check` caught it. `--lib` structurally cannot. |
| 2026-08-25 | `4a21cbde7` | Correction to a correction: `Int.prodRange_permute` is full-range (`MapsInto σ n`), so the predicate-scoped primitive genuinely does not exist over any carrier. Production regen 1125 → 1141. |
| 2026-08-25 | `af8340e16` | Held-out contamination and the seven-lane fold finding, recorded. |
| 2026-08-25 | `8aa57e4e8` | The `CReal.sqrt` route: `KRegular` at `c = 3` **uniformly in `x`**, so `sqrt` is total and needs no `PosBound` — which a constructive setting could not have supplied, since `0 ≤ x` is undecidable. |
| 2026-08-25 | `efbe6cc82` | Top-three focus plan, production-only episode gate, kernel lemma search index, and typed deterministic query API. |
| 2026-08-25 | `86431e6cd` | Autonomous-loop read tool exposes held-out-safe kernel lemma neighborhoods as candidate-only context. |
| 2026-08-25 | `92271d133` | Kernel projection and lemma index advanced together to the then-current 1,185-theorem population. |
| 2026-08-25 | `d904fa59c` | Python CI installs its agent dependencies; the pinned-nightly MIR fixture and all authentication hashes move together. |
| 2026-08-25 | `d0037b378` | Restore dependency assurance with the published `anyhow` fix and narrowly documented transitive stub-generator exceptions. |
| 2026-08-25 | `2d43f2791` | Repair the CReal geometric-series Rustdoc reference exposed by the merged theorem lane. |
| 2026-08-25 | `9cd07c5f1` | Authoritative frontier/execution/transaction admission settles `Nat.ModEq.symm`; multi-target credit reaches 9. |
| 2026-08-25 | `b34067dc0` | The recomputed frontier settles `Nat.ModEq.trans` through the same producer; multi-target credit reaches 10. |
| 2026-08-25 | `43f87f269` | Durable symmetry unlock promotes `Nat.ModEq.comm` into the unchanged family operation with source-bound evidence. |
| 2026-08-25 | `3375112a9` | Recomputed scheduling admits `Nat.ModEq.comm`; durable-state-driven multi-target credit reaches 11. |
| 2026-08-25 | `3cfb80172` | Resolve five manually verified Nat evidence identities; exact links reach 315 theorems and 319 facts without guessing. |
| 2026-08-25 | `be0c67f67` | mobility summary names the dominant unevaluable reason (`unevaluable_no_export`, `unevaluable_top`), so `unevaluable=186` reads as a reachability block not a tactic gap; regenerates the committed census (191->189) that had drifted stale |
| 2026-08-25 | `e27140275` | `--reachable-first`: stably reorder `--next` selection so facts with a frozen export come first (the first 5 eligible had 0); deterministic, population unchanged |
| 2026-08-25 | `b2813872f` | `--skip-unreachable`: preflight the frozen export before spending a model; skips retrieval-miss-only facts at zero cost (~26k tokens/fact saved), opt-in so replays are unchanged; 3 controls |
| 2026-08-25 | `2a2e863f2` | `gen-statement-adapters.py`: proof-free Lean statement adapters from `formal.statement` to expand frozen-export coverage; `--exportable-only` drops arrow-bearing statements lean4export 3.1.0 refuses; verified end to end on s5; 7 controls |
| 2026-08-25 | `57f3e68b4` `90d6cb5c0` | `14-frontier-reachability.md`: the ~3-of-146 gap decomposed into reachability x provability, measured; finding is the frontier is producer-bound (498 proved, open modeq facts are congruence goals the producers decline) |
| 2026-08-25 | `5c5c2fd04` | fix: a deep `CasExpr` chain raises `BudgetExceeded` (`MAX_EXPR_DEPTH`) instead of segfaulting the process |
| 2026-08-24 | `da1701d97` | The knowledge overlay may not name a sibling repository: source, namespace, 24 links and three unreachable relation types removed; schema tightened so the vocabulary cannot come back; the validator no longer reads `ROOT.parent`. |
| 2026-08-24 | `94f3beb0c` | The crosswalk and the tactic catalog, plus the two projections that went structurally empty with them. `uses_technique` no longer mandates an external source on every tactic. 13 tactic guards, each killed by exactly one test. |
| 2026-08-24 | `70aaccb38` | `scripts/check-external-coupling.py` — 4 rules, 8 guards, 25 controls, each guard killed by exactly one test; wired into both aggregates with `--self-test` first. `graph_pin` and `resolved` removed from all 104 claims; the 777-line Python integration and the agent's `file://` allowlist entry deleted. |
| 2026-08-24 | `c0c2b6fea` | **ADR-0546 + the gate wired into both aggregates.** Records three findings against the brief: `technique`/`concept` are NOT uninstantiated overlay kinds (24 endpoints, resolved `external-pinned` next door); the existing vocabulary still does not suffice, because `unlocks` is reachability and every `formalizes` edge is *required* to be `completeness: partial` so two cannot compose into "same"; and the motivating `Int.fib_cassini ↔ Rat.det2_mul` edge **is not landable** — neither theorem has a fact and neither is in the kernel projection, so `specialization` ships as a declared kind with zero instances and the gate prints that zero. |
| 2026-08-24 | `06b41a5e6` | **`artifacts/correspondences/` — two theorems can be said to be the same idea, and the claim is checked.** Refuses any pair the ledger's *transitive* `depends_on` closure connects (`F:ml430-nat-fib-add-two` / `F:ml430-int-fib-add-two` is a real such pair and the control pins the refusal against the committed ledger). `carrier-transport` is checked *structurally* — erasing the carrier from both formal statements must leave the same string, and an unknown carrier FAILS rather than skipping. Two status axes mirroring the ledger's, each backed: `asserted` ⟺ empty `via`; `route-recorded` requires every non-null ref to resolve; `mechanized-here` forbids a null ref and requires a checker command; evidence at all requires `mechanized-here`. Empty population exits 1. Prose floors set from measuring `../math-education` (1,263 reasons, median 190 chars — and a bridge to `C:pi` whose reason was about *density* validated cleanly there, which is why nothing here rests on prose). |
| 2026-08-24 | `3ba9c1ec6` | Additive Autogenesis knowledge overlay v1 defines typed, qualified, provenance-bearing links across facts, operations, capabilities, and a pinned read-only external concept graph, with eight seed links and four negative controls |
| 2026-08-24 | `b42ecfd81` | Complete F1's evidence-backed multi-target-producer crosswalk, publish a generated coverage census, and reject uncredited producer or individual complete-coverage claims |
| 2026-08-24 | `137fef720` | Generate the complete constructed-kernel declaration/dependency projection with exact theorem-edge agreement and negative controls |
| 2026-08-24 | `00cbed24b` | Normalize retained decline records into a generated obstruction projection that rejects lost blockers and invented resolution claims |
| 2026-08-24 | `c49566743` | Derive hash-bound transport chains with incomplete paths explicit rather than name-matched |
| 2026-08-24 | `8e78d8e3e` | Publish separated formal, producer-credit, and transport coverage dimensions |
| 2026-08-24 | `7160fc0bc` | Publish non-authoritative producer observations; current live queue has zero registered admissible candidates |
| 2026-08-24 | `219ce5618` | Q7: panic-surface hardening -- a probe over every callable took panics 3->0, crashes 19->2; preflights + one `catch_unwind` (`InternalError`); a hypothesis no-panic property found the solver-dispatch panic the hand battery missed |
| 2026-08-24 | `e0ce70376` | Q8: the CAS long tail (179 items, 941 tests vs sympy oracle, coverage 302->471, three disagreements pinned) + a runnable demo gallery |
| 2026-08-24 | `f11a74c18` | Q5: typed stubs from the Rust signatures via pyo3-stub-gen (96.9% typed), stubtest + `Any` ratchet gates; found three `axeyum.m` type errors |
| 2026-08-24 | `f11a74c18` | Q5: typed stubs via pyo3-stub-gen behind an off-by-default feature (96.9% typed, allowlisted `Any`s with reasons), `stubtest` + `Any` ratchet gates; three `axeyum.m` type errors found and fixed |
| 2026-08-24 | `68f5d61a4` | `axeyum.m`: Mathematica-shaped verbs over the CAS -- parser, variable inference, readable printer; three iterations (equations, assumptions, limits at infinity; systems, definite integrals, Substitute, semantic Equal, mixed int/Fraction arithmetic on `Expr`; Sum, Reduce, Rationalize, NRoots, polynomial toolkit); 19 tests |
| 2026-08-24 | `460bee2db` | Q2: replay of the deciding run's model via `solve_smtlib_with_model` (2.22x on sat), clone audit (12 borrows, 13 `__eq__` via cast), CAS detaches, bytes accessors, benchmarks |
| 2026-08-24 | `d904a5c14` | `axeyum-solver`: `solve_smtlib_with_model` -- the front door returns arena, assertions and model; `solve_smtlib` wraps it; 152-file equality test |
| 2026-08-24 | `68fb060e7` | Q1: 73 hypothesis differentials, 8 Rust unit tests, `ty` ratchet; fixed replay-over-empty-stack on the word-only fallback |
| 2026-08-24 | `a4393ef18` | Q4: the eight open tier-R solver rows as typed ledgers + `get_assertions/get_info/get_option` + `SolveStats`; coverage backlog empty |
| 2026-08-24 | `e0ce50f97` | Q3: release wheels (manylinux 2_28, macOS, Windows, 3.14t, sdist) with a smoke-install gate before publish |
| 2026-08-22 | (pending) | Corrected-checker `Nat.fib_eq_zero` transaction is frozen from clean commit `39b408e619f2` before one crash-safe intent fault and one recovery |
| 2026-08-22 | (pending) | Exit-75 intent fault leaves `Nat.fib_eq_zero` unchanged; recovery performs exactly one ledger write, the registered checker passes, and the measured readiness delta is empty as preregistered |
| 2026-08-22 | (pending) | Replay preflight declines before mutation because current checker-text gate scanning differs from the retained frontier; exact registration commit reproduces the retained frontier byte-for-byte and is frozen as the V2 replay source |
| 2026-08-22 | (pending) | Historical-source preflight correctly rejects its still-open fact; V3 freezes the exact detached transition child, which preserves the registration gate surface and recovered post-state required by replay verification |
| 2026-08-22 | (pending) | Isolated replay `b63854f8…bfaa0` independently repeats `Nat.fib_eq_zero` selection, certified execution, exit-75 recovery, one write, and the exact empty readiness delta |
| 2026-08-21 | (pending) | All 35 dominance audits re-run at `496288979` from a `lane-snapshot` tree; `dominant_unsat` 262 / 324 → **269 / 326**, `lean-reconstruction-gap` 15 → **10**, certified/checked 278 → 280. Four rows moved: QF_NRA cvc5 (+3, `RealProduct`×2 + `MonomialBound`), QF_S (+2, `StringLength`), QF_NRA synthetic (+2, the prelude-warm instrument fix, proved by an A/B with the warm suppressed at two revisions), QF_SEQ (a `parse-error` became `sat`, no dominance change). `gen-proof-gap-matrix`, `gen-proof-gap-shape-census`, `gen-dominance-scoreboard` and `gen-autogenesis-baseline` regenerated; the six moved markers in `PROJECT-STATE.md` and the gap analysis renumbered **with** the account of what moved them, and the ten remaining Lean-reconstruction gaps recorded one line each with the fragment's own decline reason rather than the fallback route's. |
| 2026-08-21 | `a3799dca2` | **`QF_FP/fp_misc`'s "timeout" was an unmemoized DAG walk in the classifier.** `array_bv_abs::abstract_term` re-explored shared subterms once per path; 8/8 `gdb` samples sat in it. Memo + visit budget, each guard mutation-verified to kill exactly one test: **124.7 s timeout → 314 ms**, 4,194,309 visits → 4,365 over 5,762 nodes. QF_FP `timeouts 1 → 0`, certified/checked 15/16 → **16/16**; `dominant` stays 15/16 and the row now declares `bit-blast` instead of `timeout`, because `887b52e64` withdrew its term-level FP route on purpose. Also measured and pinned: `QF_BVFP/Float-no-simp3-main` is not the "evidence exceeds 120 s" it was recorded as — its reduction certificate is `proved` in **28.3 ms** and is withheld only by `produce_evidence`'s blanket "timeout set → skip", whose deadline covers the SAT search and none of `lower_terms` / `tseitin_encode` / `check_drat` / LRAT. QF_FP and QF_BVFP audits re-run at `a3799dca2`; `proof_errors` 4 → **3**, certified/checked 280 → **281**, and the four moved markers in `PROJECT-STATE.md` and the gap analysis renumbered with the account of what moved them. |
| 2026-08-21 | `17079b33d` | `:pattern` was parsed and dropped; the author's trigger now decides. Arena side table, alternatives unioned, multi-patterns joined, declines explicit. ADR-0537. |
| 2026-08-21 | `da314781b` | QF_NIA post-fix: 39/83 = 47.0%, **+6** on its own pre-fix sweep four hours earlier. Which corrects the batch note: `40a1ab969` — one file in `dpll_lia.rs` — moved FOUR divisions (QF_UFLIA +18, QF_NIA +6, QF_SLIA +2, QF_RDL +1), one of them strings and one nonlinear, where it was expected to move QF_UFLIA. Scoped to the expected division, three of those rows would have been recorded at PRE-FIX values under today's date with the freshness gate green over them. |
| 2026-08-21 | `f2060eeb2` | The freshness gate runs in hosted CI too — the third place the gap analysis named. Held back deliberately until the board was green, because a gate that reds CI on landing over a multi-hour sweep is one people learn to override. Runs in the `fetch-depth: 0` job, which is load-bearing: the solver-currency column needs history and degrades to NO-GIT on a shallow clone (verified against a `.git`-less tree — reports NO-GIT, still exits 0). |
| 2026-08-21 | `45587c513` | QF_NIA gap #4 diagnosed. "Multi-year catch-up" confirmed for the search — three cheapest levers yield 0 / +1 / +3 files, 4× clock buys 0 of 20 timeouts — and three premises corrected: **cvc5 is on this host** (`/nas3/data/axeyum/harness/bin/cvc5`, not on `$PATH`; two docs say otherwise), **z3 is 60 files from cvc5 here** (136 vs 76, cvc5's set a strict subset), and **the deficit is one family** (`VeryMax/ITS` = 74 of 104 misses; excluding it, 74.4 % of cvc5). `int-blast-ladder` decisive on 158/161; its constant-fit rule leaves **1 live rung on 32 files, 0 decided**. Four per-file passes committed. |
| 2026-08-21 | `b3ef9a965` | The refusal census picked the next thing to build, and it was not what the gap felt like. `(get-model)` declined 66 times over 400 corpus files and **58 were arrays**, against 6 uninterpreted-sort tokens; arrays now render as `(store … ((as const (Array I E)) default) …)` and the same census reads **166 rendered, 9 refused**. Also `DecidedQuery::proof_eligible`: a bounded-string `unsat` the gate did not confirm cannot draw an Alethe proof of the *packed* assertions. That one is defence in depth and says so — over 184 QF_S/QF_SLIA benchmarks, deleting it changes no answer, because the QF_BV emitter declines those shapes. |
| 2026-08-21 | `81361cdd1` | Gap #3's items 2–4. `solve_smtlib_session` answers `get-model`, `get-value`, `get-unsat-core`, `get-proof`, `get-assertions` and `echo` at the command where they stand; `set-option` reports `unsupported` for every option it does not honour; `(set-logic NONSENSE_XYZ)` says `unsupported` and still decides, as z3 does. `solve_smtlib_incremental` became the same walk with the output commands off, so no verdict could move — A/B over all 1,430 tracked `.smt2` at a 10 s budget: 2 differences, both on files that finish in 9.7–11.8 s, both binaries agreeing three of three at 60–120 s. 34 tests; 23 guards deleted one at a time, 22 killed a test and 16 killed exactly one. |
| 2026-08-21 | `326445bba` | Gap #6: `nra-even-power`, `finite-array-extensionality` and `finite-domain-pigeonhole` no longer checked by re-running their producer — 11 guards, 11 satisfiable-query fixtures, each deletion killing exactly one test. All 28 remaining re-run checkers classified: **16 instances are a complete decision procedure re-run, not the defect**; 14 across 5 families cannot be made independent without a certificate change and are now named in the code. |
| 2026-08-21 | `3a509de54` | Carcara HAS array rules: `check_alethe` gains `arrays_idx`/`arrays_row` under Carcara's semantics, `prove_qf_abv_unsat_alethe` emits `arrays_idx` instead of a name Carcara rejects, and `portable_artifact` decides Alethe portability from the artifact's rule vocabulary rather than its variant. Six guards, each deletion killing exactly one test. |
| 2026-08-21 | `4b0f001c7` | Built Carcara for the first time and ran the crosscheck suite: **5 of 79 tests failed**. Four hand-wrote stale `!fn_app_*` ids into the problem (fixed by reading them from the proof); the fifth found `bv_poly_simp` checked by neither checker. Adds the shipped ROW-same proof's Carcara acceptance, its negative control, and tamper rejection in both checkers. |
| 2026-08-21 | `f9ccdcb9d` | `alethe_portability_probe`: the first committed tool behind the "externally checkable" figure, plus the per-`ArrayAxiomKind` census showing the array-axiom family unreachable at every rung and why. |
| 2026-08-21 | `40a1ab969` | `crates/axeyum-solver/src/dpll_lia.rs` + ADR-0538 + `bench-results/lia-core-minimisation-20260821/`: theory-core minimisation rationed by an oracle-call work budget instead of a core-width gate. QF_UFLIA 92 → 114 (+22, −0) at 0 disagreements against z3 and 0 against the declared `:status`. |
| 2026-08-21 | (pending) | `docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md` + `bench-results/linear-arithmetic-diagnosis-20260821/`: gap #1 diagnosed — three causes not one, 800-file per-file classification, two A/Bs (one refuted, one +17 QF_UFLIA files at 0 disagreements). |
| 2026-08-21 | `9333f779d` | **`bv_nego` returned a wrong `sat` above 128 bits.** `1u128 << (w - 1)` with legal widths to 65536: Rust masks the shift mod 128, so at `w = 129` the term became `x == 1` instead of `x == 2^128` and the shipped `SatBvBackend` answered **`sat`** to an unsatisfiable query (measured with overflow checks off; debug panicked instead). Fixed by following `bv_umulo`'s existing wide branch. Corpus reachability, which the gap analysis marked UNVERIFIED: **0 of 1430** tracked `.smt2` files use `bvnego` (control: `bvadd` in 106), so it is reachable only from the parser on user input. Three tests close the width asymmetry that hid it — widths 129/130/191/192/193/256/4096 by value *and* by the constant's structure, the 128-bit boundary staying narrow, and the end-to-end backend verdict. Two guards, each mutation-verified to kill exactly one test, registered as `ir-bv-nego-width`. |
| 2026-08-21 | `d4ffe2a54` | **`SolverConfig::memory_limit_mb` was set but never read on the shipped build** — its only read was under `#[cfg(feature = "z3")]`, and `axeyum-verify`'s `tock_log2_external` had been setting a 2 GB cap on a non-z3 build where it bounded nothing. Now two mechanisms: a portable pre-allocation clause ceiling at a **measured** 384 B/clause (peak-RSS, fresh process per width; a plain `VmRSS` delta under-reports 3–7x and `VmHWM` is monotone, so both obvious methods fail toward *under*-charging), and a `/proc/self/status` probe (**9.4 µs**, 276x an `Instant::now()`, which is why it may only sit at a phase boundary) at three BV boundaries and both front doors. Measured against a tree without it: default path indistinguishable (182.8–183.4 vs 184.0–185.3 µs/check), a configured limit **+32 µs/check fixed**. All five guards **SURVIVED** the first mutation run because they shadowed each other; a scripted-RSS test seam plus direct reach to the post-encoding gate now has each killing exactly one test. A *faithful* bound still needs a `#[global_allocator]` hook — process-global, `unsafe impl`, needs per-query attribution — recorded as an open research question rather than an unspoken gap. |
| 2026-08-20 | `9eb81822f` | Isolate persistent pre-push worktree metadata from the caller lane and register the two-sided control |
| 2026-08-20 | `24b16642e` | Confirm the repaired hook against a live Rust push with unchanged caller state and a clean exact-SHA gate checkout |
| 2026-08-20 | (pending) | The string family's first re-derivable UNSAT artifact beyond word-clash/regex-emptiness: `Evidence::UnsatStringLength` abstracts every string term to an integer length keyed on its SOURCE NAME, names the five theory lemmas the argument uses, and closes with one nonnegative combination per case-split branch. The checker is two stages — bind each lemma to the conjunct that licenses it, then re-derive the arithmetic — and is arena-free, because a string script's flat view is the bounded packed-BV encoding rather than the query. 23 guards mutation-checked; two killed nothing and were fixed rather than kept (one was dead code the command allow-list already covered, one had no multi-`check-sat` fixture). Also: `diagnose_evidence` reported the ARENA front door for string files, i.e. a query nobody solves — it now reports the text front door too, and agreed with the dominance audit for the first time. |
| 2026-08-20 | `0797719a7` | Rational operands no longer defeat algebraic field arithmetic; the NRA `sat` witness replays and the evidence route matches the decision route |
| 2026-08-20 | (pending) | `Evidence::UnsatRealHandelman`: multi-term Handelman/Positivstellensatz refutations for `QF_NRA`, with case splitting over a top-level disjunction and polynomial multipliers on asserted equalities. Certifies the three corpus rows `nra_product_cert` declined by design. 15 guards mutation-checked; 14 kill at least one test, and the fifteenth (the producer's own self-check) kills nothing and is documented as such at the function rather than pretended to be a guard. Three checks that provably could not fail were deleted instead of kept. `NamedPoly` is now shared with `nra_product_cert` rather than reimplemented — two name-keyed polynomial types would be two chances to disagree about what `a*b` means. |
| 2026-08-20 | (pending) | `Kernel::whnf_core` is memoised — the second of Lean's two reduction caches (`m_whnf` beside `m_whnf_core`), which this kernel never had. `build_creal_prelude` 33.0 s → 13.0 s, template reuse 0.41 s → 0.15 s. Pure memoisation: same key discipline as the δ-free memo, split on `has_fvars`, cleared by `push`/`pop` and by environment revision, closed half covered by the `reduction_ctx_reads` tripwire. Six guards mutation-checked, each killing at least one test and four killing exactly one; a seventh looked unreachable and a `debug_assert_eq!` proved it is not, which is what the comment on it now records instead of the argument that was wrong. Root cause recorded: `502184d3f` did not slow the kernel down, it switched the literal-`Nat` acceleration ON for the first time, because `build_nat_binop_table` gates on `Bool`'s constructor order. |
| 2026-08-20 | (pending) | `Kernel::reduce_nat_binop` moves out of the δ-free normaliser to Lean's two call sites — `whnf_core`'s δ loop (Lean `whnf`, `type_checker.cpp:670`) and `lazy_delta_step` (Lean `lazy_delta_reduction`, `:978`) — both under Lean's `!has_fvar` guard. `build_creal_prelude` 12.99 s → 6.79 s (median of three interleaved rounds), against 8.71 s before the acceleration was ever switched on. Measured separately: Lean's placement *without* the guard is 12.12 s, so the guard is the entire win and the placement is faithfulness, not speed. Identification unmoved — kernel lib 399/0; full kernel crate 609 passed / 1 failed, the one (`real_lean_wellfounded_elaborator_divergence`) failing byte-identically on an unmodified `HEAD` and being a real-Lean *elaborator* rejection rather than ours; solver `reconstruct::` 312/0; clippy 618/618 targets 0 diagnostics; prelude-reuse differential `compared=8 failures=0`; axiom ledger `axreal=30` and all others 0. Three new tests in `tests/nat_literal_arithmetic.rs` pin both call sites and both guards on an environment where the accelerated answer and the declared body disagree; each guard mutation kills exactly one. ADR-0536. |
| 2026-08-20 | `01d54044a` | **Certified 278/324 (85.8%)**, from 267/327 (81.7%) this morning. Timeouts 10 -> 4, `proof_errors` 10 -> 4. Four of the recovered rows were emitters that had returned the CORRECT answer and were billed 31.9s of shared prelude construction inside a 15s cap; `prelude_warm_ms` is now a visible artifact field instead of one instance's bad luck. |
| 2026-08-20 | `5a25f247a` | **Four DAG walks were exponential today, all the same bug written four times** — `contains_quantifier`, `lower_derived_bv`, `collect_enumerable_symbols_rec` (1.28e10 calls in 90s), `collect_nested_registrations`. `Float-no-simp3-main` >300s -> 19.4ms, `fp_fromsbv` 45s -> 3.8ms. The `certify.rs` memo deliberately does NOT collapse occurrences for the quantified-bit budget: that is a tree-sum, and collapsing it would undercount an exponentially shared quantifier nest and let a query past a budget check it cannot satisfy. |
| 2026-08-20 | `609417c9e` | `MAX_UNARY_TERMS` 4096 → 128: mutating the size guard away aborted the test binary rather than failing a test (cost 1026 overflows the stack; cost 514 renders a 13.2 MB module), so the budget admitted the crash it existed to prevent. Now pinned from both ends. The inequality sign re-check killed nothing and was deleted — positivity is enforced upstream by `checked_refutation` and downstream by both Farkas engines. The hypothesis-count check and the external `infer == False` re-gate also kill nothing and are kept, with the mutation pair that shows what the first one does (removing the equality registration kills 7 tests *through* it; removing both kills 1 and ships a quietly weaker module). New `lean_crosscheck` family `qf_s_string_length`: real Lean 4 accepts both modules, 173/173 in the full sweep. |
| 2026-08-20 | `b495a396e` | The string-length certificate reaches the kernel. `reconstruct_string_length` folds the certificate's own facts into a `False` over the constructed integers; `checked_refutation` is now the single derivation both `check_string_length_refutation` and the reconstruction read, so the exported view cannot drift from the validated one. An asserted **equality** enters as an equality — `LraReconstructCtx` grew `hyp_overrides` so the route mints `a = 0` and derives the `≤` half rather than assuming it, which is the one distinction the certificate's fact table turns on. A single-disjunct `(or A)` declines: the query states the disjunction, not the disjunct. Variables are named after their source (`len_xx`, `code_x`). `Evidence::UnsatStringLength` became a struct variant carrying `lean_module: Option<String>`, re-derived on `check` and never read back; a decline is `None`, not a weaker certificate. No `ProofFragment` variant — `scan_proof_fragment` is arena-based and a string script has no faithful arena. |
| 2026-08-19 | `pending` | `scripts/check-kernel-suites.sh`: the kernel's push-time / real-Lean suite partition, discovered from the source and asserted total; `hooks/pre-push` repointed at the non-Lean half (2,296 s → 80 s warm). Found `real_lean_string_monoid_crosscheck` owned by nothing and mis-formatting its check count; floor 218 → 219. |
| 2026-08-19 | `e3e105cd6` | The local-ci freshness gate is ENFORCING in both `check.sh` and `justfile`, on a `PASS` record (`57af69142-s4.json`, 6656 s, 7561 tests + 179 doctests, no vacuous/unreadable step). Landed report-only the day before because the only record was FAIL; that was the sole blocker. Flip re-tested through the real call site: NO_RECORD / STALE / STEP VACUOUS all red, unmodified green. |
| 2026-08-19 | (pending) | `artifacts/local-ci-runs/57af69142-s4.json`: first all-pass authoritative-gate record (5/5 steps, 7561+179 tests, 6656 s); `check-local-ci-freshness` flipped from `--report-only` to ENFORCING in `scripts/check.sh` and `justfile`. |
| 2026-08-19 | `ae0676aec` | `docs/formalized-math-2026-08/` corrected against measurement: "system-proved theorems = zero" falsified (3 facts, re-derived, heavily qualified; C2 still zero); C1 landed 2026-08-14 and did **not** deliver `N x 149/day`, so the single-file-lock diagnosis is falsified by its own remedy; the rate metric retired as unmeasurable across preludes; ADR-0517/0518's two-checker finding and the 122-declaration coverage hole recorded, with the limitation stated at its true width (shipped artefact does not carry the whole carrier; 4 declarations kernel- but not elaborator-checkable). |
| 2026-08-19 | `4c7af898d` | **ℝ is a lattice.** 15 `Rat` + 18 `CReal` declarations, every one accepted on first submission, all footprint-free. The predicted obstacle — a four-way sign split over `|a| − |b| ≤ |a − b|` — never appears. Nothing here has a side condition, so the failure mode is a *degenerate operation*, not a vacuous guard: `max x y := x` satisfies `le_max_left` by reflexivity and `abs x := x` satisfies `le_abs_self`, `neg_le_abs` and `abs_le`. So `not_le_zero_neg_one` and `not_equiv_abs_neg_one` are proved from the laws alone, the witness's exit status depends on both, and `max x x ≈ x` / `max 0 1 ≉ 0` / `min 0 1 ≉ 1` are admitted **through the kernel**. One level down, `Rat.max`/`Rat.min` are checked to COMPUTE on both branches with the wrong answer REFUSED — the nine `ℚ` laws are all one-sided and would hold of a projection. Three one-token mutations refused. |
| 2026-08-19 | `e9f5cf287` | **The mathematics strand stops advising against work that is finished.** `02` gains a dated ℝ/ℂ status block, a `ℂ` row and a corrected `ℝ` row in the construction-order table, measured prelude counts, and a "not built" table with reused costings (cotransitivity ~400 lines, `apart_mul` ~300, completeness/`sqrt`/suprema uncosted, ℂ `abs` downstream of both). `05`'s D3 is re-ordered rather than deleted: it was a pre-flight check on a construction order that has since been walked, and is now a coverage measurement against Mathlib. `04` closes R4 and keeps the 30 `Real` axioms as the ADR-0509 negative control. `01`, `03`, `README` and `diary-real-keystone.md` corrected in place. |
| 2026-08-19 | `c26e492b1` | **The axiomatized reals are renamed `AxReal` (ADR-0522 step 1), and two green assertions were reading the wrong carrier.** `CReal` contains `Real`: a front-door test asserting `contains("Real.add_le_add")` was satisfied by `CReal.add_le_add`, and `infeasibility_farkas_lean`'s ordered-field scan by `CReal.le` — the latter is a `proved` fact's checker command. One string literal moves the whole 30-row package. `--accept-rename OLD=NEW` is new: routing a rename through `--accept-population-change` would have published 30 retirements that never happened. |
| 2026-08-18 | `4b5613e26` | `check-fact-derived-numbers.py`: every number a fact asserts about its own `axiom_footprint` re-derived from the array. Fixes `F:schedule-critical-chain-infeasible` (prose 30 vs array 26, plus an obsolete facade paragraph found by re-measuring: `Lra`/62 lines, not a 21-line shim) and the example's stale module doc. 52 of 3,243 prose numbers bound, denominator printed every run; 7 guards, each deletion kills exactly 1 test; wired into both `just check` (`facts`) and `check.sh` so `check-aggregate-scope.sh` records no new divergence. |
| 2026-08-18 | `24578036f` | `gen-lean-axiom-ledger.py`: coverage command gains `--include-constructed` (on `--release`, 12x faster), `EXPECTED_PRELUDES` gains `rat`/`creal`/`complex`, and measurement drift is reported per prelude **with its direction** — REGRESSION / IMPROVEMENT / COVERAGE LOST / ADDED / RESHAPED, each with the re-pin command. Ledger now pins 8 groups by value (was 6); 39 tests (was 24); 11-mutation control registered in `mutation_controls.py`, no survivors. Already wired in both `check.sh` and `just check`, so no new gate divergence. |
| 2026-08-18 | `7646b2c04` | `reject_self_refuting_module` at `gate_module_content` — the one boundary every route's module crosses; the Python predicate widened from one shape to the property and run over EVERY class; DECLINED pinned two-sided in its own manifest; the shadowed attested-path copy deleted after the mutation control that used to kill a test reported SURVIVED. 6 mutations, 0 survivors; 9 Rust unit tests, each with its discriminating twin. |
| 2026-08-18 | `31442bd5d` | `quant_{affine_growth,counterexample_cover,eq_partition,residue}` — four golden Lean-module pins re-pinned at cause (+1 640 header bytes from `b760fd6ae` and `46724faec`), unredding `main`. Found by the first completed run of the authoritative gate. |
| 2026-08-18 | `e069afa03` | `local-ci`: the zero-test guard could not fire on the workspace sweep — nextest's summary is indented and the pattern was `^`-anchored. Fixtures now captured from the tool; a test step whose count is unparseable is `unreadable` (89), not `pass`. |
| 2026-08-18 | `69c12646c` | `artifacts/local-ci-runs/a6ee37c6a-s4.json` — first completed run of `scripts/local-ci.sh` in this repository's history. FAIL, 6401 s, 4 of 7511. |
| 2026-08-18 | `a2841965e` | `local-ci` gates the COMMIT, not the working tree: stable flock'd detached worktree, `--no-worktree` opt-out, controls mutation-tested. |
| 2026-08-18 | `PENDING` | Lean has two checkers (ADR-0517): the kernel accepts all 470 carrier declarations, the elaborator refuses those whose checking must reduce a `theorem`. `real_lean_creal_carrier_kernel_replay` (whole carrier, no reachability filter, count-equality + tamper control) and `real_lean_wellfounded_elaborator_divergence` (`gcd` refused / `mod` accepted / same module with `theorem`->`def` accepted / kernel takes both); gate floor 212 -> 218. |
| 2026-08-18 | `00f998ccb` | ℤ categoricity: the existence half of the universal property (`iter` + three preservation equations, making `Int` the initial ℤ-structure) and `categorical` — every generated aperiodic ℤ-structure is in structure-preserving bijection with `Int`, universe-polymorphic. `iso` is the constructed two-sided-inverse form, honest about hypothesising the back-map. 32 theorems, all footprints empty; 22 injected weakenings each refused at their own declaration, now bracketed by `reached_declaration` on the near side too. |
| 2026-08-18 | `a2a36590b` | `F:int-categoricity` recorded, and `F:int-characterization`'s "not proved that they determine it" caveat removed because it stopped being true. Every checker anchored on the declaration name AND the empty-footprint column, each run with its subject mangled: 0 on the finding, 1 on the mangle. |
| 2026-08-18 | (pending) | ADR-0512 phase R3: the ordered-ring telescope gains an equality slot (30 → 39 binders) and `specialize_setoid_to_eq` proves it specializes back to today's statement — conclusion **and** all 30 non-slot binder types, node for node. Three mutation kills recorded; `residual_eq_constants` guards the one failure the footprint cannot see. |
| 2026-08-18 | (pending) | `Sos` reconstruction accepts a **nonzero affine row** in the `LDLᵀ` linear forms (`rational_affine_squares`, `int_affine_lin_to_rexpr`), so `Σ xᵢ² + 1 < 0` and `(x−1)² + (y−2)² + 1 < 0` reconstruct instead of emitting `axiom P; axiom Not P`. The transcription checker's two normalizers learned degree-2 monomials to match, with square/cross discrimination driven to failure six ways. Binding gate `instances=125 → 135`, `attested=28 → 19`, `failures=0`. |
| 2026-08-18 | (this change) | Round 3: corpus widened 51 -> 66 mutation families over a development that now carries a Type-valued structure, a `Nat` literal, an indexed family, a parameterized family and a mutual group; a fourth defect found and fixed — a **recursor's** `levelParams` was decorative, because a recursor is generated and compared rather than admitted, and the comparison's positional alpha-rename leaves an unbound parameter untouched |
| 2026-08-18 | `2633d7186` | Kernel-vs-Lean differential widened to 51 mutation families; recursor/constructor regeneration compared against Lean's own, closing the 37% of the stream `addDeclCore` never reads; two defects fixed — universe closure on `check_declaration` **and** the inductive gate, and the recursor `k` flag validated on import |
| 2026-08-18 | (pending) | ADR-0512 phase R4: `build_creal_model_of_arith` — the `Real` axiom package modelled by the **constructed** reals. 22/22 witnesses axiom-free, 9/22 restated over `CReal.Equiv`, 7/7 discrimination witnesses, exit status depending on all of it (`creal_model_witness`). Four mutation kills; ADR-0456's "`Int` is not ℝ" caveat discharged. |
| 2026-08-18 | (this change) | Round 4: the fourth admission gate (`restore_nested_inductive_group`) gains adversarial coverage — the auxiliary recursor was never unread by Lean's kernel, only by `Environment.find?`, the elaborator's lookup; the replay script now asks `env.toKernelEnv`, a nested group is on the wire, and 14 `ind.aux-*` families cover it. 0 violations in 274 and 752 mutants, 80 families; residue measured exhaustively and is one non-type-checking field |
| 2026-08-18 | (pending) | `LraReconstructCtx`'s carrier is a parameter: `RingSignature` + `RingEquality` replace the by-value `ArithPrelude`, `with_ring_signature`/`try_new` replace the panicking constructor, and five mutation-verified guards check a signature against the kernel. `CReal` passes them today with `CReal.Equiv` in the equality slot. Baseline output byte-identical. |
| 2026-08-18 | (pending) | **ADR-0512 phase R4 reaches reconstruction: `LraReconstructCtx::adopt_setoid_equality` fills the ring interface's equality slot from `CRealPrelude`'s own theorems, and a Farkas/SOS refutation over the CONSTRUCTED reals rests on zero carrier axioms.** Measured on all five `ordered_ring_refutation` fixtures: 30 carrier axioms over `Real` against **0** over `CReal`, and the slot costs **0** declarations against 18 for the `Real` route — both read out of `Environment::len` and `Kernel::axiom_footprint`, with the `Real` column as the in-output control. Four adoption guards plus the ctx's one-slot rule, each killed by exactly one test under mutation. The nine slot-member types come from one builder shared with `declare_setoid_equality`, so an interface change cannot move only one of them. `--require-empty` output is byte-identical to before. |
| 2026-08-18 | (pending) | **`PreludeKey::CReal`, and the shipped LRA/SOS front door moves onto the constructed reals.** `build_creal_prelude` 43.97 s -> **0.149 s** per call (debug; release 4.69 s -> 0.067 s) via the ADR-0464 template. `prove_unsat_to_lean_module` now reconstructs over `CReal` with an adopted equality slot: carrier axioms 12/17/8 -> **0/0/0** on three front-door fixtures, `Real` control non-empty, module axiom lines equal the kernel footprint. Also fixes a module-renderer ordering defect the constructed carrier exposed, which rejected 5 of 77 `lean_crosscheck` families; 77 of 77 now check under lean 4.30.0. Cost: modules 2.4-41 kB -> ~2.6 MB. Every new guard mutation-checked, exactly one test dead each. `nat_axiom_inventory --include-constructed` is now under the prelude-reuse differential gate. |
| 2026-08-18 | 61c466b53 | **The shipped front door reaches no `Real` axiom, measured at `build_arith_prelude` itself.** `RingSignature: From<IntPrelude>` + `try_new_over_integers`; `reconstruct_int_farkas_to_lean_module` off the `Real` package. `arith_prelude_builds()` = 0 across all four arithmetic arms, 1 for the control. Mutation-checked twice, exactly one test dead each — and all 9 tests of the suite named for that route pass under both mutations. Fact + ADR-0509 (declared vs reached). Also unbroke `clippy` on STABLE, red on `main` since `94d51fbc6`. |
| 2026-08-18 | `5734b7449` | **Positivity is closed under multiplication**, over ℚ and over ℝ. Not one of the 22 — they give `mul_nonneg`, of which the zero product is a model — and over ℚ it is a *field* lemma, going through `inv_pos`. Over ℝ it needs no estimate: `CReal.lt`'s rational gaps plus `ofRat_mul`. First proof to open the strict order's `Exists` twice, which works because the target is a `Prop`. |
| 2026-08-18 | `fc52b07f3` | **The inverse's domain, both directions, and the Prop/data line drawn correctly.** `0 < x` and `∃ k, 1/(k+1) ≤ x` are the same proposition, and the `Exists` is a `Prop`, so the modulus can never be extracted into a `CReal`. It is *computed*, not searched: `CReal.lt` already carries a rational gap. **Corrects the previous commit's doc** — a function may TAKE a `Prop` and return a `Type`, it may not BRANCH on one, so the disjunctive `Apart` blocks a definition and the one-sided `PosBound` does not. Plus `CReal.ofRat_le`, `Rat.natDivSucc_pos`. |
| 2026-08-18 | `b91b6dac5` | The four ordered-field lemmas ℝ's inverse is written in — `sub_mul`, `mul_inv_sub_one`, `inv_sub_inv`, `inv_le_of_pos_le` — from `mul_inv_cancel` and the 22 alone, so each transcribes one level up. |
| 2026-08-18 | `6375d7746` | **ℚ is a FIELD.** `Rat.mul_inv_cancel : 0 < q → q·q⁻¹ = 1`, axiom-free: the one proof here about the representation, since `Rat.inv q` is stuck until `num q` is in constructor form. The `negSucc` branch needs no lemma — `Int.lt Int.zero (negSucc m)` **ι-reduces to `False`**. Guard: `Rat.inv (2/1)` REDUCES to `1/2`; the identical script pointed at `= 2/1` is REFUSED. |
| 2026-08-18 | `baf81fd66` | ℝ gets **Bishop apartness**, verbatim rather than encoded — `CReal.lt` already carries the separation as a rational gap. Four laws, `not_equiv_of_apart` ONE-WAY (its converse is Markov's principle), and `CReal.no_total_inverse`. |
| 2026-08-18 | `57af69142` | **`CReal.inv` is built**, with `mul_inv_cancel`, `inv_congr` and `inv_index_irrelevant`, all footprint-free and accepted on FIRST submission. Index `(C+1)n + C`, `C+1 = (4k+4)(k+2)`, read back *two* ways so `natDivSucc` still need not be antitone. Non-vacuity is admitted **through the kernel** (`PosBound one 0`), and `∀h, ¬(1⁻¹ ≈ 0)` follows from `mul_inv_cancel` alone, so the operation is neither vacuous nor the zero function. Negative controls: `x·x⁻¹ ≈ 0` and `x⁻¹ ≈ x` both REFUSED. |
| 2026-08-18 | `facde4243` | The two ℕ/ℚ lemmas the index arithmetic is written in. `Rat.inv_natDivSucc : (1/(m+1))⁻¹ = (m+1)/1` — the only place the *value* of an inverse is computed, and needed because every bound over ℝ is one `natDivSucc` with a `Nat` numerator. `Rat.nat_index_symm : (a+1)b + a = (b+1)a + b` — **Bishop's sampling index is symmetric in shift and argument**, which is how a bound read at a product index comes back to the *shift* rather than to `n`. |
| 2026-08-18 | 570b5c738 | **The interface as a telescope, and it is the same over ℤ.** `ring_interface_telescope` + `examples/ring_interface_pin.rs`, 30 of 30 byte-identical. Also repaired a test `61906c585` swept in broken, and the finding behind it: a `NameId` is an INDEX, so a signature read against another *populated* kernel resolves silently to `Nat.le`, `Nat.beq_refl`, … rather than failing. |
| 2026-08-18 | 9ab8d7977 | **The negative control at one axiom instead of thirty.** `build_control_carrier`, three mutations, one test dead each. |
| 2026-08-18 | 6c08c906f | **ADR-0515** + `F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers`. |
| 2026-08-18 | `74946dd3b` | Split Lean module layout: `render_lean_prelude_module` / `render_lean_module_compact_importing` / `declarations_reached` / `lean_name`, `real_lean_shared_prelude_crosscheck` (4 real-Lean checks, 2 of them refusals), `examples/shared_prelude_module.rs --require-split`, gate floor 208 -> 212. 257x per query; found two `CReal` theorems Lean 4.30.0 rejects that the in-tree kernel admits. |
| 2026-08-18 | `035a92d9a` | ADR-0518: proofs stay spelled `theorem`. `Kernel::set_render_proofs_as_def` built as a `Kernel` field, OFF by default, so nothing shipped moves; 7 guards in `tests/proof_keyword_render_option.rs` (no `lean` binary, 0.69 s, so `hooks/pre-push` is unaffected), mutation-checked 1/1/1/1/2; `examples/proof_keyword_cost.rs` renders the front door, the shared half and the whole carrier both ways and `--require-keyword-only` fails if the switch moves anything but the keyword. Measured: the shipped artefacts already elaborate clean under `theorem`; flipping the default costs 1.36-1.69x elaboration, +9.7% on the Lean gate, and makes `real_lean_wellfounded_elaborator_divergence` report that Lean CLOSED the divergence. |
| 2026-08-18 | `c9223e4` | binding: the converse number says which side of the check the missing 245 rows are on — `undecomposable_spine=0` measured and gated, `represented` is a maximum matching rather than an overlap. |
| 2026-08-18 | `b9d2f0a` | binding: the 4 `FiniteArrayExtensionality` rows were never content-free — the emitter collapsed each `(select a i)`; `attested` 9 → 5, `structural` 98 → 102 with 360 new matched term nodes. |
| 2026-08-18 | `a25b18a` | binding: 66 rows were recording the weaker of two true statements — four verdicts become a partition with two-sided pins; `anchored` 10 → 73, `structural_anchored=66` new. |
| 2026-08-18 | `3076b6ae0` | the one Lean module `rfl` refuted on its own: root-caused to a degenerate `(t, t)` witness, the route now declines, and a self-refuting attestation FAILS the run instead of being counted |
| 2026-08-18 | `8e4894de4` | `ArrayAxiom` renders the query's own terms; a third `structural` verdict binds 95 modules to their query's subterms, 359 of 372 corruptions caught, and the attested class drops 124 → 28 with an anti-absorption guard |
| 2026-08-18 | `pending` | binding coverage: +20 bound (105 → 125), 124 modules proved content-free, and the converse direction measured at 286/531 |
| 2026-08-18 | (pending) | `gen-adr-index.py --check-remote`: cross-checkout ADR-number collision detector, wired into `just check` and `check.sh`; found a second live collision (0468-0470) beyond the one already fixed today (471-474) |
| 2026-08-18 | (pending) | `lean_pp::split_module_banner` + `tests/support/lean_golden.rs`: golden pins cover the module BODY, banner pinned once as committed text in `module_banner_pin`. |
| 2026-08-18 | (pending) | `scripts/check-lean-golden-pins.sh` (+ controls): the golden-module gate, membership DISCOVERED not listed; wired into `just check`, `check.sh`, and diff-scoped `hooks/pre-push`. |
| 2026-08-18 | (pending) | `mutation_controls.py`: a mutation check can no longer report a result it did not measure. `DID NOT BUILD` / `DID NOT RUN` / `AMBIGUOUS ANCHOR` / `INCONSISTENT` are distinct from `killed N` and `SURVIVED` and are counted separately; build probe, two independent kill counts, baseline test count, verified restore, and a `cargo` runner for the route the defect was reported on. `self-demo` demonstrates all four outcomes live; `mutation-controls` mutation-checks the harness (24 guards, 31 controls, 24/24 killed after 3 real survivors were fixed). Found and repaired two dead controls in `lra-hypothesis-binding` (53/53), and one mutation in `lean-axiom-ledger` that was scored as a kill while running **zero** tests, so that control is 10 guards and not the 11 recorded. Wired into both `just check` and `check.sh`. |
| 2026-08-18 | `pending` | **ADR-0521: ℂ is constructed over the constructed ℝ at zero trusted declarations, and ℂ's absence of an order becomes a theorem.** `Complex` is `mk : CReal → CReal → Complex` with `Complex.Equiv` componentwise — no quotient at either level, so `Quot.sound` is never needed. Every ℂ law reduces by δι to two `CReal.Equiv` obligations that are *algebraic*, so they are **decided, not hand-derived**: `complex/ring.rs` normalizes a `CReal` expression to a sorted multiset of signed monomials with opposite pairs cancelled and emits the `Equiv` proof, declaring nothing (every function returns a proof term, in `shifted_bound_le`'s style), so the `CReal` namespace and the trusted surface are untouched by construction. `add` and `mul` are the same commutative monoid, so the reassociation machinery is `rsum_perm`/`iprod_perm` written once against an `Op` tag, one level up and over a *defined* equality — the transcription ADR-0512 predicted. Landed with `conj`, `normSq`, `mul_conj` (`z·z̄ = ‖z‖²`, the law that needs the cancellation pass) and `normSq_nonneg` into `CReal`'s existing nonneg cone. **The finding that is not a construction:** `Complex.no_compatible_order : ∀ le lt, le_refl → lt_irrefl → lt_of_le_of_lt → add_le_add → le_congr → sq_nonneg → zero_lt_one → False`, proved directly with no classical step, so the 13 order laws are refuted rather than skipped. |
| 2026-08-18 | `590e2ff8c` | **ADR-0512 phase R2 completes: all 22 ordered-ring laws hold over the constructed ℝ.** `mul_assoc`, `left_distrib` and `mul_le_mul_of_nonneg_left` land, plus `mul_congr` — the fifth congruence obligation and the R4 prerequisite. The four were one problem: each compares two products whose *sampling indices differ*, so `CReal.mul`'s exact estimate is unavailable and the naive bound is `C/(n+1)` for a `C > 2`. Two new pieces make that enough. `CReal.Equiv.of_bounded` — **`Equiv` only needs the difference to be `O(1/n)`; the constant is free** — is `Equiv.trans`'s argument with one term deleted, closing on `Rat.le_of_le_add_natDivSucc`, whose numerator is a `Nat` *parameter* so a symbolic `K` is as good as a literal; and `Rat.nat_index_compose` says **Bishop's sampling indices are closed under composition** (the additive shift `2n+1` is the `c = 1` case), so every nested index reads back at `n` through one `natDivSucc_le_scaled`. `mul_le_mul_of_nonneg_left` needed no estimate at all, exactly as costed — it is `left_distrib` + `mul_nonneg` + `mul_congr`. **22 of 22**, 58 declarations, trusted surface still 0, and the count is now read out of the kernel: `CRealPrelude::ordered_ring_laws` must name 22 *distinct* footprint-empty theorems matching `RatPrelude::ring_laws` position by position, asserted by the example's exit status and three tests, verified by deleting `mul_assoc`. |
| 2026-08-17 | `67960fc1c` | D3 grouping refuted at the point of execution: arithmetic-as-a-directory grows the largest dependency cycle 58,215 → 103,514 lines. `analyze_solver_group_collapse.py` + mutation controls; no files moved. |
| 2026-08-17 | `d23a9d883` | `Nat.exists_prime_dvd` — every `m ≥ 2` has a prime divisor — admitted axiom-free in a new `nat_prelude::primes` module, with `Nat.le_of_dvd`, `Nat.two_le_succ_or_eq_one` and `Nat.least_divisor_search` beneath it (137 Nat theorems, up from 133). Recorded as `F:nat-exists-prime-dvd`, whose `kernel-term` checker pins the entire rendered type rather than the name — verified against the `1 ≤ p` weakening, which the kernel accepts and a name-only grep would not catch. |
| 2026-08-17 | `8f8c12dce` | ℕ-induction wired into `solve` as the last rung of the quantified ladder (`unknown` → `unsat` only, on `original_assertions` because normalization + skolemization have erased the negated universal by that point). New `tests/nat_induction_adversarial.rs`: 22 adversarial shapes, hand-derived truths, measured on the route and through the front door, 0 violations. Fixed an index-out-of-bounds panic in `is_nonneg_guard` on one-argument guards. `nat_induction_corpus` re-measured (3 contradictions → 0) and its gate widened to the front-door column. Both suites mutation-verified. Blast radius: `--lib` 1159 unchanged, `corpus_regression` 152/0 DISAGREE unchanged, whole crate 285 suites / 3861 tests green, clippy and fmt clean. |
| 2026-08-17 | `pending` | `string` prelude reaches **axiom=0**: `append` becomes a checked `Str.rec` recursion with four proved monoid laws (ADR-0513); ledger `total` 31 → 30, row filed as retired; real-Lean cross-check pins that `#print axioms` names no `axeyum.string.*` row. |
| 2026-08-17 | `fae708aa5` | Characterization theorems: our ℕ proved categorical (any Peano structure is uniquely isomorphic to it), our ℤ proved no-junk + generated by 1 + discrete everywhere + unique maps out. 18 theorems, all footprints empty; 9 injected weakenings each refused at their own declaration. |
| 2026-08-17 | `f532e04d3` | Restored `rat_prelude` after `fae708aa5` reverted `cf205e9a8`: a per-lane index refreshed in one shell invocation and committed in the next, with HEAD moving in between. The refresh must be in the SAME invocation as the commit, and `git show --stat`'s file COUNT is the tell — the diff you expected to see is not. |
| 2026-08-17 | `b15debdfa` | One Lean resolution policy (the `lean-toolchain` pin) shared by `check-lean-gate.sh` and `lean_probe.rs`; every suite names the binary and version it used and the gate cross-checks them; `replay-lean4export.lean` elaborates under 4.30 and 4.34; exercised negative controls in `scripts/tests/test-lean-toolchain-policy.sh` (ADR-0514) |
| 2026-08-17 | `pending` | transcription: bind every rendered Lean hypothesis back to the query text — 105 instances, 248 hypotheses, 869 corruptions caught per run |
| 2026-08-17 | `7337f708` `caaf2906` | A SKOLEMISED refutation certifies: the elimination is recorded POSITIONALLY (binder counts, anchor by index, a binding as "the k-th witness of assertion i"), so the checker re-runs the eliminator in its own arena and no producer-side id is trusted. `F:barber-no-such-barber` closes on `smt-clausal` with a NON-EMPTY axiom footprint naming skolemisation and universal instantiation. The negative control failed on purpose and moved to `F:no-integer-square-is-minus-one`; the gate now sweeps 18/18. |
| 2026-08-17 | `ae13cd6e` | A kernel fact's `depends_on` is DERIVED from the proof term, not transcribed: `Kernel::theorem_dependencies` keeps the half of the constant closure `axiom_footprint` discards. 18 edges were missing — two of them on facts proved the same day, by hand. Isolation 65 → 62. Restraints pinned by tests; the vacuity floor had no test until mutation-checking found it killed zero. |
| 2026-08-17 | `07ffe852` `9853fb6c` `28755674` | The e-matching route certifies, on the third design. It first shipped `certified=1` on evidence whose independent re-check said FAIL (one instance passed by `TermId` coincidence, two did not); reverted, then made portable — instances rebuilt in the checker's arena, ground set rebuilt rather than stored. `tests/certified_implies_revalidatable.rs` is the guard that caught it and now licenses it. |
| 2026-08-17 | `c2365718` `4cd5d6f0` `c5f4c04b` `078b2776` | The Lean gate stops overstating: 41 of 74 crosscheck families hand Lean an `axiom P` shim, so the headline is split, the reasoning half floored, and every fragment's class pinned by name. `qf_bv` was a WIDTH, not a defect — enumeration beats bit-blasting below ~16 bits — so `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation). |
| 2026-08-17 | `3cc574c7` `502c0503` | Both counted proof-production errors closed (`int_blast`'s deliberate `int.pow2` decline was mapped to a backend error, losing a verdict `check_auto` decides in 0.13ms), and settled SMT-route facts gated on certification rather than verdict — 17 of 17, enforced. |
| 2026-08-17 | `ea9500bc` `e97db72b` `2c535667` `f40f7dc4` | Gate repairs: `check-parity-docs.py` crashed before running a single check (hiding 14 failures); CI's crosscheck grep still pinned 73 families; and `PLAN.md`'s sources were 24 KB over a 52 KB budget, journal moved to result notes. |
| 2026-08-17 | `f18904db7` | R3: reachability census re-derived and committed as `artifacts/reachability/r3-census.tsv` (190 rows over both corpora); the ranked tables in `04-reachability.md` are now a generated view of it, gated by `scripts/check-reachability-census.py` inside `check-foundational-resources.sh`. 13 guards, each with its own rejection path; mutation-verified that deleting any one kills exactly one test. Corpus coverage checked in both directions and reported SKIPPED, never passed, when the sibling checkout is absent. Stale numbers corrected in `04` and `05`. |
| 2026-08-17 | `pending` | ADR-0512: ℝ is a Bishop setoid over ℚ at **zero** trusted declarations, with `creal_shape_probe` measuring the carrier's admissibility against a `funext` negative control; ℂ scoped and deferred. |
| 2026-08-16 | `pending` | Claim dashboard regenerated and gated: `gen-claims-dashboard.py --check` added and wired into `generated-trackers` (justfile) and `check.sh`; `validate-claims.py` now type-checks `frontier.known` / `would_settle` / `attack_notes` against `claim.schema.json`; the one schema-violating claim normalised. DASHBOARD.md goes from a stale 38 claims / 1 family / 81 rows to the actual 104 / 3 / 266. Both negative controls exercised. |
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

**The prose half of the ledger is now derived, not transcribed** (`WIP`,
ledger-freshness, 2026-08-18). `F:schedule-critical-chain-infeasible` said "the
30 axioms the kernel module actually rests on" for three days after its
`axiom_footprint` was corrected to 26 — with a correct `--expect-axioms 26`
sitting in the same JSON object. `depends_on` and the footprint array are both
derived and gated; the sentences *about* them were not, and nothing in the ledger
linked a number in English back to the thing it came from.

`scripts/check-fact-derived-numbers.py` closes that for one quantity, and only
one. It anchors **structurally**, not lexically: an `evidence[i].supports`
beginning with the literal field name `axiom_footprint` (the ledger's existing
convention, 48 slots), plus `--expect-axioms N` inside a command. Measured
2026-08-18 it binds **52 claims across 48 slots, 1 unchecked, out of 3,243
numeric tokens in fact prose** — and the docstring names the 3,191 it cannot see.
That gap is deliberate: 3 of the 7 phrases matching a naive `N axioms` regex are
about Peano's axioms, Armstrong's axioms, and a *different* theorem's footprint,
so a lexical gate over all of them would be 43% wrong and worse than none.

Seven guards, each with a fixture that trips it and no other; `mutation_controls.py
fact-derived-numbers` deletes each in turn and **every deletion killed exactly one
test**. Exit status was demonstrated on a scratch fact carrying the original stale
wording: exit 1 with three FAIL lines naming field and both numbers, exit 0 either
side of it.

Detail moved to [`../notes/100-ledger-freshness.md`](docs/plan/notes/100-ledger-freshness.md).

**The pre-push kernel step ran the real-Lean suites a second time; it no longer
does (`DONE`, agent-prepush-scope, 2026-08-19).** `hooks/pre-push` ran
`cargo test -p axeyum-lean-kernel` wholesale. Fifteen of that crate's 46
integration suites hand modules to a real `lean` and `scripts/check-lean-gate.sh`
already owns them — with a pin, a counted floor and a no-skip rule this step had
none of. Measured warm on s4: **2,296 s → 80 s.**

The deliverable is not the split but the assertion that it is total.
`scripts/check-kernel-suites.sh` DISCOVERS membership (a suite is real-Lean
exactly when it carries `#[path = "support/lean_probe.rs"]`, the same
"membership is the act itself" shape as `check-lean-golden-pins.sh`) and fails if
any `tests/*.rs` is in neither half — so removing duplication cannot silently
create a suite nothing runs. A hand-written list of 31 names would have been a
list someone forgets to extend, failing silently.

**It found one on its first run.** `real_lean_string_monoid_crosscheck` (landed
2026-08-17) invokes a real Lean and was in no gate's table; only the wholesale
`cargo test` ever ran it. It also printed its count as
`AXEYUM-LEAN-CHECKED|string-monoid|1|…` where the gate parses
`AXEYUM-LEAN-CHECKED <tag> checked=<n>` — so it would have summed as zero.
Both fixed; `CHECK_FLOOR` 218 → 219, verified `checked=1` against the pin.

The step is now diff-scoped, and unlike the frontier ratchet's filter this scope
is **derived**: the crate's `Cargo.toml` has one dependency (`num-bigint`) and
nothing from this workspace, so no other crate can move these suites. The
partition assertion runs on either branch — it is what makes the skip safe.

10 guards, 10 controls, each deletion killing **exactly one** control. Needed one
mutation-harness fix: `Unittest.build` ran `py_compile` on every subject, so a
shell subject scored `DID NOT BUILD` on all ten — unmeasurable, in the harness
built to tell that apart. Shell subjects now use `bash -n`.

Detail in [`../notes/100-prepush-scope.md`](docs/plan/notes/100-prepush-scope.md).

**The axiom ledger now pins all eight prelude groups by value and names the
direction a number moved** (`WIP`, expect-axioms, 2026-08-18). The brief's
premise was mostly already met and one of its numbers was wrong: **28** fact
files (not 58) run `nat_axiom_inventory` in a `checker_command`, and the ledger
has pinned every *default* prelude by value since ADR-0465 — a fall fails that
comparison exactly as a rise does. Converting those 28 would change no bit:
`--require-axiom-free L` pushes `(L, 0)` into the same list `--expect-axioms L=0`
does, and the only preludes any fact names (`nat` 23, `integer` 6, `logic` 2)
already measure 0, the floor.

The real gap was coverage. `creal` (ADR-0512) and `complex` (ADR-0521) were in
**no** measurement the ledger consumed — they need `--include-constructed`, and
the coverage command did not pass it — so their counts could move either way
unobserved; `rat` was measured but missing from `EXPECTED_PRELUDES`. All three
are now in both. A pin for a group the command never builds would pass
vacuously, so dropping the flag is itself a gate failure.

`--check` no longer prints two JSON blobs for the reader to diff. It reports per
prelude, with direction and remedy: a **rise** is a regression (something
previously proved is now assumed), a **fall** is a result the ledger has not
published yet — the direction a blanket axiom-free assertion structurally cannot
see, because it only ever becomes more true. Both fail; re-pinning is one
command. Demonstrated failing on 28 -> 30 and on 32 -> 30 and on a 1 -> 0, then
green.

Profile decided the shape: `--include-constructed` costs **2 m 03 s debug against
10.3 s release**, so the coverage command moved to `--release` — affordable once
in a generator that already runs, not affordable in 28 `checker_command`s.

Guards: `python3 scripts/tests/mutation_controls.py lean-axiom-ledger`, 81 s, 11
mutations, **no survivors**; ten kill exactly one test. The two that do not are
recorded, not smoothed over.

Detail, including a near-miss where the shared worktree briefly measured
`creal: axiom=30` — the whole `Real.*` package — from another lane's in-flight
prelude cache, in [`../notes/101-expect-axioms.md`](docs/plan/notes/101-expect-axioms.md).

**Not 124 attestations — 5. And a second Lean module that refutes itself, found
in the class the checker's own manifest said was "NOT checked"** (`WIP`,
attestation-gap, 2026-08-18).

Re-measured first. `check-lra-hypothesis-binding.py` reports **135 bound / 102
structural / 73 anchored / 5 attested**, not the `125 BOUND / 124 ATTESTED / 21
DECLINED` the brief carried. That figure came from
`crates/axeyum-solver/src/capabilities.rs`, which had been stale for a day;
lanes 93/94 had already moved 95 of the 124 to `structural` and 9 to `bound`.
The row is corrected. **A stale capability row is how a wrong number becomes a
brief.**

So the gap was closed before this lane started. The prior census generalizes: its
2-rewrite/3-unanchorable split is all that is left, and is understated —
**4 of the 5 are rewrite output**, both `replace_all` rows being a constant-fold.

The live hole was **DECLINED** — 20 instances the manifest listed and nothing
ran on. Two costs, both already paid:

- `extract-concat` rendered `Not (And (Iff prop._24 prop._24) …)` — eleven
  reflexive `Iff`s under one negation, so Lean's `False` follows from that one
  axiom with the `.smt2` file never consulted. The 2026-08-18 self-refutation
  check recognized `Not (Eq α t t)` only, and ran only over attestations.
  Widened to the property and run over every module: **4,652 axioms, 1
  self-refuting.** The emitter now declines it.
- The class is now a two-sided pin, and its first run as a check **evicted two of
  its own members**: the `bug593` rows bind structurally. Reading their φ is the
  lane's other finding — it maps the module's function onto the query's INNER
  `g`, not its outer `f`, so `structural` means *the module names terms this file
  contains*, not *the module says what this file says*.

**The gate is RED at HEAD `570b5c738`, and not from this lane**: 133 of 249
pinned instances fail because `a6ee37c6a` migrated the shipped LRA route to
`CReal` without the checker's carrier vocabulary following. Measured from a clean
snapshot. Migrating it is the reals lane's call; loosening it here is the one
outcome worse than under-covering.

Detail in [`../notes/102-attestation-gap.md`](docs/plan/notes/102-attestation-gap.md).

**`scripts/local-ci.sh` has completed once, and it was RED** (`WIP`,
local-ci-run, 2026-08-18). Hosted CI has called it "the authoritative gate for
`main`" since it existed; nothing had run it. The record is
[`artifacts/local-ci-runs/a6ee37c6a-s4.json`](artifacts/local-ci-runs/a6ee37c6a-s4.json):
**6401 s (1 h 47 m), 7511 tests, 7507 passed, 4 failed, 32 skipped.**

All four were deterministic and one cause: `b760fd6ae` (+863) and `46724faec`
(+777) added **1 640 bytes of module header** to every emitted Lean module, each
re-pinning only the golden module that sits in a gate. Third recurrence;
`6389e0194` said the same of three of these on 2026-08-15. Re-pinned at cause,
green. The point is not the pins: **no pre-merge gate runs those four
`tests/*.rs` suites**, so their only reader was the gate nobody ran.

Two defects in the gate itself, both found by running it:

- It gated the **WORKING TREE**, so a sibling lane's uncommitted work decided
  whether a SHA passed. Now gates a detached worktree at the commit, which is
  `hooks/pre-push`'s own solution (`a2841965e`).
- `count_tests` anchored nextest's summary at `^`; nextest indents it five
  spaces, so it never matched: the recorder wrote `tests: -1` for the 7511-test
  step and the zero-test rule **could not fire on the sweep it exists for**. The
  control's fixture was typed from the docs, not captured (`e069afa03`).

Cost is not core-bound: 2.47x parallelism on 16 cores, five single-test binaries
being 40% of the wall. And **nextest is 3.5x slower than `cargo test` on the
heaviest binary** (399 s vs 114 s), so the runner is likely costing real time.
Next: a timer on s5/s7 — which **measured today cannot run it** (no stable, no
1.88.0, no nextest; 342 and 422 commits behind) — read by a freshness step in
`just check`, not a dashboard.
Detail in [`../notes/102-local-ci-run.md`](docs/plan/notes/102-local-ci-run.md).

**Lean's kernel accepts all 470 declarations of the constructed-real carrier;
it is Lean's ELABORATOR that refuses four** (`WIP`, creal-lean-divergence,
2026-08-18). The handover said our kernel admits what Lean's kernel rejects. It
does not. `scripts/lean/replay-lean4export.lean` drives
`Environment.addDeclCore` from our NDJSON — Lean's kernel, from
`mkEmptyEnvironment` — and over the **whole** carrier reports `environment now
holds 470 constants` in **1.4 s**. Tampering `CReal.Equiv.not_zero_one`'s proof
makes the same binary reject it naming `Not (CReal.Equiv (CReal.ofRat Rat.zero)
(CReal.ofRat Rat.one))`, so it checked *that* declaration against *that* type.

**The mechanism, isolated to one token per line.** Lean's elaborator does not
unfold a `theorem` while reducing; its kernel does. Re-spell every `theorem` in
the *same emitted file* as `def` — nothing else changed — and the elaborator
accepts it: the `not_zero_one` module (695,655 B) in 5.0 s and the **whole
carrier** (2,541,928 B) in 27.9 s, against 4 refusals as emitted (two, plus two
`unknown constant` cascades).
`Nat.gcd`'s descent is justified by the *theorem* `Nat.mod_lt`, so `gcd 0 3` is
accepted and every recursive `gcd` refused, while `Nat.mod/div/sub` and a bare
`WellFounded.fix` reduce fine. Not the sharing pass (hand-inlined: identical
refusal), not a budget. `internal exception #3` is the command abort.

**The coverage hole is closed.** Emission was reachability-driven, so Lean saw
only the reachable slice (343 of 465 when ADR-0511's lane measured it).
`real_lean_creal_carrier_kernel_replay` exports the complete environment and
requires Lean's constant count to **equal** our kernel's, so "accepted" cannot
mean "accepted a subset"; `real_lean_wellfounded_elaborator_divergence` pins the
residue. Gate **20 suites, floor 212 -> 218**; measured `declared=470
lean_kernel_constants=470`, `checked=2`/`checked=4`. Mutations bite: dropping
one theorem record kills the carrier suite on the COUNT alone (469 vs 470, Lean
still accepting); a no-op `theorems_as_defs` kills the divergence suite on the
`def` row alone; each left the other green. The fix (`theorem` -> `def` in the
renderer) is measured and handed to the renderer's owner, not taken here.

ADR-0517. Detail in
[`../notes/103-creal-lean-divergence.md`](docs/plan/notes/103-creal-lean-divergence.md).

**`scripts/check-local-ci-freshness.sh` exists and is wired in REPORT-ONLY
mode** (`WIP`, local-ci-freshness, 2026-08-18). Continues 102-local-ci-run's
proposed-not-landed piece: a record for `scripts/local-ci.sh --record` proves
nothing by itself — it can be green for a sha nobody has built on in days, a
rebased-away branch, or a step array that disagrees with its own top-level
`verdict`. This checker re-derives pass/fail from the record's own `steps[]`
(never trusts the summary field) and requires the sha be HEAD-or-an-ancestor
and no older than 48h (chosen over a commit-count budget: velocity measured
7–10 commits/h in bursts across lanes, so a fixed commit ceiling is either too
strict in a burst or too loose on a quiet weekend; the run's own cost —
~107 min, one lock across the whole fleet — sets the 48h floor).

**Wiring is ENFORCING in both `scripts/check.sh` and `justfile`'s `check`**
(`e3e105cd6`, 2026-08-19). It was `--report-only` for one day, deliberately,
because the only record that existed was `a6ee37c6a-s4.json` with
`verdict: FAIL` — enforcing then would have red-ed the aggregate gate for every
lane over a 110-minute run nobody had re-triggered, and a gate that is red from
the day it lands is one people learn to ignore. That was the whole blocker and
it is gone: `57af69142-s4.json` is `PASS`, `rc: 0`, 6656 s, `7561 tests run:
7561 passed`, 179 doctests, no `vacuous` and no `unreadable` step.

Nine guards, each mutation-tested by deletion to kill exactly one control. The
near-miss worth keeping: the first fail/vacuous/unreadable fixtures carried a
top-level `verdict: "FAIL"`, so the separate top-verdict guard silently did the
per-step guards' work and deleting one of them killed **zero** controls. Fixed
by making those fixtures top-level `PASS` with a bad step — which both isolates
the guards and is the more dangerous case: a record falsely claiming PASS while
hiding a bad step.

The flip was re-tested through the real call site, not the control suite.

Detail moved to [`../notes/104-local-ci-freshness.md`](docs/plan/notes/104-local-ci-freshness.md).

Detail: [`../notes/104-local-ci-freshness.md`](docs/plan/notes/104-local-ci-freshness.md).

**`scripts/local-ci.sh --record` PASSED at `57af69142`, and
`check-local-ci-freshness` is now ENFORCING at both call sites** (`DONE`,
local-ci-run-2, 2026-08-19). Record: `artifacts/local-ci-runs/57af69142-s4.json`
— 5/5 steps `pass`, rc=0, 6656 s wall. Steps: fmt 4 s · stable clippy
`-D warnings` 29 s · MSRV 1.88 check 15 s · `cargo nextest --profile local
--workspace --all-features` **7561 tests run, 7561 passed** (87 slow, 32
skipped) in 6588 s · doctests **179 passed** in 20 s. Zero `FAIL [` lines in
the run log, cross-checked against the record rather than read off the exit
code. The four golden-pin failures in the first record (`a6ee37c6a`, FAIL
rc=100) were genuinely fixed by `31442bd5d`; nothing else regressed, and the
suite grew 7511 → 7561 tests in between.

**The `tests: -1` bug is confirmed fixed by measurement, not by reading the
patch**: the old record recorded `-1` for the 7511-test sweep (nextest indents
its `Summary` five spaces, the pattern was `^`-anchored), so the vacuous-step
guard could not fire on the one step it exists for. This record reads 7561.

**Flipped to enforcing** in `scripts/check.sh` and the `justfile`'s
`local-ci-freshness` recipe (plus the checker's own header, which still
described itself as report-only). Then proved the enforcing call site's exit
status depends on the finding, through `just`, not just through the control
suite: empty record dir → rc=1 `NO_RECORD`; a copy of this record with
`finished_utc` backdated 5 days → rc=1 `STALE: 120h`; the nextest step
rewritten to `vacuous` → rc=1 naming that step. All 9 controls green.

**Standing cost this imposes on every lane:** the sweep is ~110 min behind one
box-wide lock and the budget is 48h, so roughly one lane per day must run
`scripts/local-ci.sh --record` and commit the record. It needs `setsid` — a
foreground shell caps at 10 min and an ordinary background job was killed at
59 m 59.9 s with no record written (the recorder only writes at the end).

Detail: [`../notes/105-local-ci-run-2.md`](docs/plan/notes/105-local-ci-run-2.md).

**Done (`DONE`, doc-refactor, 2026-08-19).** `docs/refactor-2026-08/` corrected
against 2026-08-18/19, by amending specific claims and keeping the original
reasoning visible — no rewrites. Five files touched of 18; thirteen left alone
because dated lane diaries are records, not assertions about now.

Corrections, each re-measured here rather than taken from a brief: `04` G2 said
"Unfixed" (`check-clippy-complete.sh` is in both gates); ADR count 455 → `rows=523`;
G4–G8 added (ADR `--check` exiting 0 on duplicates, the mutation harness scoring
a non-building mutant as a kill, axiom-freedom run by no gate, `local-ci.sh`
never having run, `just check` aborting at #18 of 41 so 23 gates never ran).
`gate-divergence-2026-08-14.md`'s 112/61 → 203/278 and its completeness ordering
INVERTED — while `aggregate-scope` was red at #18 the no-`just` fallback was the
more complete gate. `00` gained the three new hygiene incident classes and a
closing open-items list; `06` gained the shared scratchpad.

**Open, and recorded as open in `00` and `04`:** `check-aggregate-scope`'s 32
unrecorded steps (fix by wiring, not re-pinning); ADR numbering's structural fix
(non-sequential allocation, unbuilt); no `axeyum-lean-kernel` suite registered
with the mutation harness (six are: five Python plus `fp-width-guard`).

**Found while writing, not in the brief:** the record
`check-local-ci-freshness.sh` enforces has five steps; `local-ci.sh` has had a
sixth (the frontier ratchet) since `69f2cffb8` the same morning. The gate reports
`PASS -- fresh, ancestor, all-pass` over a run in which that step did not exist.
Freshness of a record is not coverage by it. Owner: whoever owns `local-ci.sh`.

**Not touched, deliberately:** CLAUDE.md still says to treat `just check` as the
gate and `check.sh` as the fallback that may lag it. G8 inverted that for the
duration of the red-gate window. It is the repository's most contested file and
outside this lane's paths.

**The strand's headline claims were falsified in both directions and are now
corrected in place, not rewritten** (`WIP`, doc-formalized, 2026-08-19).

- **"Theorems the system proved without a human writing the proof: zero"** —
  false since 2026-08-18. Three facts are `kernel-term` / `checked` / empty
  footprint, and all three re-derive today (`check-autogenesis-fact-operation.py`
  exits 0 on each). Two are `Eq.refl` from a blind producer (2 of 138 rows); the
  third (`Nat.fib_add_two`) was built by a target-specific program and repaired
  by hand across two failed runs, so it fails the autogenesis programme's own
  autonomy bar. **C2 — solver refutation → library theorem — is still zero.**
- **The 149/day rate**: the counter reads **139, unchanged**, on 2026-08-19 —
  6.4/day over 5.16 days. But it counts one prelude and production moved off it
  (Int: 57 derived, axiom-free). **No tool measures this project's theorem rate.**
- **"Lean's own kernel accepted an axeyum development"** was true and narrower
  than it read — reachability-filtered, 343 of 465. ADR-0517/0518 now live in
  the strand: Lean's kernel takes all 470 carrier declarations, its elaborator
  refuses four, our kernel is **not** the permissive one, and any decline census
  must name which checker it ran.
- **C1 (shard `nat_prelude`) is DONE and did not deliver.** 845 lines in eleven
  modules, first splits 2026-08-14; five days of collision-free library produced
  +33 theorems. `N x 149/day` is falsified by its own remedy.
- Stale status blocks in `03`/`04` (13-of-40, population UNSTARTED, "import ℚ
  and ℝ", "`#print axioms` run by hand") left visible with what falsified them.

Measured, not cited: trusted surface `…/rat/string 0 · real 30`; front door
1,304,276 / 1,330,091 / 1,442,247 B, zero carrier axioms, `Real` control
non-vacuous; `check-lean-gate.sh` green at **21 suites, 66 tests, 473 checks**
(floor 219) — **40 of 77 crosscheck families are attestations**, now in `03`
because "473 modules read" is not "473 propositions proved".
Detail: [`../notes/107-doc-formalized.md`](docs/plan/notes/107-doc-formalized.md).

**The persistent pre-push checkout no longer inherits the caller lane's Git
metadata (`DONE`, codex-autogenesis-prepush, 2026-08-20).** Git exports
`GIT_DIR` and related local variables to hooks; previously, `git -C` changed
the filesystem path but still detached and rewrote the caller's HEAD/index.
`prepare-prepush-worktree.sh` clears those variables at the foreign-worktree
boundary, checks out and cleans the exact target, then fails unless its
registered HEAD and status agree. The registered control preserves a caller
with staged and untracked work across fresh and reused gate checkouts and
rejects an unsafe root and nonexistent target.

The first post-repair Rust push checked exact topic SHA `24b16642e` in the
registered gate checkout, left it clean, and preserved the caller branch,
index, and status. The operational incident is closed; future changes remain
covered by the registered control and the live hook.

**Three of the 26 uncertified string UNSATs now carry a re-derivable
certificate; the other 23 need regex/`replace`/`contains` reasoning, not
lengths** (`WIP`, string-cert, 2026-08-20).

The refreshed dominance audits
(`bench-results/dominance/qf-{s,slia,seq}-cvc5-regress-clean-dominance-audit.json`)
list 26 rows at `evidence_kind = bare-unsat`, every one decided by
`smtlib-string-front-door` with `certified=false checked=false`. A length /
code-point abstraction plus a Farkas-style linear refutation closes the three
that are arithmetic once the strings are abstracted away (`str004`, `str005`,
`str-code-unsat-2`). The remaining 23 are regex membership, `str.replace`,
`str.contains`, lexicographic order, `seq.nth` congruence, and one pigeonhole
over `str.to_code` — none of them a length argument, and none of them silently
approximated.

Next: the `str.to_code` **injectivity** lemma
(`code(y) = code(z) ∧ code(y) ≥ 0 → y = z`) would take
`r1_QF_SLIA_str-code-unsat`, whose refutation is linear right up to the final
`distinct`; its sibling `-3` additionally needs pigeonhole over seven pinned
code points and is a different argument.

**The decision route and the evidence route agreed again on
`QF_NRA/.../cli__regress0__nl__issue3003.smt2` (`DONE`, agent-route-divergence,
2026-08-20).** `check_auto_explained` said `sat` in 0.9 ms; `produce_evidence`
said `unknown certified=false checked=false`. Both run the same exact real-root
decider, so the decider was never the difference — the evidence route replays
its candidate model through the ground evaluator first (the Hard Rule), and the
replay was failing on a CORRECT model.

`poly_big::combine` reaches an operand's interval only by bisection, and
bisecting toward a *rational* root lands the midpoint exactly on it: the
interval collapses and the code declined. Every rational lifted by
`from_rational` hits that on its first refinement, so `c + α` — here
`1 + (−3/4)`, from the witness `y = −√3/2` — never computed. A collapsed
interval is more information, not less: the operand is exactly that rational, so
`α + c` is a root of `p(x − c)` and `α · c` of `p(x / c)`, isolation carried
over by bijection instead of re-derived inside a resultant's interval. Accepted
under `combine`'s own criterion (opposite endpoint signs, exact Sturm count 1),
so a decline stays a decline.

The instance now reports `sat-model certified=true checked=true`. Worth noting
for the next lane on this axis: nothing else in the tree compares the two routes
on the same query, so a divergence is only visible when someone points
`diagnose_evidence` at a file by hand.

**The three `QF_NRA` corpus rows that `nra_product_cert` explicitly declined now
carry a re-derivable certificate, including the one whose exact refutation does
not fit in `i128`** (`DONE`, agent-handelman, 2026-08-20).

`cli__regress1__nl__coeff-unsat`, `cli__regress1__nl__combine` and
`cli__regress1__nl__approx-sqrt-unsat` all shipped as bare `Evidence::Unsat(None)`
— decided, unfalsifiable. Each needs more than one product term, which is
exactly what the two-factor route was written to refuse rather than guess at.
All three now report `real-handelman-unsat certified=true checked=true`.

The producer does not implement a Positivstellensatz search from scratch: it
abstracts every monomial to a fresh real variable and hands the resulting linear
system to the exact Fourier–Motzkin/Farkas engine already in `lra.rs`, then reads
the multipliers back. The checker never runs an LP — it binds each carried atom
to something the query literally asserts and multiplies the polynomials out — so
producer and checker can disagree, which is the property a `fresh == certificate`
re-run does not have.

The interesting one is `approx-sqrt-unsat`'s third disjunct, whose constant is
`2.0000000000000000000000000001`. Its exact refutation needs `(2+k)²`, numerator
`1.6·10^57`, and `Rational` is an `i128` fraction — so no exact `i128` derivation
of that refutation exists and an approximate one is not a certificate. A
certificate atom may therefore carry a **relaxation** `r ≥ 0` and the derivation
uses `nonneg_form(atom) + r`: still implied by the atom, still something the
query licenses, and rounding the constant up to `2.000000000001` puts every
product back inside `i128` with margin. The relaxation is carried and re-derived,
never assumed; only the one disjunct that needs it has a nonzero one, and a test
pins that.

Next on this axis: the equality multiplier basis is degree ≤ 1 and products are
pairwise, which is what the committed corpus needs and no more. A shape needing a
degree-2 multiplier or a triple product will decline rather than approximate.

**`build_creal_prelude` went 8.7 s → 33.0 s across `502184d3f`, and the kernel
was missing the second of Lean's two reduction caches. Adding it takes it back
to 13.0 s** (`DONE`, agent-prelude-perf, 2026-08-20).

The bisected commit aligns the native `Bool` with official Lean order and is
correct. What nobody noticed is what that *switched on*.
`Kernel::build_nat_binop_table` admits the literal-`Nat` acceleration only in an
environment whose `Bool` has constructors `[false, true]` **in that order**
(ADR-0459). While `Bool` was `[true, false]` the table was `None` and every
probe returned immediately — the whole rule had been dead since it landed.
Aligning `Bool` turned it on, and in this workload it fires **1,192,536 times
and produces a literal 575 times** (0.05%). Every one of the 1,191,961 failures
δ-normalises *both* arguments, from inside the δ-**free** normaliser, so the work
lazy-delta exists to avoid is done eagerly and speculatively. 99.98% of the
probes are on terms that mention a free variable.

Measured by disabling the rule at HEAD: 33.6 s → 10.0 s. The regression is that
rule, not the constructor order.

The fix is a memo, not a change to any reduction rule: `Kernel::whnf_core` (the
δ-performing normaliser) had no cache at all, only its δ-free inner step did.
The pinned reference carries **both** — `type_checker.h:31-32` declares
`m_whnf_core` *and* `m_whnf` — so this is convergence on Lean, not a local
trick. The whole δ chain is memoised, not just its head, because every δ step
mints a fresh expression that no cache has ever seen.

Detail moved to [`../notes/112-prelude-perf.md`](docs/plan/notes/112-prelude-perf.md).

**`Kernel::reduce_nat_binop` now sits where Lean calls `reduce_nat` — in the δ
loop and in lazy-delta, never in the δ-free step — under Lean's `has_fvar`
guard. `build_creal_prelude` 12.99 s → 6.79 s, and nothing stopped admitting**
(`DONE`, agent-nat-rule-placement, 2026-08-20).

ADR-0459 described the placement as "tried after `whnf_core` and before δ". The
code called it from inside `whnf_no_unfolding_uncached`, and that function *is*
Lean's `whnf_core` — one layer too deep, with no `has_fvar` guard anywhere. In
the pinned reference (`v4.30.0`, `d024af09`) `reduce_nat` is called from
`type_checker::whnf` at `:670` and from `lazy_delta_reduction` at `:978`, the
second under `!has_fvar(t_n) && !has_fvar(s_n)`. Both are now ported; the
`whnf_core` site also carries the guard, which is stricter than Lean and is the
decision ADR-0536 records.

Detail moved to [`../notes/113-nat-rule-placement.md`](docs/plan/notes/113-nat-rule-placement.md).

**All 35 dominance audits re-run at `496288979`; the fully-dominant UNSAT count
is 269 / 326, not 262 / 324, and five of the fifteen "Lean-reconstruction gap"
rows were stale records rather than gaps** (`DONE`, agent-audit-refresh,
2026-08-21).

Every committed audit was stamped between `2e207eba5` and `562b65f13` — all of
them before today's reconstruction work landed — so the artifact said "gap"
about instances the code had already closed. Four rows moved and 31 are
identical in every summary field, which is what makes the two runs comparable.

**+5 of the +7 dominant outcomes are capability; +2 are the instrument.**

- Capability, QF_NRA `qf-nra-cvc5-regress-clean` 21/32 → 24/32:
  `coeff-unsat-base` and `simple-mono` reconstruct as `RealProduct`
  (`71f1c29a0`), `ones` as `MonomialBound` (`77c70d3e0`).
- Capability, QF_S `qf-s-cvc5-regress-clean` 9/93 → 11/93: `r0_QF_SLIA_str004`
  and `r0_QF_S_str005` gained a kernel-checked `StringLength` module
  (`b495a396e`).
- Instrument, QF_NRA `qf-nra-synthetic-graduated` 31 → 33 audited: the two
  `d01` instances were being billed for a process-wide ~32 s `CReal` prelude
  build inside a 10 s per-instance cap. `562b65f13` moved that build outside the
  timer. A/B, corpus and cap fixed: `1fff66825` 31, `cfc5f8078` 31,
  `71f1c29a0` 33, `71f1c29a0` with the warm suppressed **31**, HEAD 33, HEAD
  with the warm suppressed **33** — the last row because `0887ab652` made the
  prelude cheap enough to pay for inside the cap. This is the whole baseline
  denominator movement, 324 → 326.

Detail moved to [`../notes/114-audit-refresh.md`](docs/plan/notes/114-audit-refresh.md).

**`QF_FP/solver__fp__fp_misc.smt2` timed out because `array_bv_abs::abstract_term`
walks a DAG as a tree; memoized, the row goes from 124.7 s of a 125 s budget to
314 ms. It is now certified and independently checked and it is still not
dominant, and that second half is correct rather than unfinished** (`DONE`,
agent-fp-misc-hang, 2026-08-21).

**The null was the finding.** `audit_dominance` fills `timeout_phase_detail`
from `scan_proof_fragment` *before* reconstruction starts, so `fp_misc`'s
`detail: null` meant classification itself never returned — while three sibling
rows in the same run did name their fragment, which is the positive control that
the mechanism worked. Eight of eight `gdb` samples, 100% of the axeyum frames,
were in `abstract_term`, self-recursive dozens of frames deep. `perf` and a bare
`gdb -p` are both blocked on this host (`perf_event_paranoid=4`,
`ptrace_scope=1`); an unprivileged sampling loop returns an empty file that reads
exactly like "nothing to see". `sudo gdb -p` works.

Detail moved to [`../notes/115-fp-misc-hang.md`](docs/plan/notes/115-fp-misc-hang.md).

**Gap #7 closed for `:pattern`, declined for `:weight` (`DONE`,
agent-quantifier-triggers, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 7. `:pattern`
was parsed and dropped; it is now threaded parse → IR → the E-matching loop and
a usable annotation **replaces** auto-selection ([ADR-0537](docs/research/09-decisions/adr-0537-user-triggers-are-a-hint-channel-on-the-arena-and-replace-auto-selection.md)).
Alternatives are unioned, multi-patterns joined, and everything the matcher
cannot fire is declined whole and falls back to auto-selection.

The measurement that motivated it, z3 4.13.3 with its own fallbacks off
(`smt.mbqi=false smt.auto_config=false`): `unsat` unannotated, `unknown` with
`:pattern ((h x))`. Axeyum answered `unsat` for both, in both configurations.

Two findings worth carrying forward rather than re-deriving:

- **The corpus cannot measure this.** 0 of 1430 tracked `.smt2` files contain
  `:pattern` and 0 contain `:weight` (positive control, same command: `assert`
  1419, `forall` 82). The capability delta is zero by construction, and any
  claim about this feature's value has to say so.
- **A verdict is a blunt instrument for "was the trigger obeyed".** Honouring a
  useless trigger did *not* cost the refutation through the front door: term
  invention seeds ground instances of the trigger itself and reaches the witness
  anyway, where z3 with mbqi off has no analogue. The tests measure the proposed
  *instance set* instead.

Next, if this is picked up again: `:weight` needs a corpus that moves under it
before the flood-control cost function is touched (ADR-0537 §5); and the parser
declines any trigger outside an application tree over declared uninterpreted
functions, which rules out arithmetic subterms — the first real workload with
`(f (+ x 1))` as a pattern will want that.

**The parity ledger has a gate, it is ENFORCING in both aggregate gate sets, and
the board behind it has been re-measured** (`WIP`, agent-parity-gate,
2026-08-21). `bench-results/PARITY.md` is the declared headline — external list
pinned by sha256 before each run, `DISAGREEMENTS > 0` voids an entry — and
`scripts/parity-run.sh`, the only thing that writes it, was invoked by **no
gate**: not `just check`, not `scripts/check.sh`, not CI. So the board froze on
2026-08-06 for fifteen days, through UF 32 → 85 and QF_RDL 10 → 105, and nothing
went red.

`scripts/check-parity-freshness.py` derives a per-logic as-of date from each
entry's own header and fails past **14 days** (warn at 10). 14 is not a round
number: any budget ≥ 15 days would have sat green through the whole episode the
gate exists for, and below it the binding constraint is cost — the ledger's own
2026-08-06 sequence puts a division at 68–170 minutes. The budget is **per
logic**, so a red costs one sweep, not a board refresh. The population comes
from the append-only ledger, never from `bench-results/parity-lists/`: a list
can be deleted, so anchoring there would let a logic be dropped from the tracked
set to go green.

Detail and older landed rows moved to [`../notes/117-parity-freshness.md`](docs/plan/notes/117-parity-freshness.md).

**The data coupling to `../math-education` is removed and
`scripts/check-external-coupling.py` refuses its return** (`WIP`,
agent-decouple-math-education, 2026-08-24). The owner's constraint is that the
sibling is REFERENCE ONLY — read it for calibration, never depend on it,
integrate with it, or point at it in data. It was stated and never gated, and by
today it had been violated in **five places at once**, with every validator
involved exiting 0:

- the knowledge overlay (an `external-repository` source, an `external-pinned`
  namespace, **24 of 33 links** pinned to that repo's SHA);
- the family-concept crosswalk (`path_hint: ../math-education/graph/concepts`,
  and a validator that hardcoded the SHA and *required* the file to match);
- `tactic-catalog.schema.json`, where `uses_technique` is required on every
  tactic and required `source: {const: "math-education"}` plus a `revision` —
  so no tactic could be declared here without naming that checkout;
- **all 104 claims**, each carrying `provenance.graph_pin` and 438
  `resolved: true` refs, with the schema making `concept_refs` mandatory and
  `graph` a one-value enum;
- `python/axeyum/knowledge/math_education.py`, 777 lines that resolved
  `Path("..") / "math-education"`, ran `git rev-parse HEAD` against it, and put
  the resulting `file://` prefix **into the agent's fetch allowlist**.

Four validators reached outside the checkout in code, one of them defaulting to
`~/projects/personal/math-education/graph` — an absolute path into one machine's
home directory, in a tracked file.

Detail moved to [`../notes/118-external-coupling.md`](docs/plan/notes/118-external-coupling.md).

**Gap #4 diagnosed; "multi-year catch-up" confirmed for the search, and the
sizing corrected three ways (`DONE`, agent-nia-diagnosis, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 4 →
[nia-deficit-diagnosis](docs/research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md).
Measured at `cb4a391c9` over the pinned 200-file list (sha256 `19b334d3b910`,
the hash in the `PARITY.md` entry), three solvers per file at 24 s.

The framing survives: the three cheapest levers in the division yield **0**,
**+1** and **+3** files, and 4× the wall clock buys **0 of 20** search timeouts.
Ranking QF_NIA last among decision work is right. Three premises around it do
not survive:

- **cvc5 1.3.4 is on this host** at `/nas3/data/axeyum/harness/bin/cvc5` — not on
  `$PATH`, which is why two documents record it as absent. It was reachable the
  whole time.
- **z3 is not a stand-in for cvc5 outside the linear divisions.** Same run:
  z3 **136/200**, cvc5 **76/200**, and cvc5's decided set is a strict *subset* of
  z3's. Row 1's "within 5 files" check is true where it was made and does not
  transfer. So "38.2 % of the reference" means plain cvc5; against z3, 27.9 %.
- **The deficit is one benchmark family.** `20170427-VeryMax/ITS` is 134 of the
  200 files and **74 of the 104 misses**. Excluding it: 29/39 = **74.4 % of
  cvc5**, around QF_RDL. On `20220315-MathProblems` we decide **6 of 9 and both
  references decide 0**.

Mechanism, and it rhymes with row 1's §3.2: every specialised nonlinear-integer
route declines, so `int-blast-ladder` — a *generic* bounded integer bit-blast —
is decisive on **158 of 161** undecided files. Its width ladder admits a rung
only if every integer **literal** fits, so a `2^30` Farkas coefficient kills 14
of 15 rungs. **32 files have one live rung and we decide zero of them.**

Two findings worth not re-deriving:

Detail moved to [`../notes/118-nia-diagnosis.md`](docs/plan/notes/118-nia-diagnosis.md).

**Gap #3 of the 2026-08-21 capability audit is closed at the command level**
(`WIP`, agent-consumer-interface, 2026-08-21). §6.3 ranked the consumer
interface third by measured cost and called it "the difference between a library
and a solver a stranger can run". Four of its six items were one defect wearing
four hats: **the front door accepted a command and did not answer it.**
`get-model`, `get-value`, `get-unsat-core` and `get-proof` were CLI no-ops with
Rust-API-only counterparts; `set-option` was inert; `set-logic` was stored and
never read.

The half landed earlier — `examples/axeyum_cli.rs`, one verdict per `check-sat` —
made the rest sharper rather than softer. A driver that answers `check-sat` and
drops `(get-model)` produces **no output and no complaint**, and that is
indistinguishable from a solver with no model. It is this repository's own
recurring failure: silence read as a negative result.

Detail moved to [`../notes/119-consumer-interface.md`](docs/plan/notes/119-consumer-interface.md).

**Gap #6, second and third turns: three more families converted, and the row's
own denominator corrected (`WIP`, agent-checker-independence, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 6 / §6.2.

`nra-even-power` (10 certified `unsat`), `finite-array-extensionality` (4) and
`finite-domain-pigeonhole` (3) no longer rest on
`producer(arena, assertions).is_some_and(|fresh| fresh == *cert)`. Each is now
decided from the certificate and the query, with **no fall-through** to the
re-run — the lesson from the array-axiom turn, where the same guards placed in
front of the equality comparison killed nothing because the comparison subsumed
them. Eleven guards, eleven adversarial fixtures over **satisfiable** queries,
each deletion killing exactly one test.

**The row's headline number is wrong in our favour, and that is the more useful
finding.** "~30 of 34 checkers re-run the producer" counts one shape and three
situations. All 28 remaining were read:

Detail moved to [`../notes/120-checker-independence.md`](docs/plan/notes/120-checker-independence.md).

**Gap #5: the rule vocabulary was fixed and it was never the binding constraint
(`WIP`, agent-portable-evidence, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 5 / §6.2.

**Carcara was built here for the first time.** No host in this repository had a
Carcara binary — not in `references/`, not on `$PATH`, not on any fleet host —
so every test in `tests/carcara_crosscheck.rs` had been passing by returning
early for as long as the file has existed. `references/carcara` now carries a
built `target/release/carcara` (Carcara 1.1.0, `6624ea80`). Building it needs
`m4`, which is not installed on this box but ships inside a snap
(`/snap/gnome-46-2404/153/usr/bin/m4`); no host package was installed.

**The central claim of the array-proof design note is false.**
`docs/research/07-verification/array-elimination-alethe-proofs.md` records
"Alethe/Carcara has NO array theory rules", quoted from there into six doc
comments, into `check_alethe`'s dispatch, and into the design of two emitters.
Carcara 1.1.0 registers `arrays_idx`, `arrays_row`, `arrays_row_contra` and
`arrays_ext`, and `arrays_idx` **is** axeyum's `read_over_write_same`, shape for
shape. Same problem, same proof, one identifier changed:
`read_over_write_same` → `unknown rule` / `invalid`; `arrays_idx` → `valid`.

Detail moved to [`../notes/121-portable-evidence.md`](docs/plan/notes/121-portable-evidence.md).

**The GF(2) machinery is on `main`; the Kaser--Lemire attack is not** (`landed`,
lemire-integration, 2026-08-23, ADR-0544, `b99d715bc`). Two lanes had produced
~1.3 M lines across four artifacts, and neither was mergeable whole: `main` was
57 commits ahead and **694 behind** origin, and `agent/gf2/lemire-proof` carried
the entire attack alongside the machinery.

Three things this cost, worth carrying forward:

**Sixty ADR numbers were double-allocated and `git merge-tree` reported no
conflict on any of them.** The branch allocated `adr-0484`--`0592` while
`origin/main` independently allocated `0484`--`0543`; the *filenames* differ, so
both sets merge clean and land side by side under one numbering. The generated
index would then render two different decisions as one sequence. A clean
`merge-tree` is evidence about content, not about a shared namespace — and this
repository has two such namespaces (ADR numbers, fact ids) that no merge check
covers.

**A module's size is not evidence that it is load-bearing.** `gf2_hayes.rs` is
26,655 lines and 266 public items, the largest module in `axeyum-cas`, and it is
a leaf: it imports nothing from the rest of the crate, and the only inbound
references from the keep-set were six in `gf2_extension.rs`, every one a doc
comment or `#[cfg(test)]`. The extraction that looked infeasible was four test
assertions.

**Grepping the module path missed a coupling that only failed at link time.**
`tests/gf2_artifact_cli.rs` reports clean for `gf2_hayes` and still reaches it,
through `env!("CARGO_BIN_EXE_axeyum-gf2-hayes-conditional-variance")`. When
cutting a module out of a crate the coverage surface is module paths **and**
`CARGO_BIN_EXE_*` names **and** `Cargo.toml` target declarations; a clean grep
over the first says nothing about the other two.

Which facts stayed was decided mechanically rather than editorially: a fact stays
iff every `evidence.artifact` it cites resolves under a retained path and no
checker command reaches `gf2_hayes` or `artifacts/gf2`. Exactly four of 45
qualify, `depends_on`-closed. The other 41 would have left the ledger asserting
evidence this repository can no longer produce.

Detail moved to [`../notes/122-lemire-integration.md`](docs/plan/notes/122-lemire-integration.md).

**Theorem correspondences (`WIP`, agent-correspondence-model, 2026-08-24).** The
data model can now state that two settled facts are the same mathematical
content, and cannot state it where `depends_on` belongs
([ADR-0546](docs/research/09-decisions/adr-0546-theorem-correspondences-are-not-proof-dependencies.md)).
`artifacts/correspondences/*.json`, one file per adjudication on the
`artifacts/facts/` pattern, gated by `scripts/validate-correspondences.py`
(`just correspondences`; 39 mutations, 39 killed, one test each). Three
instances landed, all `route-recorded`.

Detail moved to [`../notes/123-theorem-correspondences.md`](docs/plan/notes/123-theorem-correspondences.md).

**Curriculum-directed kernel development (`WIP`, coordinator, 2026-08-25).**
**1,106 distinct theorems, every one axiom-free**; trusted base unmoved at 30
declared-and-unreached `axreal` assumptions, and no `Opaque` or `Quotient`
declaration exists anywhere, so `Axiom`-only and the trusted surface coincide. Fact ledger **362 → 587**, `missing_edges=0`.

**The loop is code-complete.** Frontier selects → operation re-derives → receipt
survives a re-signed cross-target forgery → transaction verifies. Reproduced
end to end; the fact stays `open` on purpose, because whether to WRITE is not a
decision a gate should make.

**Why it is not yet automatic has a measured answer, not a direction.** Three
producers cover 7, 4 and 1 facts; the third is single-target **by
construction** (`const TARGET`, `const STREAM_SHA256`). Both routes past the
wall were tested: premise composition dies on WHNF opacity — reconfirmed
through a code path that never touches the induction producer — and on a
`fibAux`-vs-`Nat.iterate` representation mismatch; iterate re-derivation dies
because `LE.le` desugars to a four-argument spine and is rejected before any
combinator runs. The next capability is named: an order-relation combinator
vocabulary. Full chain in doc 262's fourth, fifth and sixth amendments.

**Next.** (1) That vocabulary, narrowly scoped — the previously-reverted broad
version exhausted a shared budget for zero admits. (2) Coverage is 210+/1134;
`Complex` and `CPoint` are thinnest. (3) `sumRange_cauchy_of_dominated` is three
named steps from closing.

**Three findings outrank the counts.** The binding constraint on the mathematics
is a **missing type** — no `List`, no `Finset`, no product — found every time by
a lane trying to prove something, never by planning. **Three targets I named
were false or unsatisfiable**, and lanes refuted them with counterexamples
rather than failing to prove them. And **reading a producer gave a plausible,
partly wrong picture three times running**; every correction came from running
it.

**A day of parallel mathematical development against the kernel, 3–5 lanes
throughout** (`DONE`, flywheel-mathematics, 2026-08-25). Production moved
**1,096 → 1,175 distinct theorems, all axiom-free, 0 axiom-bearing**; the
trusted base did not move (30, all `axreal`, none reached by any shipped route).
Kernel `--lib` sweep 656 → 695 green. Full write-up:
[`../../mathematics-2026-08/diary-flywheel-2026-08-25.md`](docs/mathematics-2026-08/diary-flywheel-2026-08-25.md).

The theorems are the smaller half of the output. **Three structural findings
came from lanes failing to prove things and reporting why**, and none of them
was visible from any plan:

1. **`CReal.sqrt` blocks three unrelated results.** The unsquared triangle
   inequality (why `CPoint.distSq_triangle_sq_bound` is stated squared), the
   metric form of Ptolemy, and `CPoint.incentre` — which needs side *lengths*,
   not their squares. Three lanes on different targets converged on one missing
   definition. Step A of its regularity proof landed, and the constant `c = 3`
   survived a genuine refutation attempt (exact rational arithmetic at
   `dm = dn`, `dm = 1`, `dm ≫ dn`, `dn ≫ dm`; margin `4/(dm·dn) + 1/dn²`,
   strictly positive throughout).

2. **The predicate-scoped fold, recorded WRONGLY TWICE before it was right.**
   Seven lanes reported "no product over a predicate-defined subset". I then
   recorded that it existed one carrier away (`Int.prodRange_permute`) and
   redirected a lane — **matching on a name without reading its hypotheses**,
   the same failure that produced four duplicate lanes the same day. It is
   `MapsInto σ n`: a self-map of the *whole* range. Wilson's theorem does not
   need the scoped version because its modulus is **prime**, so every residue is
   a unit and the subset *is* the contiguous range. Euler's modulus is
   composite. Both corrections are kept in
   [`../../mathematics-2026-08/diary-predicate-subset-product.md`](docs/mathematics-2026-08/diary-predicate-subset-product.md)
   rather than edited away.

3. **The blind-evaluation held-out partition was being spent by ordinary library
   work.** 5 of 57 nursery propositions were already proved in the kernel by hand
   development unrelated to autogenesis. `check-autogenesis-holdout-isolation.py`
   could not see any of them: it reads `epistemic_status` and scans for textual
   references, and reported `held_out=57|settled=0|verdict=PASS` throughout. Not
   the vacuous-checker shape — it discriminates correctly on its own predicate;
   the predicate was the wrong one. Repaired per ADR-0542 by an amendment moving
   `natural-binomial` to `development` as a whole family (held-out re-froze at
   **37**), and `scripts/check-autogenesis-holdout-contamination.py` now reports
   contamination without failing the build — failing it would only pressure a
   lane into not proving a theorem it needs.

**The mechanism worth keeping**: every brief said to report precisely what
blocked the lane, and treated a refutation as a complete result. Four targets
this coordinator named were refuted or redirected by lanes doing exactly that,
including one that corrected a design note and redirected a whole line of work.
A wrong brief with an escape hatch is recoverable; one that demands success is
not.

**Turn the architecture review into executable product increments** (`WIP`,
top-three-focus, 2026-08-25). The durable plan is
[`../../top-three-focus-plan-2026-08.md`](docs/top-three-focus-plan-2026-08.md);
the full lane history is in
[`../notes/126-top-three-focus.md`](docs/plan/notes/126-top-three-focus.md).

Current boundary: reusable ModEq production reached 11 facts. Exact retrieval
then composed `Nat.fib_le_succ` through `Nat.monotone_of_le_succ` into checked
`Nat.fib_mono`, but remains honestly `no_operation` because its constructor was
hand-authored. The graph links 395 theorems to 390 facts (four identities remain
explicitly unresolved) and exposes every canonical kernel type through typed
agent queries. A bounded application producer now reconstructs the Fibonacci
composition from three retrieved declarations and declines when the adjacent
lemma is absent. Its typed Python surface now preserves the explicit retrieval
boundary, fixed search telemetry, and typed declines. Next: dispatch it through
an authoritative operation and clean episode, then measure sibling conversion.
The prerequisite candidate-capsule importer now keeps the target proof absent
while independently admitting only the exact axiom-free candidate closures;
the ordinary proof-isolated importer remains unchanged.
The kernel projection now publishes both all-kind **direct** dependencies and
proof-isolated direct **type** dependencies, additively beside theorem-only
proof edges. The distinction was found before dispatch: a theorem's all-kind
row observes its finished proof and cannot authorize premise selection. The
type row gives bounded search statement vocabulary without proof leakage or a
transitive flood; for Fibonacci it includes `Nat.fib` but excludes both
`Nat.fibAux` and the two lemmas used by the checked proof. Next: combine that
type-only vocabulary with independently retrieved fact dependencies, measure
the sibling family, then register only the supported operation. The first
proof-isolated census now measures 6/109 accepted (5.5%), all kernel-admitted
and axiom-free, with 103 typed `NoTypedApplication` declines. This is a
capability measurement over settled controls, not autonomous yield.
Three proof-isolated native capsules now reproduce the accepted arithmetic
controls (`Nat.fib_mono`, `Nat.mul_one`, `Nat.one_mul`) from explicit
candidates. Git retains only hash-bound receipts; the 17–35 KiB NDJSON packs
live under `/data0/axeyum/autogenesis/reference-packs/`, are read-only, omit
the target theorem, and fresh-import to the same axiom-free proofs. Next:
register the unchanged three-target operation and dispatch one eligible target
through the authoritative receipt/transaction path; do not count these settled
controls again.
The agent's single producer boundary now resolves these receipts by exact
fact-to-kernel identity, re-hashes and size-checks the external capsule, imports
only its explicit candidates, and runs bounded application. It does not yet
expose this route as a tier-C tool: operation registration and transaction
authority remain deliberately separate.
The corrected 57-target train/development open/conjectured arrow-free sweep
measures the honest next boundary: the unchanged 13-declaration palette accepts
0, 30 targets reach search and type-decline, and 27 fail closed during import because their target
type closure reaches an unallowlisted trusted declaration. The hashed census is
measurement only. Do not register the settled three-control family as new
production. Next: route rich statements through the existing checked type-slice
boundary, then add dependency-ranked premise retrieval and rerun this exact
population. The 27 import rejections must use the already implemented ADR-0484
type-slice/generalization and exact-specialization route; do not create a second
trusted-support allowlist in the candidate importer.
The first exploratory run improperly included 23 held-out rows. It found no
proof and read no source proof body, but the attempt itself spent evaluation
information. The v2 census excludes them before capsule access, records their
identities, and fails closed on facts absent from the nursery. Do not use the
superseded 80-row counts.
A held-out-safe candidate-ranking projection now covers 142 open/conjectured
Lean goals in train/development with 1,704 proof-isolated kernel-lemma rows; all
37 held-out IDs are excluded before statement tokenization. The deterministic
lexical/type/graph score is retrieval context only. Its broad ties demonstrate
the next need: exact type compatibility and bounded application over ranked
candidates, with no fuzzy match receiving fact or operation authority.
The import boundary now also exposes checked cross-kernel compatibility for two
closed proposition expressions. It translates by exact declaration identity,
re-infers in a private target clone, and requires target-kernel definitional
equality; unlike declaration-type reuse it therefore cannot mistake two
proof-free `definition : Prop := ...` goals as equal merely because both outer
types are `Prop`. This is diagnostic candidate filtering only: it reads no
proof, mutates neither kernel, and grants no fact or admission authority. Next:
measure ranked native candidates against train/development imported goals and
publish the match and decline distribution before registering any operation.
A reusable proof-free audit now applies that relation to one imported target
and any number of independently rebuilt Nat/Int theorem candidates. The first
complete terminal census over the 57 mapped train/development goals checked 684
ranked pairs and found six exact equivalents (five `Nat.choose` statements and
`Nat.one_le_factorial`), with 678 typed declines and zero row failures. This
terminal result is not yet durable evidence: next generate and gate a
hash-bound census artifact, then reconcile those six graph identities without
claiming autonomous theorem production.
That census is now durable and freshness-checkable as
`open-ranked-proposition-census-v1.json`: 57 goals, 684 pairs, six compatible,
678 declined, zero audit errors, zero held-out access. Each row binds its
external capsule size/hash, while the artifact binds both source censuses. Its
recipe is intentionally not in the fleet-wide knowledge freshness aggregate
because reproduction requires the external reference-pack mount. Next:
reconcile the six exact identities as aliases/correspondences, preserving their
non-autonomous provenance and leaving the remaining 51 goals open.
The knowledge overlay now represents those six observations with an additive
`definitionally-matches` relation from fact to kernel declaration. The relation
is independently checked but explicitly non-authoritative: all six fact
statuses remain unchanged. A durable review explains why these cannot yet be
theorem correspondences (that schema correctly requires two settled fact
endpoints) and sequences two missing native fact records, a reviewed
reconciliation transaction, coordinated regeneration, and a remaining-target
rerun. Next: add the two missing native fact records from kernel evidence, then
specify and test the non-autonomous reconciliation transaction before changing
any imported fact status.
Two previously unlinked native theorem declarations now have first-class fact
records derived from exact kernel types, direct dependencies, and theorem-level
empty footprints: `Nat.choose_succ_self_eq_zero` and
`Nat.zero_choose_succ`. The ledger reaches 698 facts / 504 proved while open
remains 185; exact graph linkage reaches 397 theorems / 392 facts. All derived
views were regenerated against the merged 1,253-theorem kernel, and the ranked
57-goal census still finds exactly the same six matches. This is metadata and
connective-tissue repair, not autonomous yield. Next: specify the reviewed
reconciliation transaction and its negative controls before settling any of
the six imported statement records.
A prepared proposition-reconciliation transaction now requires an open,
evidence-free source fact; a proved axiom-free native kernel fact; evidence
binding that native fact to the exact matched declaration; and the exact
independently checked overlay link with its false admission-authority
qualifier. Mutations of every boundary fail closed. Each proposal carries
`no_operation`, `autonomous: false`, and no admission event. All six source
facts remain open. Next: materialize the six proposals against live hashes,
version the pre-reconciliation evaluation artifacts, then apply and regenerate
as one coordinated non-autonomous metadata transition.
Six live, hash-bound reconciliation proposals now materialize from the exact
census, lemma index, overlay links, and fact files. They name unique native
fact endpoints and proposed after-facts while reporting zero ledger writes,
zero operations, and zero autonomous credit. Two historical native evidence
rows gained the additive `kernel_declaration` identity required to remove the
last legacy-ID inference. No source fact changed status. Next: add a crash-safe
checked apply path for this proposal kind, preserve the current 57-goal census
as the pre-reconciliation version, then apply all six and regenerate the
remaining-target v2 population.
The crash-safe fact applier now rebuilds this proposal kind from the live
census, overlay, native fact, and open fact before compare-and-swap. Durable
events are `fact-reconciled`, not `fact-admitted`, and embed the same
operation-free, non-autonomous classification. Recovery after intent, fact
replacement, and event publication is deterministic; all six live proposals
reconstruct byte-for-byte. No fact status changed in this increment. Next:
preserve v1 as the explicit pre-reconciliation baseline, then execute the six
checked transitions and publish a v2 remaining-target census.
The original 1,704-row candidate ranking is now preserved under an explicit
pre-reconciliation path, and the 57-goal census pins that path and SHA rather
than the mutable current ranking. Its six proposals were regenerated against
the versioned census. This removes the artifact-lifecycle blocker: later
status-driven ranking refreshes cannot rewrite or invalidate the experiment
that justified reconciliation. Next: execute the six exact crash-safe
transitions, regenerate current views, and publish the 51-goal remaining-target
result separately.
All six crash-safe reconciliations are now committed and checked as one
coordinated transition. The ledger moves from 185 open / 504 proved to 179 open
/ 510 proved; exact linkage reaches 397 theorems / 398 facts. The current
ranking shrinks from 142 goals / 1,704 pairs to 136 / 1,632, while the mapped
open-population comparison moves exactly from 57 goals / six matches to 51 /
zero matches. Durable events, live after-facts, v1 matches, and v2 exclusions
agree exactly; operation and autonomous credit remain zero. Next: point
bounded application at the now-clean 51-goal population and measure whether
semantic/type-directed retrieval improves the honest 0/51 construction rate.
After rebasing over concurrent CReal, Nat, Complex, and Rat construction,
mutable views were regenerated again at 1,629 declarations / 1,275 theorems /
7,458 edges. The full 753-test kernel suite passes. These additions are
credible manual library construction, not autonomous-production credit; the
semantic-review queue still has all 1,275 indexed theorems unreviewed. The
historical authorization artifacts remain pinned to their archived
pre-transition index, while the post-transition 51-goal census absorbs the new
kernel state and remains zero exact matches.
The 51-goal v2 result now also pins an immutable post-reconciliation ranking.
This separates completed evaluation artifacts from the live theorem dashboard:
concurrent theorem construction can advance current projections without making
either the 57-goal v1 or 51-goal v2 experiment stale.
The fixed-palette producer now runs directly against that committed 51-goal
population through a backward-compatible population input. The direct result
is 0 accepted, 24 `NoTypedApplication` declines, 27 statement-import
rejections, and zero held-out access. Future changes must report the import and
search denominators separately; retrieval work cannot affect the 27 rejected
closures, and import work alone cannot affect the 24 grammar declines.
The must-decline gate exposed and now independently refutes a tenth visible
mutation (`Nat.choose_self = 0` at `n = 0`). The clean census therefore contains
45 positive targets and six false controls: 20/4 in the importable population
and 25/2 in the import-rejected population. Control acceptance is a soundness
failure, never production credit.
Surface-operator normalization now contributes arithmetic, modular, order, and
divisibility vocabulary to live retrieval; for the two Nat additive ModEq
goals, `Nat.mod_eq_add_left` and `Nat.mod_eq_add_right` move into slots 1-2.
The first ranked-application census then fails closed before search on all 51
rows: 48 selected declarations are absent from the imported goal capsules and
three candidate closures reach a trusted declaration. Next work is a general
proof-isolated native-candidate materialization/transport boundary, not a
larger application grammar pretending graph names are executable lemmas.
That boundary now exists for one exact source theorem at a time. It validates
same-name target reuse or independently composes a missing source closure, and
in both cases requires an axiom-free theorem before publishing the private
target clone. The real `Nat.add_modEq_left` probe makes 8/12 ranked candidates
executable (five added, three reused, four typed transport declines), then
honestly reaches `NoTypedApplication`. Next: expose this primitive through the
typed Python producer surface and rerun the 51-goal census with transport and
proof-search outcomes reported separately.
The typed Python surface and full rerun now do that. Across the 24 importable
goals, 288 ranked candidate attempts yield 158 newly composed theorems, 52
already-present candidates, and 78 typed `AdmissionRejected` transport
declines. Bounded application receives the resulting 210 executable premise
handles but still returns `NoTypedApplication` on all 24 goals; all four
importable false controls remain rejected. Transport is no longer the dominant
zero-conversion explanation. Next: extend the bounded application grammar
against this immutable population, while tracking the 78 composition failures
as a separate compatibility defect.
The producer no longer erases retrieval priority by alphabetically sorting its
input before spending the 128-term budget; it preserves caller ranking and
deduplicates stably. The complete 51-goal artifact reproduces byte-for-byte
with 0/24 conversion and identical telemetry. Candidate ordering was a latent
policy defect, not this population's active limiter; do not spend the next
increment tuning that budget.
The accepted ADR-0541 general SMT-LIB session driver is now also a named
`axeyum` binary target, not only a discoverability-poor Cargo example. The same
source remains the historical example control, and the binary's focused check,
Clippy, file execution, format, link, and exact-SHA pre-push gates pass. It is a
repository-built front door, not yet a published crate or prebuilt release.
Retrieved equality rewriting now extends bounded induction through an additive
Rust/Python API with explicit caller-owned declarations, fair per-declaration
typed specialization, closed-numeral normalization, deterministic forward
chains, fixed budgets, and no retrieved-premise residual recursion. A
second-hop knowledge projection derives connective lemmas from operator
vocabulary introduced by the first-stage topical ranking. The immutable
51-goal census converts `Nat.choose n 1 = n`: one induction, empty axiom
footprint, and checked dependencies on four retrieved theorems. All six false
controls remain unaccepted. The honest denominator is 1/20 importable positive
targets (1/51 overall); 27 rows remain import-blocked and 15 imported rows end
outside the equality grammar. A digest-bound obstruction projection now turns
all 51 outcomes into typed capability demand while excluding the six controls
from scheduling. Among 45 positives: 25 need type-slice generalization, 13 need
non-equality grammar, five need a missing rewrite/induction plan, one exceeds
the binder budget, and one is integration-ready. Do not register a one-target
operation: route the largest blocked population through the existing general
type-slice boundary and require one unchanged contract to convert at least
three siblings before it receives operation authority.
That statement-boundary route now accepts all 25 positive targets with checked
fresh-kernel receipts and exact specialization; no proof producer ran. The
slices expose 14 distinct abstracted source definitions, so the honest next
blocker is semantic contracts for recurrence, bit operations, order, and
concrete functions—not statement import and not a larger blind search budget.
Next: derive an exact contract-demand graph, join existing checked behavior
lemmas/receipts, and choose the largest reusable sibling family.
That graph now joins all 14 exact source identities to the live kernel index and
durable contract-receipt population. No checked contract receipt exists. Only
`Nat.testBit` (four targets, five candidates) and `Int.gcd` (one target, six
candidates) have exact axiom-free theorem edges. `Nat.testBit` is therefore the
first general contract prototype; twelve unmatched identities stay visible
rather than receiving fuzzy or manually asserted support.
Joint requirements show zero of the 25 targets fully contract-supported:
every `Nat.testBit` sibling has an unsupported co-abstraction. The shorter
reachable path is now measured separately. Transparent terminal reduction
moves all ten imported ModEq positives into equality composition while all six
controls remain unaccepted; conversion is still 0/13 because the producer does
not yet have the needed remainder-equality contracts. A representation audit
shows the native existential `Nat.modEq` chain is not the imported Mathlib
`Nat.ModEq`, which unfolds to equality of remainders. Next: construct
`Nat.mod_self` and reusable modulo-add equalities, retaining native relation
composition only as a boundary control, and require unchanged conversion of at
least three imported siblings.
Native `Nat.mod_self` is now axiom-free and ranks first by a generic
alpha-stable statement-shape feature, but a fresh transport probe refuses its
implementation-bound `div_mod_exec` dependency over Mathlib's different
`Nat.mod`. Production remains zero. Next: reconstruct the equality inside the
imported kernel from portable order/decision facts, then test unchanged reuse
across the additive siblings.
The imported representation boundary is now a generated knowledge artifact,
not a prose inference. All 14 exact definitions abstracted by the 25 checked
type slices expand to 1,363 transparent-definition occurrences and 7,303
direct dependency edges (1,000 context-bound transparent nodes / 1,734 total
declaration nodes / 5,421 identity-bound edges), with same-named variants and
nontransparent trust boundaries retained.
The checked `Nat.mod` spine explicitly reaches `Nat.decLe`/`Nat.ble`,
`Nat.modCore`, recursive `Nat.modCore.go`, and subtraction-instance machinery.
No theorem proof or held-out target is read and the graph grants no contract or
transport authority. Next: derive a deduplicated reverse-reachability view,
then use the shared `Nat.testBit` subgraph and the modulus spine to choose the
smallest multi-sibling contracts rather than writing another target-local
proof.
The derived reverse-reachability frontier now replays every root closure and
ranks 113 near-root `Nat`/`Int`/`List` identities without granting proof
authority. The four bit-observation siblings share a concrete implementation
spine including `Nat.land`, `Nat.ble`, `Nat.bitwise`, `Nat.testBit`, and
`Nat.instAndOp`. Next: separate observation laws from generic infrastructure
in that intersection and construct one explicit contract interface consumed by
at least three siblings.
The exact four-target bit-observation slice now contains 471 union nodes and a
103-node shared core; target-specific deltas are 106/87/88/87. Its five current
axiom-free `Nat.testBit` candidates cover zero/successor, bounds, and sums, but
not the required `Nat.bitwise` or list-lookup commutation. Next: inventory exact
lower-level recurrence theorems and construct one operator-parametric generic
law without using a desired target conclusion as its own contract witness.
Pinned Lean already supplies that generic law as `Nat.testBit_bitwise`, and
Mathlib's and/or/difference targets are direct specializations. A root-selected
external export independently imports, but its measured footprint contains
`propext` and the quotient package, with 29 direct theorem dependencies. It is
candidate guidance only. Next: add an exact imported-candidate search
population with footprint-aware `reconstruct-required` routing, then rebuild
the generic theorem constructively inside the imported kernel before any
three-sibling production claim.
The footprint-aware imported-candidate index now provides that separate search
population. Its first exact row is strategy-eligible but execution-ineligible,
and a Rust descriptor reproduces canonical/alpha type hashes, declaration and
dependency identities, 29 theorem dependencies, and the five-member footprint
from the external stream. Next: expose this index through the candidate-only
agent read surface and dispatch reconstruction for its row.
The agent now exposes that index through a separate ninth tier-R tool. Exact
name/type queries preserve the bitwise candidate's source, five-member
footprint, 29-dependency count, and `execution_eligible=false`; invalid query
shapes fail closed and the toolset policy fingerprint moves. Next: implement a
reconstruction proposal that consumes strategy metadata without importing the
assumption-bearing proof term.
The assumption-bearing theorem now materializes as a proof-free 10 KiB
reconstruction target: 12 declarations, two explicit definition abstractions,
zero normalization rewrites, and an empty footprint. The source theorem name is
absent. Next: reconstruct this generalized goal and issue exact specialization
evidence before attempting the three bitwise siblings.
Immediate semantic review refuted that generalized proposition: unconstrained
operation parameters admit a concrete `false = true` countermodel. The capsule
is now explicitly execution-ineligible, and the checker fails closed unless the
countermodel remains valid. Next: construct and check a law-bearing semantic
interface before reconstruction dispatch.
The replacement demand is now machine-readable: five law obligations join the
exact candidate type to the two exact implementation-graph definition hashes,
and a checked successor-bit witness proves the interface excludes the earlier
countermodel. All imported supports remain labeled assumption-bearing; next is
clean reconstruction of the law leaves, beginning with `testBit_succ`.
Exact retrieval found the native successor and zero-bit laws already axiom-free,
but also caught their result-sort mismatch: native observation is `AxNat`, while
the imported contract is `Bool`. The demand now binds both native types and
adds an explicit missing Boolean/numeric observation-transport obligation.
The native half of that transport now exists: a constructive Boolean view of
numeric bits preserves the successor equation by reflexivity and has an empty
kernel footprint. Exact equivalence to the imported Bool-valued definition is
still missing and explicitly receives zero credit.
The old capsule command now also fails closed by default: writing the refuted
statement requires an explicit `--emit-refuted-diagnostic` opt-in, so omitting
the separate metadata checker cannot accidentally make it a producer target.
Exact definition descriptors now bind both imported operation bodies, types,
direct closures, and footprints. Each concrete implementation reaches
`propext`; `testBit` does so through its typeclass-expanded shift/and/equality
route, while `bitwise` reaches a private unary worker and `PSigma`. Clean work
must therefore reconstruct target-owned semantics rather than graft definitions.
The target-owned pointwise bitwise algebra now checks axiom-free for arbitrary
Boolean operators. The remaining mathematical obligation is sharply isolated:
reify that observation function as a natural number, then prove its observations
round-trip. Observation-level success is explicitly denied theorem credit.
Bounded reification is now implemented as the binary weighted sum, and its
zero-length base theorem checks axiom-free. The exact remaining proof is the
bounded observation round-trip for `i < k`; neither that induction nor the
unbounded bitwise theorem has received credit.
The reifier's successor equation now also checks axiom-free, exposing the prefix
plus one weighted digit as a stable induction interface. The round-trip theorem
remains the next proof; implementation unfolding is no longer required.
The Boolean digit map now round-trips through bit zero axiom-free. The kernel
correctly rejected treating the one-bit weighted sum as definitionally equal to
that digit, exposing weighted-sum normalization as the next arithmetic lemma
instead of silently conflating the two.
That explicit chain now checks: one-bit weighted-sum normalization and the
transported one-bit observation round trip are both axiom-free. The open proof
has narrowed to the general `i < k` bounded round trip.
An exhaustive oracle now checks all 8,191 Boolean vectors through 12 bits,
covering 90,114 in-range and 8,191 boundary observations. It validates the
construction but is explicitly non-proof evidence; the universal kernel theorem
remains open.
The Boolean coefficient bound `boolToBit b ≤ 1` now checks constructively and
axiom-free. It supplies the missing local inequality for the universal
`reifyBits bits k < 2^k` induction.
The universal size theorem now checks axiom-free: every `k`-bit reification is
strictly below `2^k`. The remaining universal obligation is observation
round-trip/uniqueness, not existence or boundedness of the constructed number.
The bound now composes with native `sum_testBit_lt` and `mod_eq_self_of_lt` to
prove a universal numeric reconstruction round trip, also axiom-free. The
remaining seam is componentwise digit uniqueness below `k`, followed by the
already-checked Boolean transport.
The low-digit decoder now proves axiom-free that `boolToBit b + 2*n` has
quotient `n` and remainder `boolToBit b` under division by two, using a
constructed `divMod` witness and uniqueness against executable division. Next:
put the bounded reifier into this low-digit-first form and induct the decoder
to componentwise uniqueness.
That induction now checks axiom-free: the low-digit-first reifier round-trips at
every `i < k`. Specializing it to `bitwiseObservation` yields the first bounded
bitwise theorem with an empty footprint. Next: derive a sufficient input width
and prove all out-of-range observations are false under `f false false = false`;
weighted-reifier equivalence and exact imported-operation equivalence remain
separate, uncredited obligations.
The output-side tail is now complete as well: zero has only false observations,
and every bit at `offset+k` of a width-`k` low reification is false, universally
and axiom-free. The unbounded theorem now needs only an input-side sufficient
width theorem plus the `f false false = false` join; imported equivalence stays
separate.
The input theorem and join now close too. `testBitBool_beyond_bound` proves a
simple sufficient width directly from divide-by-two recursion; `bitwiseTotal`
uses width `x+y`; and `testBitBool_bitwiseTotal` proves the desired equation at
every index under exactly `f false false = false`, axiom-free. The native
mathematics is complete. Exact equivalence to imported Lean `Nat.testBit` and
`Nat.bitwise` is now the sole reconstruction blocker and still receives zero
credit.
Two `Eq.refl` controls now establish the precise trust boundary: merely naming
either imported operation in a theorem statement makes the declaration-reached
footprint `[propext]`, even with zero theorem dependencies. Exact imported
empty-footprint reconstruction is therefore structurally unavailable under the
current definitions, not awaiting a cleverer proof. Next: choose the clean
product boundary deliberately—target-owned operations, clean compatible
definition reconstruction, or an explicitly weaker upstream-definition route.
Candidate routing now acts on that distinction: ordinary assumption-bearing
candidates without a measured statement floor remain eligible for proof
reconstruction, while `Nat.testBit_bitwise` is classified as
`clean-definition-reconstruction-required`, exposes `[propext]` as the floor,
and cannot consume proof-reconstruction budget. Next: specialize the completed
target-owned law into one reusable bitwise family without claiming exact
imported-definition identity.
That specialization now covers AND, OR, and difference. Each target-owned
operation uses the same `bitwiseTotal` constructor; each observation theorem is
an instantiation of `testBitBool_bitwiseTotal`, has an empty footprint, and
records the generic theorem dependency. The three-sibling reuse bar is met
without one proof per target or a false exact-import claim. Next: expose this
family as a reusable producer/knowledge operation rather than example-only
kernel declarations.
A generated projection now connects the three clean theorems to the three open
development facts for imported `land`, `lor`, and `ldiff`, while marking every
edge as semantic analogy rather than exact identity. It reports three clean
analogues, zero exact matches, and zero operation-eligible targets. The graph
can now use the connection without closing the wrong proposition. Next: promote
the target-owned family into a reusable library surface with its own durable
fact identities before considering producer registration.
The family is now reusable outside its builder process: a root-selected
official-format capsule re-imports 116 declarations with no axioms, and all
three root identities reproduce byte-for-byte from the checked builder. The
243,235-byte read-only pack stays outside Git; a committed receipt binds its
hash, population, provenance, and generic-theorem dependencies. Next: expose
the capsule through held-out-safe agent retrieval as target-owned library
material while preserving zero exact-imported and autonomous credit.
An end-to-end read-surface audit found that the typed Python
`imported_candidates` tool still exposed the obsolete one-dimensional route
even though the generated index had changed. The model and tool now carry the
statement axiom floor, proof-reconstruction eligibility, and required clean
definition route; its test requires `[propext]` and refuses the stale label.
Next: add the clean capsule roots as a separate target-owned retrieval
population, never as imported exact candidates.
The tier-R `target_owned_candidates` surface now does that. It searches exact
name or canonical type, returns capsule and declaration identities, preserves
empty footprints and generic dependencies, labels semantic analogue links as
non-exact/non-authoritative, and removes protected fact IDs through the central
held-out filter. The focused 35-test tool suite and the broader 105-test agent
suite pass. A full 1,861-test Python run reached 1,824 passes and exposed one
failure plus two setup errors already present outside this lane: the repository
currently violates its standard-library-only `scripts/` test in three existing
scripts, and the held-out gate rejects newly referenced exclusion lists. Do not
report the full Python gate green until those concurrent integration defects
land. The script-layer defect is now repaired: extension-dependent producer
implementations and tests live under the typed Python package, while three
stable standard-library-only launchers preserve the existing commands. This
made seven hidden type diagnostics visible and fixed them without widening the
four-diagnostic baseline. The refreshed bounded census is 6/111 (5.4%), so two
new eligible theorem goals correctly register as producer declines rather than
volume credit. The held-out-isolation setup errors are now closed without an
exception: all agent-readable exclusion arrays were replaced by
count/hash/redaction receipts, and consumers independently derive the protected
set from the nursery. The gate scans 1,066 files against 37 held-out facts and
reports zero references. The full Python authority is now green at 1,881
collected, 1,847 passed, and 34 skipped, with zero failures or errors; Rust,
docs, and remote CI remain separate claims.

**WIP, open-problems-programme, 2026-08-26.** Five durable research packages now own the
Rado/Schur, GF(2) bilinear-rank, S-box optimality, SIMD-shuffle minimality, and optimization
bound-certification targets.  The Axeyum-side programme contract is
`docs/research/10-cas/open-problems-programme-2026-08.md`: pin current literature status,
generate deterministically, run untrusted search, independently replay/check, bind evidence,
and reconstruct formal identities into the kernel where applicable. Current focus stays on
`abz7`: deterministic detectable-precedence closure is complete and exhausted after one round,
and an exact checker-compatible FlatZinc/DRCP route is calibrated against both an independent
Rust checker and the Rocq-verified FznDrcpCheck. Sustained `abz7@655` proof production remains
live without a short wall-clock cutoff; the upper-bound search is closed by the replayed public
656 witness described below. The
settled-cell calibration is green for `R_3(x-y=z)=14` (42 variables,
356 clauses, 25 checked DRAT steps); a mutated DIMACS header fails closed, and the aggregate
claim sweep reports 104 claims re-checked / 0 errors / 25 rows explicitly not re-checked.
Frontier claims remain open.

**Job-shop published-witness import, 2026-08-26.** ADR-0576 adds strict parsing of the common
one-job-per-machine-order-row solution format and deterministic earliest-schedule reconstruction
over the combined job/machine precedence DAG. Malformed permutations and cyclic rows fail closed;
the resulting start matrix is independently replayed and pinned into the bounded CNF. A live
current-source search found Optimizizer's retained 15-row `abz7` solution. Axeyum reconstructed
all 300 starts at makespan 656 and returned `sat-replayed` against the 175,770-variable /
1,696,774-clause exact-window formula. This closes the upper-bound half and supersedes the local
657 search as evidence. It does not prove optimality: sustained `abz7@655` DRCP producers remain
live, and only a completed proof accepted by both calibrated checkers can close the lower half.

**Job-shop FDS gap localization, 2026-08-26.** The current pinned OptalCP 2026.2.0 preview
benchmark was reproduced on the byte-equivalent `abz7` instance with four workers, seed 1,
zero gap tolerances, verified solutions, and two level-4 no-overlap / level-3 cumulative FDS
workers. It internally raised the lower bound to 656 at 59.877 seconds and reported optimum at
108.466 seconds (5,833,383 branches, 2,636,506 failures). This is strong search-direction
telemetry, not evidence: its `proof: true` field has no exported proof object, every one of 300
solution-value slots is null, and no independent checker can replay its inference. A hash-bound
package receipt records that fail-closed boundary. The generic missing capability is now sharply
identified as certifiable scheduling propagation/search composition, while all seven independent
DRCP/DRAT proof producers continue without short cutoffs.

**Checked energetic-overload boundary, 2026-08-26.** ADR-0577 adds a reusable cumulative-task
window type and exact energetic checker: task membership, domains, duration, demand, capacity,
and compulsory energy are recomputed with checked arithmetic, and only a strict overload is a
conflict. Portable job-shop conflicts replay either defining job-chain windows or ADR-0574's
precedence closure; schema, bound, machine, interval, and energy mutations fail closed. The
bounded exhaustive scan evaluates all integer intervals under explicit ceilings. On `abz7@655`,
3,222,600 intervals / 64,452,000 task contributions identify machine 5 `[0,538)` at 533/538
required/capacity energy in 0.75 seconds. Repeating after all 256 forced precedences gives exactly
the same ratio, so no root conflict exists and none is emitted. Conditional conflict composition
under branch domains is the next required layer; the target lower bound remains open.

**Checked conditional energetic clauses, 2026-08-26.** ADR-0578 adds canonical semantic
start-bound assumptions, independent conditional-overload replay, and an exact bridge from each
assumption's negation to the existing operation prefix variables. A bounded deterministic
producer searches one interval and relaxes its explanation before replay. On the strongest
`abz7@655` interval it checks 40 candidates and proves that job 2 operation 10 must start after
532: the contrary domain requires 539 units in 538 available. The 175,170-variable /
1,690,226-clause precedence-closure formula gains exactly one checked unit. Matched 30-second
CaDiCaL runs remained unknown, so no speedup or lower-bound claim is made. Fourteen focused
job-shop tests and all-feature Clippy are green; the next layer is a bounded all-interval unit
fixpoint before multi-assumption clauses or checked cover composition. All seven full-proof
producers remain live.

**Exhaustive standalone energetic units, 2026-08-26.** ADR-0579 scans every machine interval
and both one-sided bounds for every flexible task under explicit resource ceilings, uses monotone
binary search for the strongest implied unit, and independently replays every retained artifact
before bulk CNF insertion. The `ft06 = 55` control finds two units and preserves a lifted/replayed
optimal schedule. On `abz7@655`, 3,222,600 intervals / 128,904,000 candidates / 322,261,348
task checks complete in 7.49 seconds and retain exactly two deductions: `start(2,10) > 532` and
`start(7,0) < 24`. The exact formula gains two clauses; a matched 30-second SAT run remains
unknown. This exhausts standalone units, not contextual propagation under learned bounds, and
does not change the open lower-bound verdict.

**Contextual energetic fixpoint, 2026-08-26.** ADR-0580 turns replayed unit conflicts into a
bounded implication chain: semantic start bounds propagate across job chains and detectable
machine precedences, every contextual overload retains the complete assumption conjunction, and
each clause is independently replayed before insertion. A single release command reproduces four
exhaustive `abz7@655` rounds with conflict counts 2/2/1/0 and six final bounds. Forced machine
orders rise from 256 to 861; 1,289,053,403 exact task-energy checks produce five contextual plus
two premise clauses, growing the 175,170-variable formula from 1,690,226 to 1,690,233 clauses.
The closure stabilizes without a precedence or energetic contradiction, and matched 30-second
CaDiCaL runs remain unknown, so no lower bound or speedup is claimed. This exhausts the current
contextual energetic-unit layer; certified edge-finding/not-first/not-last explanations or checked
branch composition are the next materially different lower-bound routes. All seven sustained
DRCP/DRAT producers remain live.

**Rado frontier file-backed proof consumption, 2026-08-26.** The exact
`R_5(3(x-y)=2z)@351` producer is still live and its multi-gigabyte DRAT prefix carries no
credit. Before completion, the independent `akb2_frontier check` path was changed from holding
both the complete proof text and a parsed step vector to Axeyum's existing file-backed backward
checker, which retains only the reverse clause plan required by the algorithm. The settled
`R_3(x-y=z)=14` control regenerated a 25-step / 263-byte proof and the changed command accepted
it from disk with `route=file-backed-backward`; all-target/all-feature Clippy and
warning-denied Rustdoc pass. This is checker-readiness, not a result at 351.

**Strict external SAT-model replay boundary, 2026-08-26.** A reusable harness parser now
imports SAT Competition output only when it contains exactly one `SATISFIABLE` status, a
terminated complete assignment of the declared width, and no duplicate contradiction,
out-of-range literal, post-terminator payload, or missing variable. The job-shop importer no
longer owns a permissive duplicate, and `akb2_frontier check-model` evaluates the imported
assignment against the regenerated CNF, lifts its one-hot colouring, independently replays the
defining relation, re-evaluates the lifted witness, and only then writes it. Eight malformed
controls fail closed; focused tests, all-target/all-feature Clippy, and warning-denied Rustdoc
pass. The live `n=351` producer has not returned SAT, so this closes an evidence-route gap rather
than establishing a new bound.

**Rado 351 local-search experiment closed honestly, 2026-08-26.** The ordinary portfolio
completed 192 equal-budget jobs / 3.84 billion moves in 5,142.3 wall seconds without a
colouring. The experimental constraint-weighted portfolio completed 96 jobs / 1.92 billion
moves, also without a colouring; normalized user CPU was 225.66 versus 207.89 seconds per job
(+8.55%), and peak RSS was 401,924 versus 178,932 KiB (2.25 times). Different thread counts and
changing contention make wall time non-comparable. Weighting demonstrated no frontier benefit
and was removed rather than promoted. The independently justified CLI `noise`/`tie` controls,
percentage validation, and one-colour/100%-noise panic repair remain; focused tests,
all-target/all-feature Clippy, and warning-denied Rustdoc pass. Both completed `not-found` runs
carry no UNSAT or upper-bound credit; the exact proof-producing run remains live.

**Rado exact lower bound advanced, 2026-08-26.** The seed-619 CaDiCaL producer completed the
canonical 351-, 352-, 353-, and 354-point formulas SAT; the 354 run took 35:44.27. Every complete
assignment passed the strict SAT Competition importer, regenerated CNF evaluation, unique
one-hot decoding, independent enumeration of the defining relation, and lifted-witness
re-encoding. The retained strongest witness has 354 entries, uses all five colours, covers
27,730 defining triples / 143,957 clauses, and has SHA-256
`bdbefdab98481c995876fcf1a31b5b82b352ba50b5ac472595912b9a33c4fcba`. Therefore the checked
conclusion is now `R_5(3(x-y)=2z) > 354`; no upper bound or exact value is claimed. A persistent
exact driver is live at 355 and advances only after both replay routes. A post-result literature
refresh through 2026-08-26 found no five-colour bound at least 354 for this equation, but that
negative retrieval is not proof of priority.

**Shared import boundary, 2026-08-25.** ADR-0555 adds a non-authoritative, hash-pinned
external-certificate replay runner for all five packages.  It validates checker and artifact
bytes before execution, hard-kills a timed-out process session, requires an observable finding
in addition to exit zero, and emits a content-addressed three-outcome receipt.  Four focused
tests cover success, pre-execution mutation rejection, false-success rejection, and timeout;
format-specific independent checking is still required before any imported result gains
Axeyum evidence or kernel authority.

**Bilinear upper-certificate slice, 2026-08-25.** ADR-0556 adds a public bounded exact
`GF(2)` rank-one tensor-decomposition checker and independent full-polynomial target
generator. Wang's published rank-17 `P_6` witness matches all 396 target coefficients; a
one-entry mutation exits 1 at `[0,0,0]`. This independently reproduces the known upper bound
17 but does not narrow `[16,17]`. The pinned published lower-bound verifier has now replayed
`P_6 >= 16` in 26:08 wall / 17,532 KiB peak RSS; raising an early flattening claim from 6 to
7 aborts in under one second after recomputing 6. The separate hash-pinned replay completed
in 1,547,630 ms with verdict `verified` and canonical receipt hash `d5153fac...145eda`.
This is upstream-checker reproduction, not an independent Axeyum lower-bound proof.

**Certification arithmetic and source audit, 2026-08-25.** Krpan--Povh's sole arXiv
ancillary was completely inventoried: it contains graphs, scalar logs, and source, but no
primal/dual matrix or certificate; its source rounds floating MOSEK objective bounds with a
`1e-9` offset and discards the task. ADR-0557 adds a bounded exact `BigRational` PSD checker
alongside the existing checked-`i128` route. Large coefficients succeed, indefinite controls
fail, and intermediate growth declines explicitly. Producing and graph-binding an exact dual
matrix remain open.

**Certification novelty correction, 2026-08-26.** The brief's ZykovColor claim is no longer
current: Dold et al., CP 2026, already add VeriPB logging to ZykovColor and formally check
the result with CakePBcolour. The official 13,145,463-byte Zenodo archive (SHA-256
`5aa7f082...232e75`) contains the producer, VeriPB, CakePB, command wrapper, and experimental
logs; its tables cover 137 DIMACS and 1,000 random-graph attempts. Target 5c is therefore a
reproduction/import or coverage-extension candidate, not a first. This does not touch 5a:
the overlapping `C2000.9` stem in a colouring corpus is not a certificate for the
Krpan--Povh maximum-clique theta bound.

**Instance-bound theta duals, 2026-08-26.** ADR-0560 closes the graph/objective/PSD binding
gap: `sos::theta::check_theta_clique_dual` validates an undirected graph and sparse exact
non-edge multipliers, reconstructs `t I + Y - J`, and accepts only if ADR-0557's bounded
BigRational checker proves the slack PSD. `K_3 <= 3` and empty-three <= 1 verify; false
`K_3 <= 2`, edge-supported or duplicate multipliers, malformed graphs, and resource-policy
controls fail or decline in their distinct channels. The published target solver discarded
its dual variables, so none of 73/115/168 is certified yet.

**S-box positive-certificate slice, 2026-08-26.** ADR-0558 adds a portable named-wire
Boolean-circuit artifact and bounded complete truth-table checker. The published
`PRIMATEs^-1` witness matches all 32 independently sourced rows with 8 AND, 35 XOR, and 2 NOT
gates; changing its first XOR to XNOR exits 1 on row 0. This reproduces the known upper bound
8, not optimality or a new result. General bit-gate synthesis and a checked target-boundary
UNSAT remain open.

**Multiplicative synthesis envelope, 2026-08-26.** ADR-0561 adds the complete deterministic
affine-between-AND SAT encoding, model-to-ADR-0558 lifting with exhaustive replay, and
backward-checked DRAT for UNSAT. All 16 two-input functions reproduce their exact affine/
one-AND boundary. The published PRIMATEs-inverse MC=8 circuit normalizes into the same
9,326-variable / 31,712-clause formula; 222 selector units solve, lift, and replay. Unpinned
MC=8 at 30 seconds and the known MC=6 lower-bound control at 120 seconds both interrupted,
so no MC=7 frontier result is credited. Symmetry/performance work is next.

**SIMD semantic/minimality calibration, 2026-08-26.** ADR-0559 adds exact provenance-tag
semantics for unary AVX2 `vpshufb` and same-source `vperm2i128`. Global 32-byte reversal
replays in two instructions; the complete one-step family query is a deterministic
2-variable/4-clause CNF whose serialized one-step DRAT proof is accepted by the independent
backward checker. A GCC intrinsic oracle agrees on all 32 bytes on AVX2 hardware, while a
one-control mutation exits 1 at byte 16. This establishes minimal length 2 only in the named
two-family subset and is a calibration, not the open ISA-wide result. Multi-step synthesis
with lifted controls and additional instruction families remains open.

**SIMD five-family bounded synthesis, 2026-08-26.** ADR-0566 closes that named next step with
a complete multi-step SAT encoder for permutation-preserving unary `vpshufb`, `vpermd`,
`vpermq`, same-source `vpalignr`, and same-source `vperm2i128`. Global byte reversal's
one-step query is 2,663 variables / 87,940 clauses; CaDiCaL's 957,982-byte DRAT proof is
accepted by Axeyum. The 4,302-variable / 159,912-clause two-step query lifts and independently
replays a `vpermd; vpshufb` program. A hardware oracle agrees with every modeled family and
rejects a direction mutation. This proves minimum length two only in the exact unary language;
LLVM already records a two-operation AVX2 byte reverse, and current Scholar/arXiv/web searches
do not justify a novelty-priority claim. Multi-source and weighted-cost synthesis remain open.

**SIMD weighted dependent-latency synthesis, 2026-08-26.** ADR-0583 adds generic,
resource-bounded weighted-at-most CNF composition and uses it without changing the ordinary
unweighted formula bytes. Under the explicitly named Haswell register-form serial dependency
profile `vpshufb=1, vpermd=3, vpermq=3, vpalignr=1, vperm2i128=3`, global byte reversal has
minimum cost four in the same exact unary language. Cost at most three is 6,024 variables /
235,303 clauses; CaDiCaL's 12,554,825-byte DRAT is accepted by Axeyum's file-backed backward
checker, while a 64-byte truncation is rejected. Cost four is SAT and lifts/replays as
`vpermd; vpshufb`. Intel explicitly scopes added latency to dependency chains, so this is not
a throughput, port-scheduling, whole-machine, ISA-wide, or priority claim. The durable sibling
package retains deterministic compressed CNF/DRAT, hashes, diary, provenance, and a cleanly
built LaTeX note. Multi-source live-register semantics and a real scheduler objective remain
the open SIMD boundary.

**SIMD multi-source live-value synthesis, 2026-08-26.** ADR-0585 replaces the unary
accumulator boundary with a reusable bounded SSA program encoding: the original input and every
earlier result remain selectable as operands. Its exact fourteen-family AVX2 language adds
two-source `vpalignr`, nonzero-control `vperm2i128`, all low/high byte/word/dword/qword unpacks,
and `vpblendd` to the prior permutation families. A GCC intrinsic differential agrees on 11
two-source modes across all 32 bytes and rejects an align-direction mutation. Global byte
reversal's one-step formula has 2,697 variables / 97,314 clauses; CaDiCaL's 1,922,088-byte DRAT
is accepted by Axeyum's file-backed checker, while a two-byte truncation fails. The 4,372-variable
/ 239,078-clause two-step formula lifts and replays `vpshufb; vperm2i128`. This proves minimum
length two only in the exact constant-control SSA language. It excludes memory, insert/extract,
logic composition, register allocation, and scheduling, and carries no novelty-priority claim.
The prior unary formula remains byte-identical, and the sibling package retains deterministic
compressed CNF/DRAT, a manifest, diary, provenance, and LaTeX write-up.

**Boolean-ANF control route, 2026-08-26.** ADR-0562 adds canonical resource-bounded Boolean
polynomials, deterministic Bosphorus interchange, and a sparse coefficient-DAG formulation of
the complete affine-between-AND search. The PRIMATEs-inverse MC=6 control is 738 variables / 759
equations / 8,835 monomials before external preprocessing. Bosphorus 1.2.12 reduced it to 586
free variables / 603 equations / 6,157 monomials and emitted a 5,782-variable / 62,674-clause
CNF. CaDiCaL on the independent truth CNF and CryptoMiniSat on that external CNF both remained
undecided after 300 seconds; Bosphorus solve mode overran its requested deadline and was
interrupted. External rewrites have no UNSAT authority without a checked equivalence chain, so
the published MC=6 lower control remains unreproduced and MC=7 has not been attempted.

**External Rado-bound correction, 2026-08-26.** ADR-0563 adds generic palette
canonicalization and a dual-route colouring witness CLI: independent defining-relation replay,
then evaluation against the freshly regenerated CNF. A live search located Li's public
296-point `R_5(3)>296` witness at pinned commit `e0b30e5...75a74`; Axeyum verifies its
equivalent `3(x-y)=z` colouring and the 1,480-variable / 125,222-clause formula. A one-colour
mutation fails at monochromatic `[1,22,63]`. This supersedes Axeyum's 251-point retained best
and removes any novelty claim for that weaker bound. A 144-million-move probe across all five
warm extensions and a cold start found no 297-point witness; that is explicitly not an upper
bound.

**Bilinear bounded-rank search, 2026-08-26.** ADR-0564 adds row-major matrix tensor generation
and a complete resource-bounded `GF(2)` rank SAT encoding whose models lift into ADR-0556
artifacts and independently replay. Wang's `<3,2,4>` rank-20 witness, after an explicit
output-dual basis permutation, matches all 576 coefficients and passes the pinned 22,984-
variable / 90,952-clause path; a one-support mutation fails at `[0,0,0]`. The known
`<2,2,2>` rank-6 control generated 776 variables / 2,880 clauses; CaDiCaL refuted it in 39.35
seconds and Axeyum's file-backed backward checker accepted its 234,288,465-byte DRAT proof in
196.98 seconds. The open `<3,2,4>` rank-19 baseline (21,806 variables / 85,824 clauses)
reached 300 seconds without a model or proof, so its verdict is interrupted and the bracket
remains `[19,20]`.

**Job-shop certificate route, 2026-08-26.** ADR-0565 adds strict OR-Library parsing,
independent schedule replay, complete bounded-makespan SAT with machine-order/prefix clauses,
untrusted model lifting, and file-backed DRAT checking. The public `ft06` control is now
certified end to end: a 3,692-variable / 15,958-clause SAT model lifts to a replayed makespan-
55 schedule, while the 3,620-variable / 15,640-clause makespan-54 formula has a 375,015-byte
DRAT proof accepted by Axeyum; a precedence mutation fails. This reproduces optimum 55 and is
not advertised as a first result despite finding no earlier artifact in current searches.
The target `abz7@655` formula fits at 381,418 variables / 4,343,486 clauses, but its lower
run and the `@656` witness run both reached 300 seconds without proof/model. Both verdicts are
interrupted, so `abz7 = 656` is not yet certified here.

**Bilinear term-order symmetry, 2026-08-26.** ADR-0567 adds an opt-in complete breaker for
permutation of rank-one summands while leaving all retained baseline formulas byte-stable.
It lex-orders concatenated factor bits, canonicalizes padded witnesses, and passes an
exhaustive comparator test plus reversed-Strassen and Wang rank-20 replay controls. The open
rank-19 formula is 22,688 variables / 89,388 clauses; CaDiCaL reached 300.19 seconds and
7,140,981 conflicts without model/proof. This is interrupted telemetry, not rank evidence,
and it shows that the `19!` term labels are not the whole obstruction. Search found explicit
prior term ordering, so no technique-novelty claim is made; stabilizer/basis symmetry is next.

**Bilinear first-summand normalization, 2026-08-26.** ADR-0568 applies a complete
matrix-tensor stabilizer reduction: a chosen nonzero summand occupies slot zero, its first
factor is one of the `min(m,n)` matrix rank-normal forms, and only the remaining slots are
lex-ordered. Strassen with padding and Wang's rank-20 witness both pin/lift/replay; a valid
decomposition with a non-normal first term is rejected. The open rank-19 formula is 22,641
variables / 89,206 clauses and again reached 300 seconds without model/proof. This remains
`interrupted`, not rank evidence. The de Groote normalization is classical prior mathematics;
the next safe step is a complete stabilizer-orbit cover, not a single assumed orbit.

**S-box complete operand ordering, 2026-08-26.** ADR-0569 replaces the partial
first-coefficient breaker with an opt-in complete lexicographic order on every pair of affine
AND operands across the truth-CNF, direct-ANF-CNF, and portable-ANF routes. Exhaustive
three-bit comparison, every two-input function, a reversed witness, and the published
PRIMATEs-inverse MC=8 circuit all pass lift/replay controls; the old MC=6 formula remains
byte-identical when its mode is selected. The complete MC=6 formula is 6,406 variables /
21,901 clauses and reached 300 seconds with `UNKNOWN`, no model, and no proof. Zhang--Huang
already specify this full order and report their control at 239 seconds, so the technique is
prior art and Axeyum's known lower-bound reproduction remains open. MC=7 was not attempted.

**Trusted Boolean-ANF/CNF bridge, 2026-08-26.** ADR-0570 adds a generic deterministic
definitional extension from bounded Boolean-ANF systems to CNF, with shared monomial-prefix
gates, exact parity chains, projected SAT-model replay, and independently checked DRAT. The
published PRIMATEs-inverse MC=8 witness traverses the complete portable-ANF/CNF/circuit route.
The byte-stable MC=6 source system lowers to 16,820 variables / 57,017 clauses; CaDiCaL 3.0.1
refuted it in 228.81 seconds, and Axeyum's file-backed backward checker accepted the
1,068,108,069-byte proof in 1,377.68 seconds. A 100-line truncation fails closed. This finally
reproduces the known MC>=7 endpoint and, with the replayed MC<=8 witness, independently
checks the published `[7,8]` bracket. It does not decide MC=7. ANF/CNF conversion and the
lower bound are prior work; incomplete forward-citation access precludes a first-artifact
novelty claim.

**Splitter-blind cube composition and first MC=7 frontier probe, 2026-08-26.** ADR-0543 is
accepted and `axeyum-cnf::cube` is now public. The substantial dormant implementation and its
twelve controls were preserved; the landed increment adds file-backed backward checking and
deterministic emitter/checker CLIs, bringing the focused suite to fourteen. Every leaf formula
and the cover CNF are reconstructed from the base formula and literal lists, so no splitter
formula is trusted. Szeider's July 2026 LRAT-Catcher already composes cube proofs inside Lean,
so neither the argument nor formal composition is novel. The PRIMATEs-inverse MC=7 portable
ANF/CNF frontier is 919 variables / 970 equations and 20,585 CNF variables / 69,778 clauses.
A monolithic 600-second run interrupted. A first cover exposed source variable 1 as forced;
two live leaves interrupted. An adaptive exhaustive cover on variables 2 and 3 has a checked
two-step covering proof, but all four leaves interrupted at 600 seconds. No model or complete
leaf-proof set exists, so `[7,8]` is unchanged.

**Premise-explicit exact-budget circuit reduction, 2026-08-26.** ADR-0582 adds a reusable
normal form for a query known to be at its minimum possible budget: every AND operand has a
nonconstant term, every AND result is used later, every essential primary input occurs, and
every varying output coordinate is nonconstant. The ordinary at-most-budget encodings remain
unchanged; the PRIMATEs driver requires the independently checked MC=6 premise by name before
adding these clauses to its MC=7 formula. The generic Boolean-ANF/CNF bridge now composes
validated clauses over source selectors without exposing its private extension variables,
and pure ANF export refuses the disjunctive mode. All eight exact-MC-one two-input functions
remain SAT and replay through both direct and portable routes; malformed source indices fail
closed. The complete MC=7 formula is 20,585 variables / 69,809 clauses with SHA-256
`176513848d1fa511bca2a7b5c50255f6dabe6ebff696eb9f62abcfad0f43ae76`. Two persistent
proof-producing CaDiCaL runs have no short cutoff and remain uncredited. Soeken 2020 already
publishes the corresponding nonconstant/all-used constraints, so no technique novelty is
claimed and `[7,8]` is unchanged.

**Bilinear complete first-factor orbit cover, 2026-08-26.** ADR-0571 exposes typed canonical
support/selector descriptors from normalized matrix-tensor encodings, avoiding dependence on
private CNF allocation. The `<3,2,4>` rank-19 formula reports `[0] -> 495` and `[0,3] -> 496`.
Its complete four-cube Boolean-product cover has a checked covering proof; the two leaves
inconsistent with the base one-hot constraint have independently checked DRAT proofs. The two
live leaves each returned `UNKNOWN` after 600.01 seconds, and their incomplete 5.29/5.68 GB
proof streams were deleted. The exact manifest, cover artifacts, and receipt are retained in
the sibling package. The partition is certified, not the rank bound; `[19,20]` is unchanged.
Focused CNF/search tests, all-feature Clippy, rustdoc, generated-plan/index checks, and links
are green. The full `just check` is independently red before reaching Rust tests because the
settled `Nat.fib_le_succ` fact omits two proof-derived dependencies; correcting those edges
then exposes a stale historical Autogenesis child-qualification contract. Neither belongs to
this lane, so no full-gate success is claimed.

**Bilinear polynomial-family artifact boundary, 2026-08-26.** ADR-0581 adds the missing
family-native `P_n` synthesis driver over the existing complete tensor-rank encoder. It exports
deterministic DIMACS, pins known decompositions, imports only complete strict SAT Competition
models, lifts them to portable JSON and independently replays every coefficient, or checks a
completed textual DRAT from disk. The two-sided `P_2` control replays rank 3 from an external
model and checks a 130-byte rank-2 refutation; empty output exits nonzero without writing a
witness. Wang's rank-17 `P_6` construction pins, lifts and replays all 396 coefficients. The
complete ordered `P_6@16` formula has 13,289 variables / 52,110 clauses, raw SHA-256
`d5692510...6d940`, and is under sustained no-short-cutoff CaDiCaL search. Its live proof prefix
carries no rank credit. The primary source remains arXiv v10 (2026-07-30), and refreshed exact
searches found no closure through 2026-08-26; this is negative retrieval evidence, not priority
proof.

**Job-shop exact windows and semantic order cover, 2026-08-26.** ADR-0572 adds an opt-in
complete operation-domain restriction from exact job-chain earliest/latest starts and exposes
all machine-order selector variables as typed, deterministic semantic records. `ft06` retains
its checked 55/54 boundary while shrinking by more than half. `abz7@655` falls from 381,418
variables / 4,343,486 clauses to 175,170 / 1,689,970, but 600-second lower and upper runs and
a deterministic 300-second CP-SAT upper run all remained `UNKNOWN`. A checked Boolean-product
cover over two typed order selectors proves four leaves exhaustive; every leaf remained
`UNKNOWN` at 120 seconds. ADR-0573 fixes the generic bottleneck this cover exposed: internal
proof SAT now branches only on variables occurring in clauses, taking the sparse cover from
more than two minutes without completion to a 3.55-second checked proof. Exact formulas,
semantic maps, cover proof, manifest, and resource receipt are retained in the sibling package;
incomplete 4.15 GB leaf proof streams were deleted. `abz7 = 656` remains uncertified.

**Job-shop detectable-precedence closure, 2026-08-26.** ADR-0574 adds deterministic
longest-path earliest/latest propagation over job and logically necessary machine edges.
Every machine pair is classified free, forced in either direction, or infeasible; forced
edges close to a fixpoint and remain attached to typed selectors. Baseline/closure parity and
lifted replay cover all 64 two-job/two-machine routing/duration patterns across bounds zero
through eight (576 checks). `abz7@655` forces 256 orders and `@656` forces 254, but both
stabilize after one productive round. A matched 180-second SAT run remained unknown. A
redundant time-capacity encoding was measured at 2.27 million variables / 7.97 million clauses
and 2.12 GiB RSS, then removed rather than retained as a misleading capability.

**Job-shop DRCP proof interchange, 2026-08-26.** ADR-0575 adds strict deterministic bounded
job-shop FlatZinc export on the exact predicate surface shared by Pumpkin and its checkers:
job-chain domains, `int_lin_le` precedences, and unit-demand/capacity-one cumulative machine
constraints. The `ft06@54` calibration emits a 19,396-byte gzipped full DRCP proof accepted by
Pumpkin's independent checker and FznDrcpCheck rebuilt from its Rocq development; weakening a
machine duration makes both reject inference 1887. CP 2026 already establishes the general
formally verified DRCP route, so no technique novelty is claimed. A full `abz7@655` DRCP run
is live on `/data0`; only completion plus both checks can establish the lower bound. A
deterministic makespan-678 schedule has independently replayed and now warms a sustained
six-hour CP-SAT search for the still-missing 656 witness.

**The kernel's stack requirement is now a measured, pinned, gated number, and
the numbers say the margin was zero** (`WIP`, kernel-envelope, 2026-08-26).

The trigger was `CReal.e` making
`every_creal_declaration_is_checked_and_axiom_free` — the single test behind
this project's axiom-freedom claim — SIGABRT instead of run. Exit 134 is
indistinguishable from a broken tool or an absent declaration, and this
repository has read it as both.

Bisected the real requirement (`scripts/check-kernel-stack-envelope.sh
--measure`): the smallest power-of-two thread stack on which each prelude
build completes.

| prelude | debug | release | ratio |
|---|---:|---:|---:|
| `cpoint` | **33,554,432** | 1,048,576 | 32× |
| `complex` | 4,194,304 | 262,144 | 16× |
| `creal` | **2,097,152** | 131,072 | 16× |
| `rat` | 1,048,576 | 131,072 | 8× |

`creal` in debug needs **exactly** the 2 MiB default a spawned thread gets,
which is what a `#[test]` runs on — there was never any margin, and one deep
declaration was always going to end it. `cpoint` needs 32 MiB, so the five
sites using a 64 MiB `on_a_deep_stack` copy had **2×** headroom, not the
comfortable margin the number looks like.

**The recursion-depth limit that was proposed is the wrong instrument, and the
measurements are why** (ADR-0584). Debug frames cost up to 32× release frames
at *identical* depth, so one constant cannot serve both profiles; the two deep
recursions cost ~2,250 B and ~576 B per frame, so depth does not predict stack;
and only `infer_core`/`check_core` return `Result` — `whnf_core`,
`def_eq_core_uncached`, `instantiate_aux` and `abstract_aux` cannot report one.
Lean 4.30's own kernel uses a **stack-pointer probe** with a 128 KiB margin
throwing a catchable `stack_space_exception`; the depth counter arrived only in
4.34, as a supplement. That design is deferred with its open questions written
down, not rejected.

**Method note worth more than the numbers.** The first measurement instrumented
`infer_core`, `whnf_core`, `def_eq_core_uncached` and `instantiate_aux` with a
stack-pointer probe and reported a `cpoint` peak of 1,681,616 B — **12× too
small**, and I nearly set the shared constant from it. A probe sees only the
frames it is installed in, and the deepest recursion of a run need not pass
through any of them (`Kernel::abstract_aux` recurses over the term and was not
instrumented). The subprocess bisection measures the process instead of a
chosen subset of it.

**Next.** (a) `creal/creal_tests.rs` still carries a private 1 GiB helper and a
doc comment blaming `axiom_footprint`, which is an explicit worklist and cannot
recurse — another lane owns that file. (b) `creal/integral.rs`'s
concrete-instantiation tests are the workload that set the 256 MiB constant and
the only one still unmeasured; they need their own probe mode. (c) The deferred
headroom probe, if a caller ever needs to survive exhaustion rather than gate
against it.

**WIP (autogenesis-knowledge-overlay, 2026-08-24).** A backward-compatible version-1 sidecar joins existing facts and operations to reusable capabilities and pinned read-only `math-education` concepts or techniques.

F1 is complete: the two authoritative multi-target operations have nine applicable facts, all nine have explicitly partial concept/encounter mappings, and seven evidence credits are checked against their fact records (the other two were settled by earlier one-target operations).

The owning fact, operation, claim, and kernel schemas are unchanged; local/external endpoints and false complete-coverage or uncredited-producer edges are mutation-tested.

F2 now projects 1,142 current kernel declarations and 4,127 direct theorem dependencies from accepted terms, with theorem/definition/inductive/constructor/recursor kinds and prelude visibility kept distinct.

Next: normalize producer declines into typed, measured obstructions rather than hand-authoring the next bottleneck.

F3 now normalizes 47 retained decline records into 20 families while preserving unknown remedies and unbound resolutions; next is representation/transport lineage.

F4/F5/F6 now publish hash-bound transport coverage, non-authoritative scheduler observations, and a capability-gap projection.

Live frontier evidence is the limiting result:

141 facts are dependency-ready but zero are admissible because none has a registered applicable operation.

Detail and older landed rows moved to [`../notes/40-autogenesis-knowledge-overlay.md`](docs/plan/notes/40-autogenesis-knowledge-overlay.md).

**Status:** Exact Mathlib 4.30 `Nat.fib_gcd`, `Nat.fib_dvd`, `Int.fib_natCast`, `Int.fib_add_two`, both recurrence corollaries, `Int.fib_neg`, `Int.gcd_fib`, `Int.fib_dvd`, `Int.fib_of_nonneg`, `Nat.fib_pos`, `Nat.fib_eq_zero`, and now `Int.fib_eq_zero` are durably proved with empty kernel footprints. An isolated clean replay independently reproduced `Int.fib_eq_zero` selection, certified execution, exit-75 recovery, exactly one ledger write, its proved fact, and the preregistered empty readiness delta.

**Next:** preregister exact `Int.fib_add` specialization over sealed recurrence uniqueness, exact constructive induction, admitted `Int.fib_add_two`, and the smallest clean algebra/base-value supports.

Detail and older landed rows moved to [`../notes/40-autogenesis-program.md`](docs/plan/notes/40-autogenesis-program.md).

**D3 grouping is BLOCKED, not queued (`BLOCKED`, solver-arith-group,
2026-08-17).** Sent to execute the one D3 group the 2026-08-17 edge measurement
supported (arithmetic; the other three were refuted). Re-measured first, and did
not move any files — two reasons, both in
[`03-solver-decomposition.md`](docs/refactor-2026-08/03-solver-decomposition.md)
under "Measured 2026-08-17 (second pass)".

1. The first pass committed no script, so its membership rule is unrecoverable
   and its arithmetic verdict does not survive re-derivation: sweeping plausible
   boundaries moves the degree-matched p from <0.0001 (23 modules) to 0.377 (39),
   crossing out of significance **at the 34–35 modules the first pass itself
   reported** (p = 0.110). Only the `strings` row reproduces exactly, because
   zero internal edges pins the set.
2. The move fails the gate for every membership. A directory is *one* node in
   `analyze_solver_module_graph.py`, so grouping merges nodes and creates cycles
   no member had. Best case (23-module core): `mbp` newly enters the theory
   core's cycle and the largest cycle grows **58,215 → 103,514 lines**, 25.8% →
   45.8% of the crate, while its module count moves 24 → 25. Every wider
   membership also adds `arith -> reconstruct`, destroying D1's precondition.

Landed the measurement as code instead — `scripts/analyze_solver_group_collapse.py`,
exit status is the finding — so the next lane decides this before moving a file
rather than after.

**Next:** not this. The blocker is the arithmetic ↔ `auto` / `reconstruct`
cycle; D3's sequencing item 3 now depends on item 4 (`D1` narrowing), not the
other way round. Whoever takes that: run
`scripts/analyze_solver_group_collapse.py --group arith-core --check` and watch
it go green — that is the exit criterion, and it is currently red.

**Both of Euclid's missing ingredients are in; `F:nat-exists-prime-gt` is one
slice from closing** (`WIP`, nat-prime-divisor, 2026-08-17).
`Nat.exists_prime_dvd : ∀ m, 2 ≤ m → ∃ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) ∧ p ∣ m`
is admitted axiom-free, recorded as `F:nat-exists-prime-dvd`. It did **not** go
through `lt_well_founded`, which is what the previous lane's note predicted:
strong induction on `m` has to *decide* primality of `m`, and a bounded `∀` is
not decidable constructively without a bounded search anyway — so the search is
done directly, by ordinary `Nat.rec` on the bound, returning the **least**
divisor `≥ 2`. Leastness is what makes primality free; a proper divisor of the
least divisor would be a smaller divisor of `m`. Each step decides `succ j ∣ m`
by reducing `beq (mod m (succ j)) 0`, with the branches separated by the checked
`div_mod_remainder_eq_zero_iff_dvd`. Nothing classical, nothing well-founded.

**A theorem-only slice is kernel-guarded, but its *statement* is not.** No
`Definition` was added, so there is no degenerate computation rule to fear — the
kernel refuses a false theorem and a non-prime witness never gets in. What the
kernel cannot see is a statement weaker than intended. Measured: spelling the
primality bound `1 ≤ p` instead of `2 ≤ p` still type-checks, still admits, and
passes every pre-existing test including axiom-freedom and the determinism
count — and is satisfied by `p = 1`. That mutation was run and killed **exactly
one** test, the new one, which compares the admitted type against an
independently built term. The fact's `kernel-term` checker greps the whole
rendered type for the same reason; a name-only grep survives the mutation.

**Next.** Close `F:nat-exists-prime-gt`. Two small steps remain, both resting
only on already-admitted axiom-free lemmas: (1) `1 ≤ Nat.factorial n` (induction,
`one_le_mul` at the successor), which is what makes `2 ≤ 1 + n!` and so lets
`exists_prime_dvd` apply to it at all; (2) the assembly — take `p` prime with
`p ∣ 1 + n!`; if `p ≤ n` then `dvd_factorial_of_le` gives `p ∣ n!`, `add_comm`
reshapes the sum, `dvd_add_right_cancel_of_pos` yields `p ∣ 1`, and
`not_dvd_one_of_two_le` refutes it; `le_total` then leaves `n ≤ p` and
`lt_or_eq_of_le` sharpens it to `n < p`.

**ℕ-induction is in dispatch; the front door now decides 4 of the 12 corpus
instances where it decided 1** (`WIP`, induction-dispatch, 2026-08-17).
`prove_by_nat_induction` had been built, exported, and deliberately kept out of
`solve` because it applied ℕ-induction to goals quantified over all of `Int` and
answered `unsat` for satisfiable sets. `a32280b6a` made a recognised `n >= 0`
guard mandatory; this lane re-measured that fix, attacked it, and wired the route
in as the last rung of the quantified ladder.

Re-measurement of `corpus/regression/uflia_induction` (12 instances): the three
`unguarded_*` rows are declines and the four unique `unsat` decisions survive —
**0 status contradictions, down from 3**. The route decides `guarded_linear_
closed_form`, `guarded_linear_nonneg`, `guarded_monotone_step` and
`guarded_parity_range`; the two nonlinear-step instances (`guarded_sum_gauss`,
`guarded_product_factorial_bound`) still overrun.

**No wrong `unsat` was found, and one crash was.** The new
`tests/nat_induction_adversarial.rs` carries 22 shapes chosen because a plausible
recogniser gets them wrong, each with a hand-derived truth and its witness — a
`<= n 0` guard, `>= 0 n`, `>= n (- 5)`, `>= (+ n 1) 0`, a guard on a *different*
variable, a vacuous `true` guard, a disjunctive guard admitting `-1`, nested
binders, a conclusion carrying its own quantifier, binders shadowing free
symbols, nested and n-ary implications, three multi-goal orderings. Every one
declines, on the route alone and through the front door. The defect that surfaced
was arity, not soundness: `is_nonneg_guard` bound `(args[0], args[1])` before
matching the operator, so a one-argument guard (`(=> (not (= n 5)) …)`, legal
SMT-LIB) panicked — unreachable while the route sat outside dispatch, a
front-door crash the moment it did not.

Detail moved to [`../notes/51-induction-dispatch.md`](docs/plan/notes/51-induction-dispatch.md).

**`string` is axiom-free (`DONE`, agent-strings, 2026-08-17).** The last
prelude assumption outside `real` is retired: `axeyum.string.<n>.append` was a
`Declaration::Axiom` and is now a checked structural recursion over `Str.rec`,
with `nil_append` / `cons_append` / `append_nil` / `append_assoc` admitted as
`Declaration::Theorem`s the kernel re-checks (ADR-0513). Measured, not read off
the diff: `nat_axiom_inventory` reports `string: axiom=0 opaque=0 quotient=0`,
and the derived ledger is `total=30 | real=30 | everything else 0`. Verified
outside this kernel as well — a real `lean` 4.34.0-rc1 accepts the exported
module and its `#print axioms` lists only the problem's own opaque words.

The whole trusted surface of this project is now the `real` prelude (30 rows,
being constructed under ADR-0512 by another lane).

Next for this lane: length (`str.len : Str → Nat`) and the cancellation lemmas,
which are what the monoid laws were the prerequisite for — a word-level
refutation that reasons by length rather than by first clash. `word_reconstruct`
still only needs `append` as a function symbol, so nothing consumes the new laws
yet; that is the gap to close.

Not done, and deliberately: the `real` rows are a different case (their carrier
is genuinely opaque), and `nat_axiom_inventory`'s doc header still cites a stale
`integer=1` — owned by another lane.

**The ℕ side is closed; the ℤ side is half-closed, and the half that is missing
is named (`DONE`/`PARTIAL`, agent-characterization, 2026-08-17).** The gap was
real: `nat_axiom_inventory` reports `nat: axiom=0` and `integer: axiom=0`, and
neither number says the objects are the standard ones. A `Nat` with a subtly
wrong order reports the same zero, and rendered Lean modules run in `prelude`
mode re-declaring their own `Nat`/`Int`/`Eq`/`False`, so official Lean accepting
one certifies "typechecks against THESE definitions", not that they are the
usual ones.

Closed by proof rather than by inspection, in `crates/axeyum-lean-kernel/src/characterization/`:

- **ℕ is pinned.** The three Peano axioms (`Nat.Peano.zero_ne_succ` was
  genuinely absent — the prelude's own docs said successor/zero discrimination
  was not there), the universal property (`iter` + `iter_zero`/`iter_succ`
  definitionally + `iter_unique`), and `Nat.Peano.categorical`: **every**
  structure `(N, z, s)` satisfying the Peano axioms is in structure-preserving
  bijection with ours, universe-polymorphically. That is second-order
  categoricity stated inside the kernel, and it is strictly stronger than a
  bridge lemma to one other definition of ℕ.
- **ℤ is pinned as a *theory*, not up to isomorphism.** No junk (`cases`,
  `of_nat_or_neg`), generation by `1` (`induction` on `±1` — what lexicographic
  `ℤ[x]` fails), discreteness at **every** point (`discrete_everywhere`, derived
  by translating `(a, a+1)` down to `(0,1)` — what `ℚ` fails), `le_total`,
  `zero_ne_one`, and the **uniqueness** half of the universal property
  (`rec_unique`). The existence half — a map `Int → R` built from an arbitrary
  target's own data — is not proved, so "these properties determine `Int`" is
  **not** claimed.

Detail moved to [`../notes/53-nat-int-characterization.md`](docs/plan/notes/53-nat-int-characterization.md).

**The real-Lean gate now names its checker, and there is only one rule for
picking it (`DONE`, agent-lean-toolchain, 2026-08-17).** Two Lean toolchains are
installed on this box (4.30.0, the pin, and 4.34.0-rc1) and **two discovery
implementations disagreed about which to use**: `scripts/check-lean-gate.sh`
tried `command -v lean` and found elan's default, while `lean_probe.rs` sorted
elan's toolchain directories newest-name-first and took the release candidate.
Under 4.34, 21 of 77 `lean_crosscheck` families were rejected and
`scripts/lean/replay-lean4export.lean` did not elaborate at all — so the gate's
verdict depended on which toolchain happened to be installed and on which entry
point ran, and nothing in the output said which one produced it.
[ADR-0514](docs/research/09-decisions/adr-0514-the-pinned-lean-toolchain-is-the-one-that-runs.md)
decides **the pin runs**: `lean-toolchain` is the single source, `PATH` and other
elan toolchains are candidates only if `--version` matches it, there is no
"newest wins" step, and a non-pinned toolchain is a refusal naming both versions
rather than a substitution. Not newest, because
`real_lean_strict_positivity_crosscheck` asserts an exact commit and
`real_lean_wire_differential` is a differential against the reference
implementation; "whatever was installed" makes both meaningless.

Every suite now prints `AXEYUM-LEAN-TOOLCHAIN … bin=… version=… matches_pin=…`
and the gate **fails** if any suite reports a different binary than it resolved,
or reports none — a result that does not name its checker is not evidence.
Measured after the change: 17 suites, 57 tests, **223 real-Lean checks** (floor
208), 37 theory families (floor 37), every suite confirming the same binary.

Detail moved to [`../notes/54-lean-toolchain.md`](docs/plan/notes/54-lean-toolchain.md).

**ℤ is now pinned up to bijection, and the limit of that is stated rather than
blurred (`DONE`, agent-int-categoricity, 2026-08-18).** Lane
`agent-characterization` closed ℕ and named its own gap exactly: for ℤ only the
**uniqueness** half of the universal property was proved, so those properties
were proved to *hold* of `Int` and not to *determine* it. `rec_unique` was
uniqueness of a map nobody had constructed.

Built in `crates/axeyum-lean-kernel/src/characterization/int_categoricity.rs`,
declaring into the existing `Int.Characterization` namespace:

Detail moved to [`../notes/55-int-categoricity.md`](docs/plan/notes/55-int-categoricity.md).

**ADR-0512 phase R3 has landed: the ring interface takes equality as a
parameter, 30 → 39, and instantiating it back at `Eq` reproduces today's
statement node for node (`WIP`, agent-r3-telescope, 2026-08-18).**
`LraReconstructCtx::enable_setoid_equality` declares nine equality-interface
axioms (`eq`, `eq_refl`/`eq_symm`/`eq_trans`, and `add`/`mul`/`neg`/`le`/`lt`
congruence) plus the nine `Eq`-stated `Real` laws **restated through them** —
whose types are computed from the environment by rewriting the partial
application `Eq Real` to `eq`, never written out, so a changed law changes its
restatement rather than silently disagreeing with it. Every equality step in the
LRA/SOS reconstruction then routes through the slot, and
`RingTelescope::SetoidInterface` binds 39. All five fixtures of
`cargo run -q -p axeyum-solver --features full --example ordered_ring_refutation
-- --require-empty`: **39 binders, footprint 0, zero kernel-`Eq` constants left
in the proof term, 30 of 30 non-slot binder types reproduced exactly.**
`farkas_over_the_integers` (9 tests) is untouched — the `Eq` route is the
default and is unchanged.

**Why the five congruences are exactly five is a measurement, not a taste.**
Every `Eq.rec` in the whole arithmetic reconstruction sits inside one of eleven
helpers, and those eleven collapse onto symmetry, transitivity, `add`- and
`mul`-congruence (each left and right), `neg`-congruence, and the `le`/`lt`
casts (each left and right). One-sided congruence is the two-sided law with
`eq_refl` on the argument that does not move, so the two-sided form is what gets
bound. Nothing else in the LRA or SOS routes touches `Eq` at the carrier.

Detail moved to [`../notes/56-r3-telescope.md`](docs/plan/notes/56-r3-telescope.md).

**The `Sos` route stopped attesting and started reconstructing: nine
content-free skeletons and one declined module became ten *bound* ones
(`WIP`, agent-sos-normalizer, 2026-08-18).** Gate line
`python3 scripts/check-lra-hypothesis-binding.py`:

    before  instances=125 | structural=95 | attested=28 | failures=0
    after   instances=135 | structural=95 | attested=19 | failures=0

with `hypotheses` 288 → 298, `mutants_caught` 1210 → 1259, `mutants_accepted`
unchanged at 427, `represented_assertions` 286 → 296.

**The whole gap was one predicate, and it was never mathematical.** A degree-2
SOS certificate's Gram matrix is `(n+1)×(n+1)` over the *homogenized*
`v = [x₀ … x_{n−1}; 1]`, so `p(x) = vᵀMv` and `M = LDLᵀ` gives
`p = Σₖ dₖ·(Σᵢ L[i][k]·vᵢ)²` — in which the last coordinate is the constant `1`.
`SosCertificate::rational_squares` nevertheless declined any column with
`L[n][k] ≠ 0`, and the comment said why: the reconstructor's linear-form builder
could emit variables and nothing else. Every corpus row that needs a constant
term — `Σ xᵢ² + 1 < 0` (k01…k08) and `(x−1)² + (y−2)² + 1 < 0` — fell through to
a `prop._0` wrapper that renders `axiom P; axiom Not P` and says nothing about
the query. `rational_affine_squares` returns the affine entry under the index
`n_vars`; `int_affine_lin_to_rexpr` maps that index to the ring's `one`; the
degree-2 ring normalizer has had `Mono::Const` all along. The kernel still
re-proves `M·p = Σ (M·wₖ)(ℓₖ⁺)²` and declines on a canonical-generator mismatch,
so a wrong index convention would decline rather than fabricate.

Detail moved to [`../notes/57-sos-normalizer.md`](docs/plan/notes/57-sos-normalizer.md).

**Round 3: a fourth kernel-vs-Lean defect found and fixed, and the corpus
widened from 51 families to 66 over a development that finally carries the
constructs the kernel works hardest on (`DONE`, agent-kernel-adversary-2,
2026-08-18).** Rounds 1 and 2 damaged a `Prop`-only development, so 51 families
were rewiring the same handful of record shapes. Round 3 put a Type-valued
STRUCTURE (with a theorem provable only by structure eta), a `Nat` LITERAL (with
a theorem provable only by literal/constructor conversion), an INDEXED family, a
PARAMETERIZED recursive family, a MUTUAL group, an `axiom`, an `opaque` and the
`abbrev`/`opaque` reducibility hints on the wire, and added 15 families for
fields nothing had ever damaged: `levelParams` and `all` on families,
constructors and recursors; universe-parameter PERMUTATION at the binding site
and at the `Const` reference; a short universe-argument list; ι-rule right-hand
sides exchanged between rules of one recursor, and the rules permuted.

Detail moved to [`../notes/58-kernel-adversary.md`](docs/plan/notes/58-kernel-adversary.md).

**ADR-0512 phase R4 has landed: the `Real` axiom package is modelled by the
CONSTRUCTED reals, and ADR-0456's "`Int` is not ℝ" caveat is discharged
(`WIP`, agent-r4-model, 2026-08-18).** `build_creal_model_of_arith` admits one
theorem per law,

```text
Real.CRealModel.<law> : ⟦ type of Real.<law> ⟧ := CReal.<law>
```

with `⟦·⟧` **computed from the axiom as it stands in the environment** —
`arith_model`'s discipline — so an axiom whose statement changes changes the
obligation and an axiom `CReal` does not satisfy makes the build fail rather
than dropping a row. `cargo run -q -p axeyum-lean-kernel --example
creal_model_witness`: **22/22 witnesses footprint-empty, 22/22 syntactically
the `CReal` law up to binder names, 9/22 restated over `CReal.Equiv`, 7/7
discrimination witnesses**, exit 0.

**The interpretation is not a constant renaming, and that is the whole content
of R4.** `Eq` is polymorphic and `CReal.Equiv` is not, so no map from `Eq`
alone is type-correct; what gets replaced is the *partial application*
`Eq Real`, which is exactly R3's `rewrite_eq_at_real` applied to the axioms
instead of to the telescope. The rewrite is **self-guarding**: fail to fire and
the obligation still reads `Eq CReal …` while the proof proves
`CReal.Equiv …`, so the kernel refuses it. Verified — disabling the match makes
`build_creal_model_of_arith` return `DeclarationValueMismatch` and the example
exit 101.

**9 of 22 is now measured three independent ways.** ADR-0512 Measurement 2
counted `Eq` in the axiom types; R3's η-expansion mutation isolated the same
nine as binder-type mismatches; this model reports `restated_over_equiv` from
whether the rewrite fired, and the nine names agree exactly.

Detail moved to [`../notes/59-r4-model.md`](docs/plan/notes/59-r4-model.md).

**Round 4: `restore_nested_inductive_group` now has adversarial coverage, and
the reason it did not was a defect in the instrument, not a property of Lean
(`DONE`, agent-nested-gate, 2026-08-18).** Round 3 left the fourth admission
gate uncovered and stated why: a NESTED group's *undamaged* stream failed on
`axeyum_wire_rose.rec_1`, read as "`addDeclCore` regenerates the group's own
recursor but not the auxiliary one, so every field of an auxiliary recursor is
a byte Lean never reads". Stopping there was right; the reading was wrong.

Detail moved to [`../notes/60-nested-gate.md`](docs/plan/notes/60-nested-gate.md).

**The reconstruction context's carrier is now a parameter, and the constructed
reals already satisfy it (`WIP`, agent-real-migration, 2026-08-18).**
`LraReconstructCtx` no longer holds an `ArithPrelude`; it holds a
`RingSignature` — the same 31 field names, so all 158 field reads across
`arithmetic.rs`, `ordered_ring.rs` and `setoid.rs` are unchanged — plus a
`RingEquality` saying *which relation plays the role of equality*. `new()` keeps
its contract and supplies the `Real` package's instance; `try_new()` is the same
without the panic; `with_ring_signature(kernel, sig)` is the seam: a caller
brings its own kernel and names its own carrier.

**The signature is checked, not trusted.** `RingSignature::validate_in` runs five
guards — presence of all 30; the carrier is a `Sort` and its level is *measured*;
the seven operation/relation shapes by `def_eq` against types built from the
signature's own carrier; every law inhabits `Prop`; every `Const` in a law
statement is one of the eight symbols, a propositional connective, or the
signature's declared equality. Each guard is its own function with its own
negative test. **Mutation-verified twice** (before and after the split into
per-guard functions): deleting guard 2, 3, 4 or 5 kills **exactly one** test out
of 1191 and no other; deleting guard 1 kills two, which are its two entry points
(`validate_in` directly, and through `with_ring_signature`) rather than one
shared rejection path.

**Nothing changed today, and that is measured rather than argued.**
`cargo run -q -p axeyum-solver --features full --example ordered_ring_refutation
-- --require-empty` is **byte-identical to the pre-change baseline** (`diff`, all
five fixtures: footprint 0, 39 setoid binders, 30 of 30 non-slot binder types,
0 residual kernel-`Eq` constants). `farkas_over_the_integers` 9/9,
`sos_lean_reconstruct` 14/14, `--lib --features full` 1191/1191, clippy
`-D warnings` clean, `RUSTDOCFLAGS="-D warnings" cargo doc` clean (that gate
caught three broken intra-doc links nothing else did).

Detail moved to [`../notes/61-real-migration.md`](docs/plan/notes/61-real-migration.md).

**ADR-0512 phase R4 reaches the reconstruction route: a Farkas/SOS refutation
now reconstructs over `CReal`, and the closed `False` rests on ZERO carrier
axioms (`WIP`, agent-creal-reconstruct, 2026-08-18).** R3 made equality a
parameter of the ring telescope; R4 modelled the `Real` package by `CReal`. The
gap between them was the *proof-term* route: the only way to fill the equality
slot was `enable_setoid_equality`, which **declares eighteen axioms** — nine
slot members plus the nine `Eq`-stated laws restated through them — because the
`Real` package cannot prove any of it. `LraReconstructCtx::adopt_setoid_equality`
is the other half: it takes the nine members from `CRealPrelude`, which proves
every one of them footprint-free, and reads the nine ring laws off the
signature, which under `RingEquality::Defined` already states them over
`CReal.Equiv`.

**Measured, `cargo run -q -p axeyum-solver --features full --example
ordered_ring_refutation -- --require-empty --constructed-reals`:**

| | equality slot | closed `False` footprint | of which CARRIER axioms |
|---|---|---|---|
| over `Real` | **18 axioms declared** | 32–37 | **30** |
| over `CReal` | **0 declarations added** | 2–7 | **0** |

Detail moved to [`../notes/62-creal-reconstruct.md`](docs/plan/notes/62-creal-reconstruct.md).

**The shipped front-door LRA/SOS reconstruction now runs over the CONSTRUCTED
reals, and a refutation it returns rests on ZERO carrier axioms (`WIP`,
agent-creal-default, 2026-08-18).** `PreludeKey::CReal` puts the construction in
the ADR-0464 template, removing the cost objection: `build_creal_prelude` was
**43.97 s** per call in debug and is now **0.149 s** after the first (294x;
release 4.69 s -> 0.067 s). Then `try_new_over_constructed_reals` — the
`RingSignature`/`EqualitySlot` seam plus `adopt_setoid_equality`, from
`CRealPrelude`'s own theorems at 0 declarations added — becomes what
`ProofFragment::Lra`, `DisjunctiveLra` and `Sos` dispatch to, through one
`lra_ctx()` the classifier and the renderer share.

**Measured through `prove_unsat_to_lean_module` itself**
(`examples/front_door_carrier.rs --require-axiom-free`, whose exit status depends
on the finding). Footprint / of which CARRIER: over `Real` 15/**12**, 22/**17**,
10/**8**; over `CReal` 3/**0**, 5/**0**, 2/**0** — the residue is the query's own
variables and hypotheses. The `Real` column is the in-output control; an empty
one would mean the measurement broke, and the flag fails on it.

**Real Lean accepts it, after a renderer defect the flip exposed.** The first
run failed 5 of 77 `lean_crosscheck` families with `Unknown constant
Int.natAbs`: the renderer ordered an inductive by its own type while writing its
constructors inline, and `Rat.mk` mentions a definition emitted 110 lines later.
Fixed renderer-locally — **not** in `decl_deps`, which `axiom_footprint` shares.
77 of 77 now check, 0 failed. The module declares 3/5/2 axioms against 15/22/10
over `Real`, so Lean's `#print axioms` agrees with the kernel.

**The cost is module size:** 2.4-41 kB to ~2.6 MB (66x-1069x), carrying the
whole constructed N/Z/Q/setoid development.
`nat_axiom_inventory --include-constructed` still reports `real: axiom=30`,
`creal=0`, `complex=0`: the package is unused here, not retired.
[Notes](docs/plan/notes/63-creal-default.md).

**The shipped constructed-reals module halved, with what it proves unchanged
(`WIP`, agent-module-size, 2026-08-18).** Through
`examples/front_door_carrier --require-axiom-free` (exit status depends on the
finding, and it exits 0): strict-bound **2,623,005 -> 1,304,276 B**, three-row
2,673,154 -> 1,330,091, sos-square 2,551,806 -> 1,442,247. Carrier axioms still
0/0/0 against the `Real` control's 12/17/8, and the module's `axiom` lines still
equal `Kernel::axiom_footprint` (3/5/2). `scripts/check-lean-gate.sh`: **OK, 462
real-Lean checks under the pinned Lean 4.30.0, `lean_crosscheck` 77 of 77.**

**Bullet one of the brief was already done; bullet three is the real answer.**
`write_lean_module_impl` already opens with a constant-closure walk — the
`CReal` context holds **445** declarations and the module emits **280** blocks,
so selection has no headroom. The final theorem term is 4,193 bytes, 0.16% of
the module. The size is a hash-consed DAG printed as a *tree*: `CReal.mul_assoc`
is 1,296 kernel nodes and **324,609** printed ones.

**Why the existing compact writer saved 0.6%.** `compact_share_candidates`
requires `num_loose_bvars == 0` — a top-level `def` has no binder to read a
loose variable in, and a proof body is almost entirely open terms. Landed:
scope-aware `let` sharing (`ScopeId` = a hash chain over enclosing binder
occurrences; each `let` sits at the top of the innermost body whose binders the
term reads), and the front door switched to the compact writer.

**Raw-DAG sharing is unsound, so 19x is not the ceiling — 7.7x is** (193,197
scope-correct keys against 1,488,996 printed nodes). Achieved 2.01x in bytes: a
reference is overhead against ~3.7 bytes per node, which is why scoped names are
`_sN`. Naming alone was worth more than half the saving.

**A `let` chain is nested syntax** — 2,897 bindings in one lemma blew Lean's
default `maxRecDepth` of 512, so the banner now sets 65536 (elaborator counter
only; the kernel still checks every term).

**Next: a shared prelude, worth ~500x, not more sharing.** It changes the
single-file contract four Lean suites assume and needs an `.olean` build plus
`LEAN_PATH`. ADR-sized. Detail: `docs/plan/notes/64-module-size.md`.

**No shipped route BUILDS the `Real` axiom package, and a counter says so
(`WIP`, agent-retire-real, 2026-08-18).** The ledger's 30 does not move;
ADR-0509 says why rather than working around it. What that number stood for is
now measured and gated.

**The hole found.** `a6ee37c6a` moved the front door to `CReal` and the claim
went out as axiom-free. `ProofFragment::IntFarkas` — also shipped — still built
`LraReconstructCtx::new()`, refuted over the 30, abstracted them back out and
instantiated at ℤ. Its module named no `Real` axiom and its footprint was empty,
so every footprint-shaped check passed while the route built the whole trusted
surface **twice** per query (the scan trial-builds to classify).
`front_door_carrier --require-axiom-free`, the gate for exactly this claim, has
three fixtures, all real-typed: it never reached that arm.

**Fixed by an instance already there.** `IntPrelude` carries all 30 signature
fields with every law proved, so `RingSignature: From<IntPrelude>` is the
interface at ℤ with the kernel's own `Eq` — the corner `Real` (30 axioms) and
`CReal` (defined equality) cannot occupy. All 30 integer declarations are
footprint-empty against 30 non-empty for `Real` in the same test; the four
integer tests take **1.0 s** to the `CReal` tests' **98 s**. IntFarkas refutes
directly there; Lean still accepts the module (172,934 bytes).

**Measured, not argued.** `arith_prelude_builds()` counts calls to
`build_arith_prelude`. Through `prove_unsat_to_lean_module`: **0** on `Lra`,
`Sos`, `DisjunctiveLra`, `IntFarkas`; **1** for the control in the same process.
`F:shipped-front-door-reaches-no-real-axiom`, 7 rows, each proven to fail on
mutated output first.

**Why 30 stays.** They are the digest-pinned kernel statement of the interface
three constructed carriers are checked against, and the NEGATIVE CONTROL for
every axiom-freedom measurement here — delete them and no such claim can fail.
ADR-0509 names the bounded route to declared = 0: move the specification onto
the axiom-free 30-binder telescope the abstraction already produces, then shrink
the control from 30 axioms to one.
[Notes](docs/plan/notes/64-retire-real.md).

**ADR-0510: ℚ is now a FIELD, ℝ has Bishop apartness, and the inverse's
partiality is two theorems rather than a scoping note (`WIP`,
agent-creal-field, 2026-08-18).** The prerequisite nobody had listed:
`Rat.inv` existed from the start as a definition with **no law about it**, so
the development had 22 ordered-*ring* laws and an operation named `inv`.
`Rat.mul_inv_cancel` closes that, plus five derived ordered-field lemmas. Over
ℝ: `CReal.Apart := lt x y ∨ lt y x` with four laws, `CReal.no_total_inverse`,
and `pos_of_pos_bound`/`pos_bound_of_lt` — `0 < x` and `∃ k, 1/(k+1) ≤ x` are
the **same** `Prop`, so the modulus always exists and can never be extracted.
71 `CReal` declarations; `rat` and `creal` trusted surfaces still **0**.
**`CReal.inv` itself is NOT built**; design fixed and cost measured in
[`../notes/creal-field.md`](docs/plan/notes/creal-field.md), which is also where the
next task is.

**ADR-0516: `CReal.inv` is BUILT, and `x⁻¹` denotes one real rather than one
per modulus (`WIP`, agent-creal-inv, 2026-08-18).**
`CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` — a function may
*take* a `Prop` and return a `Type`, it may only not *branch* on one, so the
**modulus** is the thing that must be data and the proof is only a proof. With
it `mul_inv_cancel` (`x · x⁻¹ ≈ 1` on the positive branch), `inv_congr` — which
quantifies over **two independent moduli**, because two callers with different
`k` for the same `x` build different sequences — and `inv_index_irrelevant`.
Congruence is *uniqueness of inverses in a commutative monoid*, not a second
estimate. **76 `CReal` declarations, trusted surface still 0**; `nat_index_symm`
is the fifth time `Rat.natDivSucc` has been kept off the antitone path. Design,
measurements and what is deliberately absent (the negative branch, `abs`,
cotransitivity): [`../notes/creal-inv.md`](docs/plan/notes/creal-inv.md).

**Both of ADR-0509's reasons for keeping the 30 axioms are discharged in
principle; the rows have not moved (`WIP`, agent-shrink-control, 2026-08-18).**
`real: axiom=30` is unchanged and I did not force it down — "what stops it"
below is the finding.

**The specification, measured rather than asserted.** ADR-0509 says the
30-binder telescope "is the interface, assuming nothing" — true only if the
telescope read off an axiom-free development says the *same* thing as the one
read off `Real`. `examples/ring_interface_pin.rs` compares them: **30 binders,
30 identical, 0 differing**, so the ledger's 30 SHA-256 type pins can be carried
by a development whose trusted surface is `0`. The gate fails on a mutated
subject: transposing `le_refl`/`le_trans` in `From<IntPrelude>` gives `28
identical, 2 differing`, exit 1 — the transposition an earlier lane found no
test could see.

**The control cannot be shrunk; it has to be inverted.** `Real` is an *opaque*
carrier, so nothing over it is definable and every law must be assumed — the
floor is the whole signature. `build_control_carrier` goes the other way: the
axiom-free `Int` development with exactly **one** deliberate axiom, typed as
`Int.lt_irrefl`, the step every Farkas chain ends on. Measured: the control run
reaches `["axeyum.control.assumed_lt_irrefl"]`, the same refutation over
untouched ℤ reaches `[]`. Three mutations, one test dead each. The control axiom
is **provably redundant** — discharged by a footprint-empty theorem in the same
environment, which `Real`'s relatively-consistent 30 are not.

**What stops the retirement, and it is not mathematics.** `build_arith_prelude`
must go before rows can retire; blocked on the three relative-consistency models
(`int`/`rat`/`creal`) re-expressed as telescope instantiations with two standing
facts riding on them, a new home for `arith_prelude_builds()`, and the ledger's
own control — its population must go `real: 30` → `control: 1` in **one**
change, since landing the control as a new row first publishes a trusted surface
of **31**. 29 `.rs` files name the package.
[Notes](docs/plan/notes/66-shrink-control.md).

**The split module layout lands, additive, and it found two theorems Lean
refuses** (`WIP`, prelude-module, 2026-08-18). Over the constructed reals a
refutation's Lean module is 1,304,276 bytes of which the theorem term is 4,193 —
0.16%. `Kernel::render_lean_prelude_module` emits the development once,
`render_lean_module_compact_importing` renders a query module that `import`s it:
**5,056 / 14,567 / 1,954 B** on the three front-door fixtures (**257x / 91x /
738x**), one 1,715,764-byte shared module byte-identical across all three.
Handed to the pinned Lean 4.30.0 it compiles in 14.4 s to a 3,786,256-byte
`.olean`, after which the query module checks in **0.102 s** and reports the
query's own three hypotheses and no carrier axiom.

The cost is stated, not hidden: the split is a **strictly weaker artefact** — a
single file needs `lean Query.lean`, this needs the prelude on `LEAN_PATH` and
`--root` is not optional. The recipe is generated by
`LeanPreludeModule::check_script` and is what the gate runs, with a
no-`LEAN_PATH` refusal so "Lean accepted it" cannot mean the import did nothing.
`prove_unsat_to_lean_module` is unchanged; `front_door_carrier
--require-axiom-free` still exits 0 and the Lean gate is **18 suites / 466
checks (floor 208 -> 212)**, `lean_crosscheck` 77 of 77.

**The finding.** Rooting the shared module at the whole carrier context emits a
file Lean REFUSES, at `CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero`,
which this kernel admits. They had never been in an emitted module — the
renderer has always emitted only the reachable slice, so 122 of the carrier's
465 declarations had never been handed to any Lean. Not a rendering artefact:
reproduced with the sharing pass off, and `maxHeartbeats 0` does not move it.
**That belongs to the constructed-real lane and is not fixed here.** The root
set is the reached union (343 of 465) instead.

ADR-0511. Detail in [`../notes/67-prelude-module.md`](docs/plan/notes/67-prelude-module.md).

**Do not flip the default: every `.lean` artefact this repository SHIPS already
elaborates clean under `theorem`** (`DONE`, theorem-opacity, 2026-08-18).
ADR-0517 measured that re-spelling proofs as `def` makes Lean's elaborator take
the whole constructed-real carrier, and left the change untaken. Built as
`Kernel::set_render_proofs_as_def` — a `Kernel` field, off by default — and
measured on the pin (Lean 4.30.0 `d024af09`): the single-file front door
(1,304,276 B) and the shared half (1,300,891 B) **both exit 0 today**, at 9.3 s
and 9.7 s; under `def` they still exit 0, at 14.9 s and 13.2 s. Only the
whole-carrier module gains — 4 refusals to none — and ADR-0511 does not ship it,
while Lean's *kernel* already accepts it in 1.4 s. So the switch costs 1.36–1.69x
elaboration and 212 lines of "this is a proof" to fix a refusal no shipped
artefact suffers. `#print axioms` reads the same either way, so soundness is not
in play; ADR-0458's honesty argument is what decides it. Decision:
[ADR-0518](docs/research/09-decisions/adr-0518-proofs-stay-spelled-theorem-and-the-def-option-is-a-measuring-instrument.md);
numbers: [notes](docs/plan/notes/68-theorem-opacity.md).

**ADR-0517's blast-radius argument was narrower than stated.** "18 real-Lean
suites read the single-file front door" — they assert on the module's ROOT
theorem, which this option deliberately leaves alone, so they are indifferent to
it. The option's boundaries are pinned by 7 tests, mutation-checked 1/1/1/1/2.

**Nothing that ships moved.** The default path is byte-identical (the carrier
renders at 2,541,928 B, ADR-0517's figure to the byte),
`front_door_carrier --require-axiom-free` still reports
`the module's axiom lines equal the kernel footprint: true`, and
`scripts/check-lean-gate.sh` is **OK at 472 real-Lean checks** (floor 218),
`lean_crosscheck` 77 of 77.

**Next**: a structurally recursive `Nat.gcd`. It closes the same elaborator gap
from the other end, with no keyword change and no elaboration cost, and it is
now the preferred route to the residue ADR-0517 named.

**ADR-0519: `CReal.max`, `CReal.min` and `CReal.abs` are BUILT, and they cost
no index shift (`WIP`, agent-creal-order, 2026-08-19).**
`max` looks like it needs a decision, and ℝ has none — but it does not have to
be *derived* from one. `Rat.le a b` **is** `Int.le (num a·den b) (num b·den a)`,
so `Rat.max` dispatches by `Int.rec` on the sign of the cross-difference, where
the sign is a **constructor**; one `Rat.max_cases` carries every lattice law and
there is exactly one `Int.rec` in the module. And `Rat.sub_max_le` — joint
one-Lipschitz-ness — means `max` does not degrade the modulus, so `CReal.max`
samples at the **same** index as its arguments: the first operation since
`CReal.neg` that costs no shift. The same lemma with the `Equiv` hypotheses in
place of the regularity facts *is* `max_congr`. `CReal.abs x := max x (neg x)`,
so it adds no sequence and no regularity obligation. **94 `CReal` declarations,
trusted surface still 0**; `Rat.abs` still does not exist. Design, the measured
mutation counts, and what is left undone with its cost:
[`../notes/creal-lattice.md`](docs/plan/notes/creal-lattice.md).

**`docs/mathematics-2026-08/` said "do not start ℝ"; ℝ and ℂ are built, and the
strand now says so without losing the argument it used to make (`WIP`,
agent-doc-mathematics, 2026-08-19).** Seven files corrected in place — old text
struck through and left visible, new text dated and sourced to a command. The
load-bearing numbers were re-measured, not copied: `nat_axiom_inventory
--include-constructed` gives `complex 0 · creal 0 · integer 0 · logic 0 · nat 0
· rat 0 · string 0 · real 30`; `creal_setoid_witness` 94 declarations;
`complex_ring_witness` 39; `nat_theorem_inventory` **139** where the strand said
106; `int_theorem_inventory` 57 derived / 0 asserted; 340 facts (120 settled),
523 ADRs.

Three corrections were not in the brief and came out of measuring. `04`'s
trusted-surface table still carried `string 1` (retired 2026-08-17, ADR-0513),
so its "total 31" is now 30 and all of it ℝ. `01`'s quoted `qf_rdl_difference`
gate transcript still shows `[Real, Real.add, …]`; the shipped `Lra` route
reconstructs over `CReal` and `front_door_carrier` measures 0 carrier axioms
against 12/17/8 for the control. And `diary-real-keystone.md`'s conclusion — *"a
Cauchy-sequence construction of ℝ … is inexpressible"* — is wrong by one word:
the *quotient* is, the construction is not, which is exactly what ADR-0512
exploited. Its two measurements were right and forced the design.

`check-links.sh` green; `check-parity-docs.py` 19 errors, none in this strand
(21 at lane start, lowered by another lane).
[Notes](docs/plan/notes/doc-mathematics.md).

**`Real` -> `AxReal` (ADR-0522 step 1) turned two green assertions red and
rotted six more no validator was looking at (`WIP`, agent-axreal, 2026-08-19).**
Trusted surface unchanged and re-measured: `complex 0 · creal 0 · integer 0 ·
logic 0 · nat 0 · rat 0 · string 0 · real 30`, rows now `AxReal.*`.

**Caught.** `CReal` contains `Real`.
`the_theory_front_door_accepts_the_farkas_route` asserted
`contains("Real.add_le_add")` against a module the shipped route emits over the
CONSTRUCTED carrier — `CReal.add_le_add` satisfied it, so it could not tell the
carriers apart. `infeasibility_farkas_lean`'s "carries ordered-field content"
scan matched `ty.contains("Real.le")`, satisfied by `CReal.le`, and that example
is the checker command of the `proved` fact
`F:schedule-critical-chain-infeasible`, whose notes had transcribed the
collision as a finding. Both now name the carrier in full and stay able to
fail. Third and fourth instances of one collision; only the first was ever
noticed, and it was worked around rather than fixed.

**Broken, and the gap that hid it.** Six evidence rows on three settled facts
are `grep -E` patterns anchored on an example's stdout. `validate-facts.py` said
`340 facts, 0 errors` throughout — it never runs a `checker_command`;
`check-fact-evidence-replay.sh` is the gate that does. One of the six asserts a count of **zero** and so survived the rename by
going vacuous. All 18 rows on the affected facts re-run clean after the fix.

**A rename is not a retirement, so the ledger got a verb for it.**
`--accept-population-change` would have dropped 30 rows to `unclassified` and
filed them as retired — a 30-row reduction that never happened.
`--accept-rename OLD=NEW` re-keys live rows, carries their classification, and
takes type and digest from the measurement: `rows=30`, `retired=35`,
`unclassified=0`. Three guards, each mutation-checked to kill one test.

**Measured.** kernel `--lib` 393; solver `--lib --features full` 1223; the
three carrier examples green with controls non-vacuous (12/17/8 carrier axioms
over `AxReal` against 0 over `CReal`); ledger `--check`, golden pins, clippy on
STABLE (609/609) and rustdoc green. **Next:** ADR-0522 step 2.
[Notes](docs/plan/notes/71-axreal.md).

**66 instances were recording the weaker of two true statements, 4 more were
recording nothing at all, and the converse number could not be read** (`WIP`,
binding-tail, 2026-08-18).

Gate line, `python3 scripts/check-lra-hypothesis-binding.py` (~35 s), before →
after:

    instances=135 | structural=95  | anchored=10 | attested=9 | failures=0
    spine_assertions=541 | represented_assertions=296

    instances=135 | structural=102 | structural_anchored=66 | anchored=73
    anchored_nodes=1098 | attested=5 | failures=0
    spine_assertions=541 | represented_assertions=296 | undecomposable_spine=0

**Nothing was weakened to get any of it.** Every number that moved moved because
a check was added or a statement that was already true started being recorded.

**1. The overlap was measured and it is the largest class.** `structural` and
`anchored` answer different questions and the manifests were mutually exclusive
*by construction*, so nobody had ever run both binders over both lists. Doing it:
63 of the 95 `structural` rows also anchor — their query asserts the disequality
outright instead of leaving it a congruence conclusion — and 3 of the 10
`anchored` rows also bind structurally, because `(ite true x y)` is a four-node
term of the file. The dual class is 66, larger than the other three together.

The real change is not the class, it is that **every pin is now two-sided**:

    structural           binds structurally, and does NOT anchor        (32)
    structural-anchored  does BOTH                                      (66)
    anchored             anchors, and does NOT bind structurally         (7)
    attested             does NEITHER                                    (5)

Detail moved to [`../notes/92-binding-tail.md`](docs/plan/notes/92-binding-tail.md).

**Ten of the thirteen bare-leaf attestations now carry a checked anchor; three
are declined with a named reason** (`WIP`, array-anchor, 2026-08-18).

Lane `agent-attestation` left 13 `ArrayAxiom`/`TermIdentity` instances whose
whole rendered module is

    axiom axeyum.reconstruct.hyp._2 : Eq.{1} α atom._0 atom._1
    axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α atom._0 atom._1)

— one assumed schema conclusion and one assumed disequality, over two bare
constants. `bind_structural` refuses them and is **right to**: an injective map
onto two of the query's symbols exists for any query with two symbols, so a
structural match there would be a check with no true instance. That refusal is
the guard, not the gap.

**The gap is the second axiom.** The module *assumes* `¬(lhs = rhs)` and nothing
in Lean checks that the query says so. Anchoring checks exactly that, and asks a
different question from the structural one — not "is this term in the file" but
**"do the file's own assertions FORCE this equality to be false, and is it the
only one they force that this module could stand for?"**

`forced_disequalities` reads the `.smt2` text and propagates a required truth
value down each `(assert …)`: through `not`/`and`/`or`/`=>`, through `distinct`,
and through the one-bit-vector encoding a BTOR-derived file writes Booleans in
(`(= #b1 t)`, `bvand`/`bvor`/`bvnot`, `(ite c #b1 #b0)`). It stops wherever the
value is not forced — an `or` under a true polarity, an `xor`, an n-ary `=` under
a false polarity, an `ite` without the Boolean branch pair — because each of
those entails a disjunction, not a fact.

**Uniqueness is what makes it an anchor rather than a formality, and it bites on
the very set it was built for: 3 of the 13 are refused.**
`solver__array__ext27.btor.smt2` forces four leaf disequalities (`i0≠i1`,
`v5≠v6`, `i0≠i2`, `i1≠i2`) and a bare module does not say which it means; the two
`unsat__replace_all__not-first-only` rows force none at all, their one assertion
being a forced-**true** equality whose sides the arena constant-folded — the same
rewrite residue as `ext10` and `redand-eliminate`. Those three stay attested.

Detail moved to [`../notes/93-array-anchor.md`](docs/plan/notes/93-array-anchor.md).

**Yes, for 95 of the 124 — it was how the emitter was written, and both the
emitter and a checker that can fail have landed** (`WIP`, attestation,
2026-08-18).

Lane `agent-binding-coverage` measured that 124 of the corpus's 270 rendered
Lean modules transcribe nothing: their entire vocabulary is
`α atom._N func._N Eq.{1} Not And`, a fresh vocabulary with no declared
relationship to any query symbol. It was right not to "cover" them. The
question this lane took is the next one: **is that abstraction necessary, or is
it how the emitter was written?** Measured per route, it is both, and the split
is sharp.

| n | route | why the module said nothing | now |
| --- | --- | --- | --- |
| 89 | `ArrayAxiom` | the emitter collapsed each whole term into ONE opaque constant | **structural**, checked |
| 6 | `QfAbv`, `QfUf` | nothing — they were structural all along, and were misfiled | **structural**, checked |
| 13 | `ArrayAxiom`, `TermIdentity` | both sides genuinely are bare query leaves | attested |
| 9 | `Sos` | the real reconstructor declined and a `prop._0` wrapper fired | attested |
| 4 | `FiniteArrayExtensionality` | the same nothing, under a conjunction | attested |
| 2 | `ArrayAxiom` | the rendered term is the output of a **rewrite** | attested |
| 1 | `ArrayAxiom` | *self-refuting* — its `False` needed no hypothesis | **declines** |

Detail moved to [`../notes/94-attestation.md`](docs/plan/notes/94-attestation.md).

**The transcription check now covers three routes, and the denominator is
measured rather than estimated** (`WIP`, binding-coverage, 2026-08-18).

Lane `agent-transcription` closed the SMT-LIB → rendered-statement gap
(trust-surface item 3, *weaker than the kernel*) for the two Farkas routes and
declined the rest. This lane widened it and, more usefully, **measured what the
rest actually is**. Swept all **1404** committed `.smt2` files: **270** render a
Lean module at all, and those 270 split exactly three ways.

| verdict | n | what it means |
| --- | --- | --- |
| **bound** | 125 | every rendered hypothesis bound back to an `(assert …)` line |
| **attested** | 124 | the module transcribes **nothing**; verified content-free |

> **SUPERSEDED 2026-08-18 by lane `agent-attestation`.** The 124 were not one
> class. Decomposed per route, **89 `ArrayAxiom` modules said nothing because of
> how the emitter was written** — `array_axiom_term_expr` collapsed each whole
> term into a single opaque constant keyed by arena index, though the certificate
> carried the query's own `TermId`s all along, and the trees are 10 nodes at the
> median. A test now pins the defect that hid behind it: read-over-write and
> select-over-ite rendered **the same module, byte for byte**. Six more
> (`QfAbv`/`QfUf`) were structural all along and merely misfiled.
>
> Current gate line: `structural=95 attested=28 attested_vacuous=0`. The
> **self-refuting** instance was a real bug — `conflicting_bool_negation_equalities`
> returned the pair `(p, p)` for `(not (not (= p (not p))))`, a *Boolean*
> conflict where no honest pair exists — and the route now declines it, which
> re-running the search could never have caught. The query is still `unsat` via
> `TermLevelEnum`, `certified=1`.
>
> `structural` is deliberately weaker than `bound`: for 89 of 105 queries no
> assertion says `¬(lhs = rhs)`, because the hypothesis is a congruence
> *conclusion*. Binding those to an assert line would be a check with no true
> instance — so they get their own verdict, and an anti-absorption guard **fails**
> if an instance pinned `attested` can be related to its query, which is exactly
> the silent lie that had already happened to those six.
| **declined** | 21 | neither — named, not pinned, not checked |

Detail moved to [`../notes/95-binding-coverage.md`](docs/plan/notes/95-binding-coverage.md).

**The weakest link in the trust chain is now gated** (`WIP`, transcription,
2026-08-17).

`docs/prover-track/research/13-residual-trust-surface.md` ranks what a third
party must believe, and puts the SMT-LIB → rendered-statement transcription at
item 3, **weaker than the kernel**: a reconstructed UNSAT declares the query's
constraints as the Lean module's own axioms and proves `False` from them, and
nothing checked that those axioms are the `.smt2` file's `(assert …)` lines. A
dropped negation would typecheck, report a clean axiom footprint, and be
worthless.

Measured first, as the note said: **nothing checked it.** The closest existing
instruments count hypotheses (`hypotheses >= assertions.len()`) or test the
declared type for the substring `Real.le`. Neither reads what a hypothesis
*says*.

`scripts/check-lra-hypothesis-binding.py` closes it for the two arithmetic
hypothesis routes. Both sides are re-parsed and re-normalized in Python —
sharing no code with each other or with `axeyum-smtlib` — because the renderer
emits `x > 5` as `-x + 5 < 0` and normalization is exactly where the bug would
hide. Every rendered hypothesis must be an atom the query **entails**, under one
injective, sort-respecting renaming; every axiom in the module must be a
carrier, a bound hypothesis, or a pinned prelude law, so `axiom smuggled : False`
cannot pass unread. **105 instances, 248 hypotheses, 0 failures** (~30s), swept
from the committed corpora rather than hand-picked.

Two things it does that the count above does not convey:

- **It corrupts the real artifacts on every run.** Each hypothesis, five ways.
  869 caught. The gate cannot pass without its detector firing — this repository
  measured 40 of 162 checker runs exiting 0 on completion alone.
- **The search is untrusted.** Its 329 *accepts* of corrupted modules are not
  misses: `x ≤ 0` shifted to `x ≤ 1` names a different genuine row, and swapping
  the sides of `x − y < 0` is faithful again under the renaming that swaps `x`
  and `y` (measured, on a real cvc5 regression file). Each accept is re-derived
  by `verify_binding`, which shares no control flow with the search. A pristine
  accept the binding cannot justify fails the run too.

Writing it found a defect in the checker's own search — it committed to the first
permutation inside a matched atom and reported a transcription defect on a
**faithful** module (`x+y=1 ∧ x=2 ∧ y=0`). Pinned as a regression.

Detail moved to [`../notes/96-transcription-binding.md`](docs/plan/notes/96-transcription-binding.md).

**Claim-dashboard gate, finding-8 re-measurement, and PLAN.md returned under its
ceiling** (`WIP`, ledger-integrity, 2026-08-16). Three defects behind a dashboard
reporting 38 claims against an actual 104; finding 8 re-measured as remediated
(177/177 checker runs can fail) after a regex audit of my own produced 19 false
positives; and `plan-authority` taken from 233,888 bytes to 46,820 by archiving
finished lanes to [`docs/plan/archive/`](docs/plan/archive/README.md). Full record:
[`diary-ledger-integrity.md`](docs/refactor-2026-08/diary-ledger-integrity.md).

**`int_prelude` is axiom-free.** `Int.euclidean_decomposition` is a theorem;
`Int: 54 derived (54 with an EMPTY axiom footprint), 0 still asserted`, trusted
surface `34 → 6 → 1 → 0`. Measured downstream under real Lean: the Diophantine
reconstructions now depend on **no library axiom at all**, and `check_one_lean`
gates that. Fourteen `kernel-lean` fact checkers were rebound from a whole-suite
run to their own theorem.

**Next.** ℚ, scoped in
[`02-the-library.md`](docs/mathematics-2026-08/02-the-library.md): build it as a
normalised structure (as Lean core itself does), not a setoid quotient. First
slice is `Int.natAbs`, then `Int.div`/`Int.mod` specified against the
freshly-proved decomposition.

**Certification is now gated on being re-derivable, not on being claimed**
(`WIP`, evidence-certification, 2026-08-17). Full record:
[`diary-evidence-certification.md`](docs/refactor-2026-08/diary-evidence-certification.md).

Detail moved to [`../notes/98-evidence-certification.md`](docs/plan/notes/98-evidence-certification.md).

**Open queue, in the order I intend to clear it** (`WIP`,
capability-assurance, 2026-08-20). Items that clear themselves are struck rather
than carried — a queue listing resolved work is the same defect as stale prose.

1. ~~`hooks/pre-push` runs `cargo test -p axeyum-lean-kernel` WHOLESALE~~ —
   **cleared 2026-08-20.** The Lean-prelude suites moved to `just check`, which
   already owned them and which gates a different property; the hook went
   **630 s → 130 s**. It also gained `cargo check --all-targets` (not
   `--workspace`, which does not compile the bench examples and let me break
   `main`) and a route-agreement step.
2. **One guard in `check-lra-hypothesis-binding.py:1244` measurably SURVIVES**
   (`bind_structural`'s opaque-sort check). Needs a control in
   `102-attestation-gap`'s test module; the mutation harness reports it rather
   than the harness having been wrong.
Items 3-4 (the 404 GB target-dir relocation, scheduled because it forces one
cold rebuild; and registering a heavy-cargo suite with the mutation harness)
are in [the lane note](docs/plan/notes/99-capability-assurance.md).

Cleared by their owners since this list was written: `103-creal-lean-divergence.md`
is under the ceiling (2,958 B), and `PLAN.md` now records the 11 -> 10 ledger
guard-count correction rather than publishing the wrong number.

Detail and older landed rows moved to [`../notes/99-capability-assurance.md`](docs/plan/notes/99-capability-assurance.md).

**`gen-adr-index.py --check-remote` detects an ADR number two checkouts both
claimed, before merge (`DONE`, agent-adr-numbering, 2026-08-18).** `--check`
only ever reads this working tree, so it could not see `origin/main` reusing
0471-0474 (fixed earlier today, `61906c585`/`cd19e54ea`) — and while building
this gate, it found the SAME defect had already recurred: 0468-0470 are ALSO
claimed twice, live, right now. `--check-remote` diffs local `adr-NNNN-*.md`
filenames against `--remote-ref`'s (default `origin/main`) tree via `git
ls-tree`; a number where each side has a file the other lacks is a collision,
reported with the exact files and the next free number.

Deliberate, documented trade: an unresolvable ref (no fetch, no `origin`)
**SKIPs, exit 0** — failing closed would redden every offline lane for a
reason no code fixes. A resolvable-but-stale ref (`.git/FETCH_HEAD` older than
`--max-staleness-hours`, default 24) downgrades a CLEAN result to ADVISORY,
still exit 0 by default (`--require-fresh` makes it exit 1) — a clean verdict
on stale data is confidently wrong, which CLAUDE.md rates worse than no check.
A COLLISION found on stale data is never forgiven by either mode.

Wired last in `just check`'s dependency list and beside `adr-index` in
`check.sh` (see comments at both sites for why "last" matters for `just`
specifically). 6 new guards, each mutation-verified to kill EXACTLY one test
(`python3 scripts/tests/mutation_controls.py adr-index` — all green).

**Left undone, on purpose:** did not renumber the live 0468-0470 collision.
Fixing it means touching ~50 files (facts, plan docs, rustdoc, `.rs` source)
the same way 471-474 was fixed, and several of those files
(`crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs` and its
tests) had another lane's uncommitted WIP in them at the time — editing them
was off-limits per CLAUDE.md's multi-agent rules. **Consequence: `just check`
and `./scripts/check.sh` are RED on this branch right now**, on the new
`adr-remote-collisions` step, for a real and correctly-reported reason. Detail
and full demo transcripts in
[`../notes/agent-adr-numbering.md`](docs/plan/notes/agent-adr-numbering.md).

**The module banner is out of the golden pins, and the golden suites have a
gate** (`WIP`, agent-golden-pins, 2026-08-18). Three commits in four days
changed the fixed banner every rendered Lean module opens with, re-pinned only
the golden that sat in a gate, and shipped the same delta red onto the rest
(`0fc7cc357`; `b760fd6ae` +863; `46724faec` +777). Two things were wrong and
both are fixed:

1. **the pins covered the banner.** `axeyum_lean_kernel::split_module_banner`
   plus `tests/support/lean_golden.rs` pin the module **body**; the helper still
   refuses a source that does not open with this kernel's banner byte for byte.
   The banner has one pin of its own, as committed text
   (`axeyum-lean-kernel --test module_banner_pin`, blessed by the same
   `AXEYUM_BLESS_LEAN_FIXTURES=1` as the 17 module fixtures). A header change
   now fails one named thing and its failure is a header diff.
2. **nothing ran the suites.** `scripts/check-lean-golden-pins.sh` **discovers**
   membership (a suite is in the gate exactly when it calls
   `assert_golden_module`) and refuses a hand-rolled whole-module `(len, fnv1a)`
   pin, so a new golden cannot be added outside the gate. Wired into `just
   check` and `scripts/check.sh` (both, keeping `check-aggregate-scope` clean)
   and diff-scoped into `hooks/pre-push` on `axeyum-lean-kernel/src/**` — the
   origin of all three recurrences.

Measured at `760befd16` in a clean lane snapshot: gate 6 suites / 33 tests, 35 s
wall warm (0 s on a push that does not touch the kernel); every pin moved by
exactly 2,122 bytes and nothing else; stable clippy, `fmt --check`,
`rustdoc -D warnings` and `check-aggregate-scope` all clean; seven guards, each
deleted in turn and each killing **exactly one** control.

Membership measured, not guessed: **five** suites, the four that failed plus
`diophantine_lean_reconstruct`. The four candidates in the brief's regex are all
false positives (`specs.len() == 720`, `== 640`, corpus population `226`,
`outer_bindings.len() == 318`) — element counts, not module bytes. Detail and
the full measurement table: [`../notes/agent-golden-pins.md`](docs/plan/notes/agent-golden-pins.md).

**Gap #1's one confirmed fix is landed, in the form its diagnosis said to ship
it in: minimisation is budget-driven, not width-gated** (`WIP`,
agent-lia-core-minimisation, 2026-08-21). `dpll_lia.rs` had one constant doing
two jobs — deciding whether a theory conflict core was minimised at all, and
deciding which cores are charged against the wide-clause retention budget. The
[diagnosis](docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
§5.2 measured what that costs: the cores too wide to minimise are exactly the
cores whose width then exhausts the retention budget, so a solve declines for
want of the narrow clauses it refused to narrow. The jobs are now separate —
`MINIMIZATION_ORACLE_CALL_BUDGET` (a deterministic **oracle-call** ration, chosen
over wall clock because determinism is a public API promise) admits the pass;
`WIDE_THEORY_CORE_ATOMS` (still 128) only decides retention accounting, by
**retained width** rather than by provenance, which keeps the memory protection
the naive constant bump gives up.

Measured on the pinned 200-file competition lists, three binaries plus z3 4.13.3
run **adjacent in time per file** so contention is shared across the arms:

| division | base | A/B (128→4 096) | **shipped** | vs z3 | vs declared `:status` |
|---|---:|---:|---:|---|---|
| **QF_UFLIA** | 92 | 112 | **114 (+22, −0)** | **0** disagreements / 114 | **0** / 114 |
| QF_IDL (control) | 66 | 66 | **65 (+0, −1)** | **0** / 63 | **0** / 65 |

Detail moved to [`../notes/agent-lia-core-minimisation.md`](docs/plan/notes/agent-lia-core-minimisation.md).

**Ranked gap #1 is diagnosed: three causes, not one, and the largest single
block of losses is a route that quits at 5 % budget use** (`WIP`,
agent-lra-diagnosis, 2026-08-21). Measured at `8426fbd2d` over the four pinned
200-file competition lists (sha256 unchanged from their `PARITY.md` entries),
axeyum + z3 4.13.3 at 24 s each, then a second pass for route ladders. cvc5 is
not installed on this host; z3 lands within 5 files of cvc5's recorded count in
every division, which is why it is used to decide which failures count.
Instrument validated by reproducing QF_LRA's recorded 86/200 exactly.

278 misses classify as: **T** budget exhausted 146, **S** admission decline on a
size constant 73, **I** incompleteness 48, **P** front-door reject 11. The
route ladders say these are **three** causes, and they do not line up with the
divisions:

- **`dl-online` runs out of clock** — 64/65 QF_IDL and 51/55 QF_RDL misses. The
  one genuinely shared cause, and it is shared by two divisions, not four.
- **the LRA route** — QF_LRA (and QF_RDL's tail): half refuse on
  `MAX_ONLINE_LRA_ATOMS = 1_024`, half time out.
- **the lazy UF/arith CEGAR** — QF_UFLIA, **82 of 82** traced misses, one route.
- plus **26 QF_UFLIA files rejected at the parser** for `Int` literals beyond
  `i128` (the Certora/EVM family, 2^256 constants). A capability zero, 13 % of
  the division, untouched by any solver work.

Two one-constant A/Bs, built in a private snapshot, positive-controlled, never
in the shared tree:

- **REFUTED** — making the LRA atom cap fall through instead of terminal
  (`lra_theory.rs:203`): **0** new decides over 71 files and **54** memory
  aborts past 12 GiB. The cap is load-bearing protection; both routes are
  inadequate above ~1,000 atoms.
- **CONFIRMED** — `MAX_MINIMIZED_THEORY_CORE_ATOMS` 128 → 4 096
  (`dpll_lia.rs:48`). QF_UFLIA **92 → 109 (+17)**, QF_IDL 65 → 64 (the one loss
  re-decides on a quieter box on **both** binaries), **0 disagreements** against
  z3 and **0** against the declared `:status`. The 48 QF_UFLIA `I1` files return
  `unknown` after a median **1.3 s of 24 s** with `core_src_minimized=0` — the
  cores too wide to minimise are exactly the cores whose width then exhausts
  `MAX_DYNAMIC_LARGE_CORE_LITERALS`.

Detail moved to [`../notes/agent-lra-diagnosis.md`](docs/plan/notes/agent-lra-diagnosis.md).

**A mutant that did not compile was scored as coverage** (`WIP`,
agent-mutation-harness, 2026-08-18). Measured against `mutation_controls.py` as
it stood: replacing `if len(unchecked) > ceiling:` with `if len(unchecked) > >
ceiling:` printed **`killed 0`** and counted the guard as tested. So did a suite
that executed zero tests — the `#![cfg(feature = "full")]` trap. Both push in the
unsafe direction, and every "exactly one test died" in this repository rests on
the mutant having been built and run.

Only `killed N` and `SURVIVED` are now measurements; `DID NOT BUILD`, `DID NOT
RUN`, `NOT APPLIED`, `AMBIGUOUS ANCHOR` and `INCONSISTENT` fail the run in a
**separately counted** bucket — "not tested" and "could not tell" have different
fixes. A build probe runs before any test count is believed; the two independent
kill counts (headers, summary) must agree with each other and the exit status;
collection size must match the baseline. A `cargo` runner covers the route the
defect was reported on.

`self-demo` produces one of each of the four outcomes from a real mutation and
fails unless the harness names all four; wired into `just check` and `check.sh`.
The harness is mutation-checked against itself (24 guards / 31 controls): first
run **21 killed, 3 SURVIVED**, all three real; now **24/24**.

Two findings in existing suites. The ambiguous-anchor check found **two dead
controls** in `lra-hypothesis-binding` (one mutating the same copy another
control already drove); repaired, 53/53. And `lean-axiom-ledger` — the control
over the axiom ledger, i.e. the axiom-freedom claim — was recorded as *11 guards,
no survivors* when it is **10**: its eleventh mutation sabotages the fixture, so
the suite ran **zero** tests and the old classifier read the non-zero exit as a
death. Removed with the reasoning in place; 10/10.

Detail: [`../notes/agent-mutation-harness.md`](docs/plan/notes/agent-mutation-harness.md).

**Both gap-analysis §7 defects closed, and both were worse than the audit
recorded them** (`DONE`, agent-resource-guards, 2026-08-21).

Detail moved to [`../notes/agent-resource-guards.md`](docs/plan/notes/agent-resource-guards.md).

**Two of the three string-length certificates now carry a Lean term real Lean 4
accepts; the third declines for two independent reasons, and the guard that was
supposed to catch the second admitted it** (`WIP`, string-recon, 2026-08-20).

`Evidence::UnsatStringLength` was rung 2 of the ladder — a certificate an
independent checker re-derives, with nothing kernel-checked behind it.
`reconstruct_string_length` builds the term for the **conjunctive** case over
the constructed integers (`try_new_over_integers`; `integer: axiom=0`), not
`AxReal` and not `CReal`: lengths and code points are integers, and `ℤ` models
every law a Farkas combination uses.

Detail moved to [`../notes/agent-string-recon.md`](docs/plan/notes/agent-string-recon.md).

**ADR-0521: ℂ is built, it is free, and its missing order is REFUTED rather than
omitted (`WIP`, agent-complex-foundation, 2026-08-18).** `Complex` — a
one-constructor pair of `CReal`s with equality the *defined* relation
`Complex.Equiv` — carries `zero`/`one`/`I`/`ofReal`, `add`/`neg`/`mul`/`conj`,
four congruence obligations, and **9 of 9** commutative-ring laws. Thirty-nine
named declarations, every axiom footprint empty, whole trusted surface **0**
(`Axiom` + `Opaque` + `Quotient`, not `Axiom` alone):
`cargo run -q -p axeyum-lean-kernel --example complex_ring_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

The other 13 of the `Real` package's 22 laws are the order laws, and they are
**not deferred**: `Complex.no_compatible_order` quantifies over both relations
and derives `False` from seven of them, with `I` as the witness through
`Complex.I_sq`. The witness also checks that `Complex.le`/`Complex.lt` are not
declared — a refutation and an omission look identical otherwise.

Next: (a) a plain-commutative-ring telescope, since ADR-0457's is parameterised
over an *ordered* ring and ℂ is not one; (b) ℚ(i) for `geometry_certify`, which
ADR-0512 deferred ℂ in favour of; (c) `CReal` completeness, which `abs`, `√` and
algebraic closure are all downstream of.

**ADR-0512 phase R2 is COMPLETE: ℝ is built, it is free, and ALL 22
ordered-commutative-ring laws hold over it (`WIP`, agent-creal-mul,
2026-08-18).** `CReal` — a Bishop setoid of regular ℚ-sequences — with `Equiv`
**reflexive, symmetric and transitive**, `zero`/`one`/`neg`/`add`/`mul`, all
five congruence obligations, the additive group, Bishop's order, the strict
order and the product. Fifty-eight declarations, every axiom footprint empty,
whole trusted surface **0**:
`cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

Detail and older landed rows moved to [`../notes/creal.md`](docs/plan/notes/creal.md).

Detail and older landed rows moved to [`../notes/creal.md`](docs/plan/notes/creal.md).

**R3 done; the census is an artifact now, and `17` was not one** (`WIP`,
math-r3, 2026-08-17). The 2026-08-13 misconception audit's `census.tsv` was
never committed, so its headline "17 out of fragment" reached both
[`04`](docs/mathematics-2026-08/04-reachability.md) and
[`05`](docs/mathematics-2026-08/05-the-mathematics-dag.md) with nothing behind
it. Re-derived against the sibling `math-education` graph at `ce3e2a5`
(unchanged since, so this is not drift): **85 / 16 / 46**, not 86 / 17 / 44.
One of the 17 was a *distractor form inside* a file counted as a separate
corpus row; one genuine out-of-fragment row (`infinity-minus-infinity-is-zero`)
was missing; one (`angle-size-depends-on-arm-length`) reduces to a polynomial
identity and is moved to A, marked CONTESTED rather than asserted. Also: the
graph carries **1,567** concepts, not 1,566 — a locale collation artefact
(`sort -u` folds `C:trend-line` and `C:trendline`; `LC_ALL=C` does not).

**The adversarial corpus ranks something else first.** Censused the graph's 42
`techniques` — proof *shapes*, not propositions: 11 reachable, 19 out of
fragment, 12 heuristics (exactly the 12 the corpus itself marks
`epistemic_status: empirical`). **16 of the 19 want one thing: induction over ℕ
as a discharged schema**, against 7 for limits. Induction is the one entry on
the ranked list that is not a missing logic — the kernel has an inductive `Nat`
with an ι-computing `Nat.rec`, while the curriculum map records the `induction`
node's fragment as `LIA / BV (base + step instances)`: instances, not the
schema. So the largest single item the mathematics asks for is automating an
arrow the flywheel already has, not adding a theory.

**Next.** The obvious slice is the one the ranking names: a goal → induction
schema → reconstructed kernel term route, tested first on the technique rows
that are pure ℕ schemas (`telescoping`, `parity-argument`, `pigeonhole` at
fixed hole count). Second, the census wants a third corpus — its two are both
school-and-olympiad, adversarial along the *shape* axis but not the
*difficulty* axis.

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](docs/python-2026-08/README.md). Plans 01-03 and the
quality goal (`10-quality-best-practices.md`) are complete on `main`. Q1-Q8
landed: property-based + Rust-side tests + a `ty` ratchet (Q1, which found a
replay that certified an empty assertion stack); the zero-copy audit and
`solve_smtlib_with_model` ending the double solve (Q2); release wheels with a
3.14t build and a smoke-install gate (Q3); the eight open tier-R rows (Q4);
typed stubs from the Rust signatures via pyo3-stub-gen at 96.9%, stubtest and
an `Any` ratchet (Q5); the CAS long tail -- ntheory / combinatorics / stats /
special / transforms / normal forms / moment provers / ansatz / gf / boolean /
algebraic, 179 items tested against sympy as oracle, three disagreements
argued and pinned (Q8, coverage 302 -> 471); panic-surface hardening -- a
probe took reachable panics 3 -> 0 and crashes 19 -> 2, the rest typed at the
boundary (Q7). Plus `axeyum.m` (Mathematica-shaped verbs) and a runnable
`python/examples/gallery.py`. Coverage `tier_r_unreferenced=0`.

Both prior follow-ups are now closed: the AGENT/knowledge fact-fixture drift
was refreshed (targets moved to `nat-modeq-symm/trans` and a nursery-derived
mobility count), and the deep-`Clone`/`Drop` segfault is guarded at the
boundary by a `MAX_EXPR_DEPTH` iterative-depth check that raises
`BudgetExceeded` (an iterative Clone in `axeyum-cas` remains the deeper fix).

**Frontier reachability (2026-08-25).** Answered "why does the agent attempt
~3 of 146 open facts?" — decomposed into reachability x provability
([`14-frontier-reachability.md`](docs/python-2026-08/14-frontier-reachability.md)).
Built `scripts/gen-statement-adapters.py`: generates proof-free Lean statement
adapters from each fact's `formal.statement` so `lean4export` can freeze them
(the only artifact a tier-C producer consumes). Verified end to end on s5
(24 adapters, one `lake env lean` compile, arrow-free ones export to valid
~320KB NDJSON that `import_statement_ndjson` accepts). Measured finding: the
"3" is producer-bound, not export-bound — the refl/symm/trans/comm shapes the
producers close are already proved (498 proved), and every arrow-free *open*
modeq fact is a congruence goal both producers decline. lean4export 3.1.0
silently refuses arrow-bearing statements (exit 1), capping auto-export at
arrow-free shapes. Next: Q6 (derive `eq`/`hash`/`str`; `Config`/`Incremental`
`Sync`); a `ModEq`-unfolding producer to lift the *provability* wall; an
arrow-capable export path.

**Agentic-loop iterations (2026-08-25).** Ran the loop live and improved it
three times: (3) `--skip-unreachable` preflights the frozen export before
spending a model — observed offline over 5 facts, all declined retrieval-miss
after ~26k tokens each because export absence is only found inside the producer
tool, two model rounds in; (4) `--reachable-first` stably reorders `--next`
selection so facts with an export come first (the first 5 eligible had 0); (5)
the mobility summary now names the dominant unevaluable reason, making
`unevaluable=186` legible as a reachability block (`no-frozen-export`), not a
tactic gap. Verified the loop still proves its live frontier (`nat-modeq-symm`,
`nat-modeq-trans`) via `modeq_family`.

**ℝ has a route and it is free (`DONE`, agent-reals-design, 2026-08-17).**
[ADR-0512](docs/research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
decides **a Bishop setoid of regular ℚ-sequences** — no quotient, no cuts.
ADR-0456's two rejections were both correct and its conclusion did not follow:
equality does not have to be `Eq`. Measured, not argued —
`cargo run -q -p axeyum-lean-kernel --example creal_shape_probe` admits the
carrier, its recursor, the representative projection (large elimination) and the
setoid relation over the *constructed* `Rat` with a **trusted surface of 0**, and
a `funext` negative control in a second kernel returns a non-empty footprint so
the zero is discriminating. The price is counted too: **9 of 30** `Real`
declarations mention `Eq`, so 13 of the 22 laws are discharged verbatim and 9
only in `Equiv` form — the order fragment Farkas actually uses is untouched.
Adding `Quot.sound` instead would read `real: axiom=0 quotient=5` and put
`[Quot.sound]` in every real footprint permanently; Dedekind costs two trusted
items, not fewer.

**One correction worth propagating beyond this lane:** the widely-repeated claim
that Coq's standard library *axiomatizes* ℝ with ~17 axioms has been false since
Coq 8.11 (Jan 2020) — `Raxioms.v` declares zero, all 17 are `Lemma`s. I wrote it
into the ADR from memory and an independent survey caught it. What is actually
there is `ConstructiveCauchyReals`: Cauchy sequences with a fixed explicit
modulus, no quotient, axiom-free, computing — i.e. this ADR's route, arrived at
independently. Corrected in place with a dated note. If you cite Coq's reals
anywhere, pin the version.

Detail moved to [`../notes/reals-design.md`](docs/plan/notes/reals-design.md).

### A1 and A2 — `DONE`, archived

Both completed. Moved to
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md)
so this file carries actions that are next.
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
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; all 163 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
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

- **Archived lane status** (43 lanes of the 2026-08-13→15 campaign, each with the
  next action it left behind): [`docs/plan/archive/README.md`](docs/plan/archive/README.md).
  `PLAN.md` carries only lanes with work in progress; a finished or cut-off lane
  keeps its file there verbatim and is restored by moving it back into
  `docs/plan/status/`.
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
