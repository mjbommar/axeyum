# BatSat / RustSAT removal surface — the ADR-1703 slice-2 inventory

Date: 2026-09-10
Lane: `R-B-batsat-slice2` (research only — nothing was removed)
Tree: worktree of local `main` at `f91570117`
Subject:
[ADR-1703](../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
point 6 — *"**Slice 2** removes the feature, the dependencies, and the ~70
historical documentation references. This ADR does not do that sweep."*

Slice 2 has not run. This note is the measured surface it would have to touch,
the load-bearing analysis of what the removal would cost, and a removal order.

> **Nothing in this note was removed, edited, or deprecated.** It is input to a
> retirement plan, not the retirement.

## 0. Method, and what each number would look like if it were wrong

Every count below is over **tracked** files (`git grep`), case-insensitively
matching `batsat|rustsat`. The brief's "104 files under `docs/`" was measured
before this lane merged main; the tracked count on `f91570117` is **110**.
Both numbers are right about their own tree; quote the tree with the number.

Positive controls, because an empty grep is not a negative result:

| Check | Command | Result | Control |
|---|---|---|---|
| default graph is clean | `cargo tree -e normal --workspace` | **0** batsat/rustsat lines | same command, pattern `axeyum-cnf` → **5** hits |
| no dev-dependency path | `cargo tree --workspace` (normal+build+dev) | **0** | (the tree is 215 lines) |
| the feature does pull them | `cargo tree --workspace --all-features` | `batsat v0.6.0`, `rustsat v0.7.5`, `rustsat-batsat v0.7.5` | — |

## 1. Dependencies

### Declarations

| File | Line | Content |
|---|---|---|
| `Cargo.toml` | 58 | `batsat = { version = "0.6.0" }` |
| `Cargo.toml` | 69 | `rustsat = { version = "0.7.5", default-features = false }` |
| `Cargo.toml` | 70 | `rustsat-batsat = { version = "0.7.5" }` |
| `crates/axeyum-cnf/Cargo.toml` | 24 | `batsat-reference = ["dep:batsat", "dep:rustsat", "dep:rustsat-batsat"]` |
| `crates/axeyum-cnf/Cargo.toml` | 28–30 | the three `optional = true` dependency lines |
| `crates/axeyum-solver/Cargo.toml` | 49 | `batsat-reference = ["axeyum-cnf/batsat-reference"]` (forwarding only) |
| `crates/axeyum-bench/Cargo.toml` | 33 | `batsat-reference = ["axeyum-cnf/batsat-reference"]` (forwarding only) |
| `crates/axeyum-bench/Cargo.toml` | 68 | `[[example]] gate_b_sweep`, `required-features = ["batsat-reference"]` |

**All three crates are optional, all behind `batsat-reference`, and only
`axeyum-cnf` owns the `dep:` edges.** `axeyum-solver` and `axeyum-bench`
forward the feature; neither declares batsat itself. No crate pulls one in by
another path.

### Verified with `cargo tree`, per crate

`cargo tree -e normal --workspace` resolves all 27 workspace members in one
graph; the members covered are `axeyum-aig, axeyum-arith, axeyum-bench,
axeyum-bv, axeyum-cas, axeyum-cnf, axeyum-egraph, axeyum-evm, axeyum-fp,
axeyum-ir, axeyum-lean-import, axeyum-lean-kernel, axeyum-machine,
axeyum-machine-evidence, axeyum-property, axeyum-property-macros, axeyum-py,
axeyum-query, axeyum-rewrite, axeyum-scenarios, axeyum-search, axeyum-smtlib,
axeyum-solver, axeyum-strings, axeyum-verify, axeyum-verify-macros,
axeyum-wasm`. Three feature-on spot checks were run per crate on top of that.

- default, normal edges, whole workspace: **0** matches. ADR-1703 point 4 holds.
- default, **including dev and build edges**: **0** matches. batsat is not a
  dev-dependency of anything.
- `-p axeyum-cnf --features batsat-reference`: pulls `batsat`, `rustsat`,
  `rustsat-batsat`.
- `-p axeyum-solver --features batsat-reference`: same three, through
  `axeyum-cnf`.
- `-p axeyum-bench --features batsat-reference`: same three, through
  `axeyum-cnf`.

### What removal actually deletes from the lockfile

`rustsat v0.7.5` is the heavy one. Its own subtree (from the feature-on tree of
`axeyum-cnf`): `anyhow`, `cpu-time` (→ `libc`), `itertools` (→ `either`),
`nom v7.1.3` (→ `memchr`, `minimal-lexical`), `tempfile` (→ `fastrand`,
`getrandom`, `once_cell`, `rustix`), `thiserror` (→ `thiserror-impl` →
`proc-macro2`/`quote`/`syn`). `rustsat-batsat` adds `anyhow` + `batsat`.

Which of those become *unreachable* workspace-wide once the feature goes was
**not measured** — several (`anyhow`, `thiserror`, `rustix`, `syn`) are plainly
used elsewhere. **Did not run.**

## 2. Code — 27 `.rs` files

Full per-file classification. "Live" means it compiles and runs on a default
build.

### 2a. Feature-gated implementation — 1 file, 306 lines

| File | Gate | Note |
|---|---|---|
| `crates/axeyum-cnf/src/batsat_reference.rs` | whole module, via `#[cfg(feature = "batsat-reference")] pub mod` at `lib.rs:44` | The entire adapter: `RustSatBatsatSolver`, `solve_with_rustsat_batsat{,_timeout,_limits}`, `BatSatDeterminism`, `rustsat_batsat_determinism`, the callback/limit plumbing. Deleting the feature deletes this file whole. |

### 2b. Feature-gated items inside otherwise-live files — 2 files

| File | Gated items | Live mentions |
|---|---|---|
| `crates/axeyum-cnf/src/lib.rs` | `mod batsat_reference` (44–45), the 6-name `pub use` re-export (88–91), a `use` in `mod tests` (4947), **4 gated unit tests** (6094, 6116, 6126, 6151) | lines 5 and 574 are **doc comments** — see 2f |
| `crates/axeyum-cnf/src/proof_sat.rs` | a `use` in `mod tests` (5013), **5 gated unit tests** (5697, 5944, 6004, 6065, 6957) | 10 doc-comment mentions — 1 is a slice-2 note (13), 9 are design-lineage credit — see 2g |

Gated unit tests total: **9** (4 + 5).

### 2c. Whole-file feature-gated suites — 3 files

| File | Gate | Tests | Role |
|---|---|---|---|
| `crates/axeyum-cnf/tests/native_vs_batsat_differential.rs` (245 ln) | `#![cfg(feature = "batsat-reference")]` :42 | **3** | The one differential ADR-1703 point 5 sanctions. |
| `crates/axeyum-solver/tests/native_cdcl_baseline.rs` (233 ln) | `#![cfg(all(feature = "full", feature = "batsat-reference"))]` :28 | 1 | **MEASUREMENT harness**, not a soundness net — prints a native/batsat wall-clock gap table. Its own header says so. |
| `crates/axeyum-solver/tests/xor_cdcl_curated_measure.rs` (262 ln) | `#![cfg(all(feature = "full", feature = "batsat-reference"))]` :23 | 1 | **MEASUREMENT harness** — CDCL(XOR) vs batsat on curated multipliers. |

Integration tests behind the feature total: **5**.

### 2d. Feature-gated example targets — 2 files

| File | Gate | Role |
|---|---|---|
| `crates/axeyum-bench/examples/gate_b_sweep.rs` (402 ln) | `required-features` in `Cargo.toml` | The tool that produced `bench-results/sat-core-gate-b-20260905/` — the four-engine gate-(b) artifact ADR-1703 rests on. |
| `crates/axeyum-bench/examples/cnf_core_bench.rs` (220 ln) | inline `#[cfg]` at 13, 24, 170, 193 | The `batsat` column of its JSON rows is absent without the feature, not silently zero. |

### 2e. LIVE code, stale naming only — 6 files

These already call the native core. Only identifiers, strings and comments say
"batsat". **They are not blockers for removing the feature**; they are
mislabelled artifacts and misleading test names.

| File | What is stale |
|---|---|
| `crates/axeyum-cnf/src/xor_cdcl.rs` | `fn learning_required_matches_batsat_on_chain` (1270), `fn differential_vs_batsat_random` (1434), `.expect("batsat solve")` ×3, `"batsat must agree PHP(7) is UNSAT"` (1332), a comment crediting "the `batsat-reference` yardstick adapter" (1316). All three call `solve_with_native_core_timeout`. |
| `crates/axeyum-cnf/src/xor_dpll.rs` | `fn differential_vs_batsat_random` (621), `.expect("batsat solve must not error…")`, panic text `batsat={theirs:?}`. Calls `solve_with_native_core_timeout`. |
| `crates/axeyum-bench/examples/cnf_stream_bench.rs` | Module doc "through persistent `BatSat` and Z3" (1); `struct BatState` (42); **the emitted JSON key is literally `"batsat"` (352)** and the mismatch message prints `BatSat=` (339). It runs `IncrementalSat`, which ADR-1703 re-based on the native core. **Every artifact this example has written since 2026-09-05 labels native-core numbers `batsat`.** |
| `crates/axeyum-search/examples/akb2_frontier.rs` | Module doc "runs the pure-Rust rustsat-batsat adapter (ADR-0007)" (16), comment "batsat is a searcher" (398), `.expect("batsat")` (422). Calls `solve_with_native_core_timeout`. |
| `crates/axeyum-solver/tests/xor_cdcl_fallback.rs` | Four comments and one assert message that say "batsat decides" / "the batsat solve returns `unknown`" (3, 44, 61, 66, 90, 99). The path is the native core. |
| `crates/axeyum-py/src/solver/core.rs` | The `unsendable` justification at 647: "the warm solver embeds a BatSat solver whose callback structs hold `Cell`s, so it is `Send` but `!Sync`." `IncrementalBvSolver` no longer embeds BatSat. Whether `unsendable` is still *required* was **not determined** — a `Send`/`Sync` assertion was not run. |

### 2f. Doc comments that are now WRONG — 4 sites in 4 files

These would mislead a reader of the source today.

| File:line | Text |
|---|---|
| `crates/axeyum-cnf/src/lib.rs:5` | "The `BatSat` adapter's proofless UNSAT is lower assurance." — the crate-level doc. ADR-1703 §"What this changes about assurance" says this boundary **disappears rather than moves**; this sentence is the one it quotes as the thing that stops being true. |
| `crates/axeyum-solver/src/sat_bv_backend.rs:4` | "…encoded to CNF, **solved through the pure-Rust `BatSat` adapter**, lifted back into an Axeyum model" — the module doc of the default QF_BV backend. |
| `crates/axeyum-solver/tests/sat_bv.rs:4` | "…**solve through the pure Rust `BatSat` adapter**, lift a model, and…" — same claim, the suite's module doc. |
| `crates/axeyum-solver/src/backend.rs:560` | "Enables the CDCL(XOR) search fallback on `unknown` **batsat** results" — the doc for `xor_cdcl_fallback`; the trigger is now an `unknown` from the native core. |

### 2g. Design-lineage credit — KEEP — 6 files

`MiniSat`/`BatSat` named as the *source of a design*, not as an engine we run.
Legitimate attribution; removing it would falsify provenance.

- `crates/axeyum-cnf/src/proof_sat.rs`: 1207, 1623, 1929, 3816, 3820, 4045,
  4278, 4309, 4330 (blocking-literal watch lists, packed clause headers,
  `propagate`'s i/j compaction, `ccmin_mode = 2`, `lit_redundant`, the default
  phase).
- `crates/axeyum-solver/src/cdclt.rs`: 238, 253, 1103.
- `crates/axeyum-solver/src/lra_online.rs`: 2611 (progress saving).
- `crates/axeyum-bench/examples/dump_dimacs.rs:34`,
  `crates/axeyum-bench/examples/pbls_probe.rs:3`,
  `crates/axeyum-bench/examples/xor_cdcl_probe.rs:3`: past-tense prose about
  what batsat timed or missed.

### 2h. Deliberate historical narration — KEEP — 4 files

Removing "batsat" from these would delete the *reason* the surrounding code
exists.

| File | Why it must stay |
|---|---|
| `crates/axeyum-solver/src/config_registry.rs` (214–232, 3215, 3879, 3939) | BatSat is the **founding case** of the admission-limit basis doctrine: a `Basis::LiveSymbol` naming `batsat` would stay true forever behind an optional dependency while "BatSat is what runs" became false. `scripts/check-admission-limit-basis.py` exists because of this. |
| `crates/axeyum-solver/src/dpll_lia.rs` (75, 79, 82, 174, 777, 2963, 5075, 5077, 5116) | The re-derivation record for `MAX_PRE_SAT_ARITH_ATOMS`: the old justification blamed BatSat's allocator, ADR-1703 invalidated it, the limit was re-measured against the native core and widened 1,280 → 10,240. |
| `crates/axeyum-solver/src/evidence.rs:162` | "where it used to read `rustsat-batsat`" — explicitly past tense, records a field's history. |
| `crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs:41` | An ADR-1703 link reference. |

### 2i. `SolverConfig::native_cdcl` — the "no-op"

ADR-1703 point 3 says it "becomes a no-op retained for API compatibility and is
documented as deprecated". **Two of those three are true. It is not a no-op.**

- **Documented deprecated: yes.** `crates/axeyum-solver/src/backend.rs:248–260`
  carries "**Deprecated no-op, kept for API compatibility (ADR-1703).**" and
  states "It is read by nobody: `SatBvBackend` dispatches to the native core
  unconditionally." `with_native_cdcl` at `backend.rs:584–589` repeats it.
  `crates/axeyum-solver/src/sat_bv_backend.rs:2287` says "`config.native_cdcl`
  is a retired no-op".
- **A no-op for SAT dispatch: yes.** `sat_bv_backend.rs::primary_sat_search`
  (2298–2316) calls `solve_with_native_cdcl(...)` unconditionally and never
  reads `config.native_cdcl`.
- **"Read by nobody" is false. Three live readers:**

  1. `crates/axeyum-solver/src/solver.rs:1090` and `:1107` —
     `warm_config_is_honored` destructures `native_cdcl` and requires
     `native_cdcl == defaults.native_cdcl`. Setting the retired flag therefore
     **disqualifies a query from the warm/incremental engine** and silently
     routes it down the cold path. That is a real behavioural difference
     produced by a flag documented as changing nothing. The predicate's own doc
     says it exists to refuse the warm route when a lever the warm engine
     ignores is set — the right rule when the flag selected an engine, a live
     trap now that it selects nothing.
  2. `crates/axeyum-bench/src/main.rs:673` — `args.native_cdcl` being set makes
     `--certify-end-to-end-unsat` **fail with an error** ("requires the raw
     full-query path … no … native-CDCL override"). A no-op flag can still fail
     a bench run.
  3. `crates/axeyum-bench/src/main.rs:7306` — it is fed into the artifact
     **config hash**, and `:6513` records it in the emitted JSON. Two runs
     differing only in a no-op flag get different artifact identities.

- Other surface naming the field: `crates/axeyum-py/src/solver/results.rs`
  (109, 130, 160 — a live Python keyword argument),
  `crates/axeyum-verify/tests/tock_log2_external.rs:94`,
  `scripts/prove-tock-log2.py:74`, `scripts/analyze-qfbv-faithfulness.py:101`,
  `scripts/tests/test_analyze_qfbv_faithfulness.py:60`,
  `artifacts/python-coverage-v1.json:3487`, and **136 recorded
  `bench-results/` artifacts** carrying `"native_cdcl": false`.
- `scripts/check-parity-docs.py:1276` **pins the string** "`config.native_cdcl`
  is a retired no-op" in `sat_bv_backend.rs`. Editing that doc line without
  touching the checker turns the gate red.

## 3. Tests and examples — genuinely differential vs. merely "a SAT verdict"

| Target | Feature-gated? | Genuinely differential? | Verdict |
|---|---|---|---|
| `axeyum-cnf/tests/native_vs_batsat_differential.rs` | yes | **yes** — native core vs. an independent third-party engine; verdict agreement + model validity | The one ADR-1703 point 5 sanctions. |
| `axeyum-cnf/src/proof_sat.rs` — 5 gated unit tests | yes | **yes** — same shape, inline: `random_cnfs_agree_with_batsat_and_self_check`, the EMA-restart family, the blocking-literal-BCP family, the `reduce_db` stress and PHP families; each `DISAGREE = 0` against batsat **plus** a DRAT check | ADR-1703 point 5 names only the integration file. These five are a second, larger, undocumented differential population — the ADR under-reports its own coverage. |
| `axeyum-cnf/src/lib.rs` — 4 gated unit tests | yes | no | Adapter-behaviour tests (raw solve + replay, pinned determinism defaults, the resource-limit `unknown`, the lower-assurance UNSAT stamp). They test **batsat**, not the native core; they die with the adapter and lose nothing. |
| `axeyum-solver/tests/native_cdcl_baseline.rs` | yes | no (measurement) | Prints a wall-clock gap table. Its own header: "MEASUREMENT harness … the soundness net is `native_vs_batsat_differential.rs`". |
| `axeyum-solver/tests/xor_cdcl_curated_measure.rs` | yes | no (measurement) | CDCL(XOR) vs batsat timings on curated multipliers. |
| `axeyum-bench/examples/gate_b_sweep.rs` | yes | measurement, with a disagreement assert | Produced the gate-(b) artifact. |
| `axeyum-bench/examples/cnf_core_bench.rs` | yes | no | Timing column only. |
| `axeyum-cnf/src/xor_cdcl.rs`, `xor_dpll.rs` | **no** | yes, but **in-house vs in-house** | Already moved to `solve_with_native_core_timeout` per ADR-1703. They still cross-check two independently written engines (CDCL(XOR) / XOR-DPLL against the native CDCL core), so they retain real value — only the names are wrong. |
| `axeyum-bench/examples/cnf_stream_bench.rs`, `axeyum-search/examples/akb2_frontier.rs`, `axeyum-solver/tests/xor_cdcl_fallback.rs` | **no** | no | Already on the native core. Names only. |

**They all moved.** No live call site still routes a verdict through the
adapter; the only executable batsat code is behind the feature.

## 4. Docs — 110 tracked files, 401 lines

Distribution (top directories): `docs/research/09-decisions` 26,
`docs/research/08-planning` 9, `docs/research/05-algorithms` 9,
`docs/solver-inventory-2026-09` 6, `docs/plan` 6,
`docs/research/11-design-review` 4, `docs/campaign-2026-08-13/agent-c-rado-akb2`
4, `docs/research/03-architecture` 3, `docs/plan/references` 3; the remaining 40
directories hold 1–2 each.

Beyond `docs/`: **137** files under `bench-results/` (recorded artifacts —
historical by construction, never edit) and **25** other tracked files
(`README.md`, `AGENTS.md`, `CLAUDE.md`, `PLAN.md`, `justfile`, `scripts/*`,
`crates/*/Cargo.toml`, `crates/axeyum-cnf/README.md`, two `artifacts/claims/`
JSONs, `references/README.md`). **300 tracked files in total.**

Per-file classification: see §6.

## 5. Gate wiring — measured

**No gate, no CI job, no `justfile` recipe and no git hook runs
`--features batsat-reference`.**

- Searching `.github/`, `scripts/`, `justfile` and `hooks/` for the feature name
  returns exactly two hits, both **prose**
  (`scripts/check-admission-limit-basis.py:14`,
  `scripts/tests/test-admission-limit-basis-control.sh:76`).
- Searching the whole tree for `native_vs_batsat_differential` outside the file
  itself returns only documentation and `PLAN.md`.
- `grep -i batsat justfile scripts/check.sh hooks/pre-push hooks/commit-msg`
  returns three hits, all comments about the admission-limit basis and DRAT
  timings. Positive control on the same command: `grep -c cargo justfile` → 145.

So the differential referee has never been on an automatic path since it landed
on 2026-09-05. It runs when a human runs it.

## 6. Docs classification — all 110 files

Every one of the 110 tracked `docs/` files was opened and its mentions read.
Three classes:

- **H — historical record, keep forever.** An ADR, a dated measurement note, a
  dated diary or campaign log, a status archive, or a captured JSON/JSONL
  evidence artifact. Rewriting it would falsify the record.
- **W — live guidance that is now wrong.** Present-tense text a reader would act
  on today that says BatSat is the default / shipping / production engine, or
  that UNSAT is proofless because of BatSat.
- **S — stale-but-harmless naming.** Ecosystem surveys of Rust SAT crates,
  design-lineage credit, reference-solver catalogues, and text that already
  states the ADR-1703 position correctly.

| Class | Files |
|---|---:|
| H — keep forever | **76** |
| W — **live and wrong** | **13** |
| S — harmless | 21 |
| total | 110 |

### The 13 that are actually wrong

This is the actionable list. Every quotation below was read directly out of the
file at the line given, not inherited from a summary.

| # | File:line | The sentence that is wrong |
|---|---|---|
| 1 | `docs/research/03-architecture/system-architecture.md:73` (also 68, 95, 102, 103) | "…lowers supported QF_BV queries through AIG and CNF, **solves with BatSat**, reconstructs Axeyum models…" — `sat_bv_backend.rs` calls `solve_with_native_cdcl`. |
| 2 | `docs/research/03-architecture/solving-strategies-and-memory-model.md:31` | Under a heading that reads "**The current architecture, as it actually is**": "`term → AIG (axeyum-bv) → CNF (axeyum-cnf) → rustsat-batsat`, then lift + **replay**." |
| 3 | `docs/research/05-algorithms/bit-blasting.md:72` (also 104, 111) | "The first SAT adapter path uses `rustsat-batsat` through RustSAT and only accepts `sat` after replay…" — presented as the path, not as history. |
| 4 | `docs/research/04-data-structures/circuits-and-cnf.md:77` (also 99) | "**The current `axeyum-cnf` slice** implements Tseitin-style encoding from AIG, DIMACS parse/write, CNF evaluation, **a `rustsat-batsat` adapter**, and replay…" — the native core is not mentioned. |
| 5 | `docs/learn/07-how-axeyum-solves-a-query.md:29, 77` | The tutorial's mermaid pipeline node is `sat["SAT core<br/>batsat / native CDCL"]`, and line 77: "The **default BatSat-backed clausal route** instead records its proof status as `Unchecked`; it must not be described as certificate-checked." |
| 6 | `docs/learn/05-models-unsat-and-unknown.md:57` | "In particular, **the default BatSat-backed clausal route** reports raw UNSAT evidence as `Unchecked`…" |
| 7 | `docs/proof-cookbook/recipes/boolean-cnf-lrat.md:40` | "This does not upgrade every CNF solver verdict: **the default proofless BatSat result** remains lower assurance." |
| 8 | `docs/user-guide/benchmarks.md:221` (also 196, 209, 213) | "…it counts deterministic `BatSat` `within_budget` progress checks **on the default path**, native proof-CDCL conflicts under `--prove-unsat`, and Z3 `rlimit` units in the oracle." |
| 9 | `docs/research/08-planning/research-questions.md:220` | "**The default BatSat adapter remains lower-assurance `Unchecked`**, and this answer does not claim every theory has an end-to-end proof." **This string is pinned by `scripts/check-parity-docs.py:1295`** — see §7.4. |
| 10 | `docs/research/08-planning/benchmarking-and-performance-methodology.md:393` (also 406, 410, 416, 664, 686) | "…this high-assurance run is kept separate from **the default batsat performance artifact** because changing the SAT engine would invalidate that comparison." |
| 11 | `docs/python-2026-08/inventories/smt-solver.md:434` (also 240, 260, 430, 431) | "`IncrementalSat` (11 methods), `IncrementalCnf` (13 methods) … **`Send` but `!Sync`** — both embed `rustsat_batsat::Solver<DeadlineCallbacks>` whose private callbacks hold `Cell<u64>`…" — `IncrementalSat`'s field is `solver: NativeIncrementalCdcl` (`lib.rs:705`). This is the same stale claim as the `unsendable` comment in `crates/axeyum-py/src/solver/core.rs:647` (§2e), and it is an *inventory* people size Python work from. |
| 12 | `docs/reference/examples.md:158` | "Replays captured append-only CNF streams **through persistent BatSat and Z3**." — it runs `IncrementalSat`, which is the native core. |
| 13 | `docs/plan/global/20-next-actions.md:485` (also 516) | A live queue entry proposing "run BatSat, the native `proof_sat` core, CaDiCaL, and Kissat on identical DIMACS… **decides whether the native core becomes the default**". That measurement was run on 2026-09-05 and the decision is ADR-1703. The entry proposes work already finished. |

Two observations about this list rather than its members:

- **Nine of the thirteen are the *same* claim** — "BatSat is what solves, so
  UNSAT is proofless" — copied into nine places (1, 2, 3, 4, 5, 6, 7, 8, 9).
  That is the sentence ADR-1703 §"What this changes about assurance" says
  disappears. Fixing it is one edit repeated, not thirteen investigations.
- **Two of the thirteen are inventories other work is sized from** (11, 13),
  which is a costlier kind of wrong than a tutorial paragraph.

### The 76 to keep forever

`docs/research/09-decisions/` (26 ADRs, ADR-0007 and ADR-1703 among them),
`docs/research/11-design-review/2026-09-05-*` (4 — including the gate-(b)
measurement ADR-1703 rests on), `docs/status-archive/` (2),
`docs/campaign-2026-08-13/` (6), `docs/solver-inventory-2026-09/` (6 — dated
2026-09-09 and already ADR-1703-correct), every dated `*-findings.md` /
`*-2026-MM-DD.md` measurement note, three captured JSON/JSONL evidence
artifacts under `docs/plan/evidence/`, and the four files that carry an explicit
"Superseded"/"Historical" banner (`docs/PARITY-STATUS-AND-PATH.md`,
`docs/plan/gap-analysis-z3-cvc5-2026-07-07.md`,
`docs/plan/references/axeyum-current-state.md`,
`docs/research/08-planning/cold-path-data-structures.md`).

ADR-1703 §Consequences is explicit: "ADR-0007 is not superseded — its *choice*
(BatSat as the first adapter) was correct and served its purpose". The ADR set
is not a cleanup target.

### The 21 that are harmless

Rust SAT-ecosystem surveys and "Source Pointers" URL lists
(`docs/research/02-ecosystems/rust-ecosystem.md`,
`docs/research/05-algorithms/cdcl-sat.md`,
`docs/research/00-orientation/{mission-and-scope,north-star}.md`,
`docs/research/06-rust-strategy/implementation-principles.md`,
`docs/research/README.md`, `docs/plan/references/{README,bitwuzla-and-sat}.md`,
`docs/research/04-data-structures/sat-core-state.md`,
`docs/research/03-architecture/crate-boundaries.md`,
`docs/research/02-ecosystems/competition-landscape-2026-09/*` and
`pipeline-survey-2026-09/arithmetic-division-gap.md`,
`docs/research/05-algorithms/cdcl-xor-integration-design.md`,
`docs/research/08-planning/glaurung-qfbv-execution-plan.md`,
`docs/research/07-verification/scalable-bitblast-certification.md`,
`docs/plan/track-2-theories/P2.5-nra/01-literature.md`,
`docs/plan/{smt-parity-plan-2026-09-05,global/30-workstream-state}.md`,
`docs/internals/cnf-and-sat.md`,
`docs/math-department/11-applied-and-computational.md`) — several of these
already state the ADR-1703 position correctly.

## 7. What is load-bearing

### 7.1 The differential suite — what it covers, and that it runs

Measured, not asserted:

```
scripts/cargo-serialized.sh test -p axeyum-cnf --features batsat-reference \
    --test native_vs_batsat_differential
→ running 3 tests … test result: ok. 3 passed; 0 failed … finished in 0.08s
```

**Nonzero: 3.** Negative control, same command without the feature:

```
→ running 0 tests … test result: ok. 0 passed … finished in 0.00s   (exit 0)
```

The trap ADR-1703 point 5 warns about is real and confirmed on this tree.

What the 3 tests actually compare:

| Test | Population | Assertions |
|---|---|---|
| `the_committed_micro_cnf_corpus_agrees` | `corpus/micro-cnf/*.cnf` — **3 files** | verdict agreement, every `sat` model satisfies, fails if the corpus is empty or everything came back `unknown` |
| `seeded_random_3sat_at_the_threshold_ratio_agrees` | **120** seeded random 3-SAT, `m/n ≈ 4.26`, n = 20…39 | all 120 must be decided, both verdicts must appear (a one-verdict family would be a weak referee), agreement + model validity |
| `degenerate_formulas_agree` | **6** shapes the random family cannot produce (empty formula, empty clause, unit contradiction, tautology, duplicated literal) | all must be decided |

≈ **129 adjudicated instances.** The corpus arm is 3 files; the weight is in the
random arm.

**ADR-1703 under-reports its own coverage.** Point 5 names one file. There are
**five more differentials of the same shape** as gated unit tests in
`crates/axeyum-cnf/src/proof_sat.rs` (5697, 5944, 6004, 6065, 6957):
random-CNF agreement with a self-check, the EMA-restart schedule, the
blocking-literal BCP path, the `reduce_db` stress family, and PHP. Each asserts
`DISAGREE = 0` against batsat **and** checks the emitted DRAT. Those five are
the larger half of what a removal would delete, and no document names them.

### 7.2 Does it run? No.

**No gate, CI job, `justfile` recipe or git hook runs `--features
batsat-reference`** (§5, measured with positive controls). The referee has
never been on an automatic path since it landed on 2026-09-05. So the removal
does not change what runs automatically; it changes what a human is *able* to
run.

That cuts both ways, and the second edge is the important one: **a differential
nobody runs is already providing zero assurance.** Deleting it costs less than
it looks; leaving it costs more than it looks, because its presence is what
makes the ledger read as covered.

### 7.3 What assurance is actually lost — stated plainly

If BatSat goes, **this is what is left checking the native core's verdicts:**

| Failure mode | What catches it after removal | Automatic? | Third party? |
|---|---|---|---|
| wrong `sat` (CNF layer) | `CnfFormula::evaluate` / `model.satisfies` — every accepted `sat` is replayed | **yes** | no (but replay is *decisive*, not corroborative — it does not need to be) |
| wrong `sat` (term layer) | model lifted and replayed through the IR ground evaluator against every original assertion | **yes** | no, same |
| wrong `unsat` | our own DRAT/LRAT checkers — `check_drat` (forward RUP+RAT), `check_drat_backward`, `check_lrat` — verifying the refutation **against the original formula**. **269 call sites across 36 files in `axeyum-cnf`, all on default builds, no feature required.** A wrong `unsat` cannot produce a checkable proof. | **yes** | **no — same project, same crate** |
| wrong `unsat` where the defect is *shared* between the core and our checkers (DIMACS parsing, `CnfFormula` semantics, literal encoding — anything that hands both the same wrong formula) | **nothing, at the CNF layer** | — | — |
| wrong verdict on a QF_BV *term* query | `bv_differential_fuzz` (front door vs Z3), `differential_qfbv_backends` (SatBvBackend vs LazyBvBackend vs PBLS vs Z3), and `scripts/run-qfbv-independent-oracle-rounds.sh` (cvc5 + bitwuzla) | **no — `#![cfg(feature = "full")] #![cfg(feature = "z3")]`, manually run; CI's single `--features z3` line is a bench, not a fuzz** | **yes** |
| a search-strategy bug the CDCL core makes and a differently-built engine would not | `xor_dpll::differential_vs_batsat_random` (300 random formulas, naive XOR-DPLL vs the native core) and `xor_cdcl::differential_vs_batsat_random` (500 random formulas, CDCL(XOR) vs the native core), plus the parity-chain and PHP(7) cross-checks | **yes — these are LIVE on a default build and need no feature** | no — both referees are ours |

So, the honest statement the plan has to be built on:

> **After removal there is no automatically-run third-party adjudication of any
> Axeyum verdict, at any layer.** The third-party oracles (Z3, cvc5, bitwuzla)
> all sit at the QF_BV *term* level behind `--features z3` and are run by hand.
> At the pure-CNF layer the remaining checks are: model replay for `sat`
> (complete and automatic), our own DRAT/LRAT checkers for `unsat` (automatic,
> strong, algorithmically independent, but same-project), and 800 random
> formulas of in-house engine-vs-engine cross-checking that already run on a
> default build.

That is *narrower* than "z3 fuzzes for theories and nothing for pure SAT" — the
DRAT route is a real, automatic, algorithmically independent check on `unsat`,
and it is a stronger one than verdict agreement, because it verifies a
refutation rather than corroborating an opinion. The specific gap is
**a defect the core and our own checkers share**, on a formula that never
reaches a third party.

Note also that **the batsat differential does not close that gap either**, for
the arm that matters: it hands batsat the same `CnfFormula` object the native
core solved, built by the same parser. A DIMACS-parsing defect is invisible to
it too. Only an external *binary* reading the DIMACS text is immune — which is
the CaDiCaL/Kissat arm of `gate_b_sweep`, not the in-process batsat arm.

### 7.4 Two things a removal will trip over

1. **`scripts/check-parity-docs.py:1295` pins a false claim.** The marker
   `"default BatSat adapter remains lower-assurance `Unchecked`"` must be present
   in `docs/research/08-planning/research-questions.md` or the gate fails. So
   the gate is currently **holding the wrong sentence in place**: whoever fixes
   W-item 9 turns `check-parity-docs.py` red unless they change the checker in
   the same commit. `scripts/check-parity-docs.py:1276` does the same for
   `"`config.native_cdcl` is a retired no-op"` in `sat_bv_backend.rs`.
2. **`gate_b_sweep` carries `required-features = ["batsat-reference"]`.**
   Removing the feature removes the tool that produced
   `bench-results/sat-core-gate-b-20260905/`, the four-engine artifact ADR-1703
   rests on. Mitigations already in tree: `crates/axeyum-cnf/examples/native_core_sweep.rs`
   runs the native arm alone (its own header says it exists because
   `gate_b_sweep` doubles the wall time), and the CaDiCaL/Kissat arms were
   always external binaries whose stdout `gate_b_sweep` parses — only the batsat
   column is in-process. So the loss is the batsat column, not the ability to
   re-measure against CaDiCaL and Kissat.

## 8. Removal order

### Tier A — no risk, no replacement needed, can go first

1. The **4 gated unit tests in `crates/axeyum-cnf/src/lib.rs`** (6094, 6116,
   6126, 6151). They test the *adapter* — its raw solve/replay, its pinned
   determinism defaults, its resource-limit `unknown`, its lower-assurance UNSAT
   stamp. Nothing about the native core. They die with the adapter and lose
   nothing.
2. **`crates/axeyum-solver/tests/native_cdcl_baseline.rs`** — a measurement
   harness by its own header, superseded by
   `bench-results/sat-core-gate-b-20260905/`.
3. **`crates/axeyum-bench/examples/cnf_core_bench.rs`**'s batsat column and its
   four `#[cfg]` blocks.
4. **`crates/axeyum-solver/tests/xor_cdcl_curated_measure.rs`** — measurement,
   *but* it is the only harness that measures CDCL(XOR) against anything.
   Re-point it at `solve_with_native_core_timeout` rather than delete it; that
   is a one-line change and it keeps a capability.
5. Once 2–4 are gone: the **feature forwards** in
   `crates/axeyum-solver/Cargo.toml:49` and `crates/axeyum-bench/Cargo.toml:33`,
   and the `[[example]] gate_b_sweep` `required-features` block (§8, Tier C).

### Tier B — do now, independently of the retirement

None of these depend on when batsat goes. They are wrong today.

6. The **4 wrong doc comments** (§2f): `axeyum-cnf/src/lib.rs:5`,
   `axeyum-solver/src/sat_bv_backend.rs:4`,
   `axeyum-solver/tests/sat_bv.rs:4`, `axeyum-solver/src/backend.rs:560`.
7. The **13 W docs** (§6). Nine are one sentence repeated; fix it once and apply.
   **W-item 9 must be committed together with `scripts/check-parity-docs.py:1295`**
   or the gate goes red.
8. **`cnf_stream_bench.rs`'s `"batsat"` JSON key** (`:352`) and its `BatSat=`
   mismatch message (`:339`). It is mislabelling *live* data: every artifact
   that example has written since 2026-09-05 attributes native-core numbers to
   batsat. Renaming the key changes an artifact schema, so it needs its own
   decision about whether old artifacts get a schema-version bump.
9. **`SolverConfig::native_cdcl`** (§2i). The field's doc says "It is read by
   nobody" and three sites read it. Two acceptable fixes: make it genuinely
   unread (drop it from `warm_config_is_honored`'s equality chain, from the
   bench `--certify-end-to-end-unsat` validator, and from the config hash), or
   correct the doc to say what it still does. **Do not leave it as is** — a flag
   documented as changing nothing that silently moves a query off the warm
   engine is precisely the defect class this repository keeps rediscovering.
   Note the destructuring in `warm_config_is_honored` is deliberately
   exhaustive, so dropping the field there is a compile-time-checked change.
10. The stale `unsendable` justification in
    `crates/axeyum-py/src/solver/core.rs:647` and the matching rows in
    `docs/python-2026-08/inventories/smt-solver.md`. **First determine whether
    `IncrementalBvSolver` is still `!Sync`** — that was **not** measured here
    (no `Send`/`Sync` assertion was run). If it is `Sync` now, `unsendable` is a
    gratuitous restriction on the Python API.

### Tier C — needs a replacement built and **wired into a gate** first

11. **`crates/axeyum-cnf/tests/native_vs_batsat_differential.rs`** and the
    **5 gated differentials in `proof_sat.rs`**. Options, ascending cost:
    - **(a)** re-point them at `xor_dpll::solve_with_xor` — an independently
      written naive decider already in-tree and already used exactly this way on
      300 random CNFs. Cheapest; keeps the shape; the referee becomes ours.
    - **(b)** turn every `unsat` in those families into a **DRAT-checked**
      assertion. Strictly stronger than verdict agreement for `unsat`; adds
      nothing for `sat` beyond the replay that already runs. Lands immediately
      and is automatic.
    - **(c)** an **external-binary referee** (CaDiCaL, Kissat, or the `splr`
      binary), driven the way `bv_differential_fuzz` already drives cvc5: skip
      when the binary is absent, `AXEYUM_REQUIRE_*=1` to fail instead of skip in
      a publication lane. This is the **only** option that restores a genuinely
      third-party check, and it costs **no Cargo dependency** — which is the
      whole reason batsat was ever in the graph.

    Recommended: **(b) now, (c) as the replacement of record.** (a) is a
    consolation prize; it does not restore what removal takes away.

    **Whichever is chosen, wire it into `check.sh` / the `justfile` / the
    pre-push hook.** The current referee is in none of them (§5), so shipping a
    replacement that is also in none of them reproduces the defect rather than
    fixing it. And confirm a nonzero test count in the gate itself — the file
    that replaces this one will have the same zero-test-exit-0 shape if it is
    feature-gated.
12. **`crates/axeyum-bench/examples/gate_b_sweep.rs`.** Either accept losing the
    batsat column and keep the native + CaDiCaL/Kissat arms (they need no
    feature — the external arms parse captured stdout), or split the harness
    first. Do not delete it while it is the only thing that can regenerate the
    artifact ADR-1703 cites.

### Tier D — the dependency removal itself, last

13. `crates/axeyum-cnf/src/batsat_reference.rs` (306 lines, whole file).
14. `crates/axeyum-cnf/src/lib.rs:44–45` (`mod`) and `:88–91` (the 6-name
    re-export), plus the gated `use` at `:4947`.
15. `crates/axeyum-cnf/src/proof_sat.rs:5013` (the gated `use`).
16. The `batsat-reference` feature in `crates/axeyum-cnf/Cargo.toml:24` and the
    three `optional = true` lines at `:28–30`.
17. The three `[workspace.dependencies]` lines, `Cargo.toml:58, 69, 70`.
18. Regenerate `Cargo.lock`. Whether `nom`, `cpu-time`, `itertools` and friends
    actually leave the lockfile was **not measured** — check it, do not assume.

### Tier E — never

19. Every ADR (26 files under `docs/research/09-decisions/`). ADR-1703 says in
    terms that ADR-0007 is **not superseded**.
20. Every dated measurement note, design review, diary, campaign log and status
    archive — the 76 H files of §6.
21. All **137** `bench-results/` files. They are recorded artifacts; editing one
    falsifies a measurement.
22. The **design-lineage credit** in `proof_sat.rs`, `cdclt.rs` and
    `lra_online.rs` (§2g). MiniSat/BatSat are named there as the source of a
    design — blocking-literal watch lists, packed clause headers, `ccmin_mode = 2`,
    `lit_redundant`, progress saving. That is attribution, and it stays.
23. The **historical narration** in `crates/axeyum-solver/src/config_registry.rs`
    and `crates/axeyum-solver/src/dpll_lia.rs` (§2h). BatSat is the founding
    case of the admission-limit basis doctrine and the reason
    `scripts/check-admission-limit-basis.py` exists; the `dpll_lia` text is the
    record of why `MAX_PRE_SAT_ARITH_ATOMS` was re-derived from 1,280 to 10,240.
    Removing the word "BatSat" from those files deletes the reason the
    surrounding code and its checker exist.

## 9. Checks this note did not run

Reported as "did not run", never inferred:

- Whether the `rustsat` transitive dependencies (`nom`, `cpu-time`, `itertools`,
  `tempfile`, …) become unreachable workspace-wide once the feature is removed.
- Whether `IncrementalBvSolver` is still `!Sync`, i.e. whether `#[pyclass(unsendable)]`
  in `crates/axeyum-py/src/solver/core.rs` is still *required* rather than just
  stale in its justification.
- Any full-workspace build, `clippy`, or `check.sh` run. This lane compiled only
  `axeyum-cnf` with and without `batsat-reference`, to run the differential and
  its negative control.
- The five `proof_sat.rs` gated differentials were **read**, not executed. Only
  `--test native_vs_batsat_differential` was run.
