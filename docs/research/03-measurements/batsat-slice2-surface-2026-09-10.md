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

## 6. Docs classification

*(pending — filled in by the follow-up commit)*
