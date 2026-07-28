# axeyum + glaurung code review -- rank-ordered recommendations

**Date:** 2026-07-17
**Method:** four parallel review agents (3x Sonnet 5 deep passes, 1x Fable 5
quantitative breadth sweep), each keeping a diary (preserved in this directory)
and returning ranked findings, synthesized here.
**Scope:** the axeyum workspace (`crates/*`) and the glaurung->axeyum
integration seam (`glaurung/src/symbolic/solver/*`, `explore.rs`). Read-only;
no source was modified.

Diaries: `1-axeyum-core.md` (solver core files), `2-axeyum-architecture.md`
(workspace/crates), `3-glaurung-seam.md` (integration), `4-axeyum-breadth.md`
(quantitative sweep).

---

## Executive summary

The **algorithms, safety posture, and crate-dependency architecture are
healthy**; the debt is **structural** and concentrated in exactly two places:
the `axeyum-solver` crate (monolithic files + a 567-item flat public API) and
glaurung's `axeyum_backend.rs` integration seam (two parallel warm engines +
policy sprawl). Four independent themes recur across all reviewers:

- **T1 -- Monolith.** `axeyum-solver` holds `reconstruct.rs` (18.5k lines),
  `abv.rs` (15k), `int_reconstruct.rs` (8.9k); 155 of 161 files sit flat in
  `src/`; the crate root re-exports ~567 items. glaurung's `axeyum_backend.rs`
  is a 4.4k-line god-object.
- **T2 -- Copy-paste instead of table/parameter-driven code.** 43
  `reconstruct_*_to_lean_module` twins, strict/nonstrict/algebraic CAD
  triplication, `collect_top_conjuncts` x17, two structurally-identical warm
  engines, 6 identical env-bool parsers, 9 near-identical stats structs.
- **T3 -- Config modeled as loose booleans, permitting invalid states.**
  `SolverConfig` demand/range bool pair (authors' own comment calls the
  both-on combination "a configuration error"); glaurung's `WarmReusePolicy`
  x 6 independent env-booleans; path-state guarded by `.expect()` instead of
  an enum.
- **T4 -- A real deployability-claim gap.** The `qfbv`-minimal profile exists
  and works, but **no consumer uses it** -- glaurung and `axeyum-wasm` both pull
  the full ~208k-line surface. The paper's "minimal pure-Rust footprint" claim
  is currently not realized in practice.

### Healthy signals (state these as strengths in the paper)

- **Zero `unsafe`** in the entire workspace; `unsafe_code = "deny"` at the
  workspace root, `#![forbid(unsafe_code)]` in 6 crates.
- **Clean, acyclic crate dependency DAG** (ir -> bv -> aig -> cnf -> solver);
  no cycles, no back-edges; `axeyum-ir` is a model of module decomposition.
- **No live width-truncation soundness bug in the axeyum core** (the coarse
  grep scare was 100% test-only code); `backend.rs`/`model.rs` are clean
  exemplars.
- **Only 10 TODOs, all phase-tagged**; no `todo!`/`unimplemented!`; very high
  test volume (solver ~104k test lines).
- Unusually thorough soundness/trust doc comments on the core traits.

The single genuine (if dormant) correctness landmine is on the **glaurung
side**, not in axeyum: see R2.

---

## Rank-ordered recommendations

Ranked by (publication impact + severity) / effort. Effort: S (hours),
M (1-3 days), L (week+). Each cites the reporting diary and file:line.

### R1 -- Enforce the `qfbv`-only profile for real  [S1, effort S, PAPER-CRITICAL]
The minimal-footprint claim is not realized: `axeyum-solver` defaults to
`full`, and both real consumers omit `default-features = false`, so glaurung
(`glaurung/Cargo.toml:42-43`) and `axeyum-wasm/Cargo.toml` silently pull
egraph/fp/lean-kernel/smtlib/strings. The `qfbv` feature is verified working
(`cargo check -p axeyum-solver --no-default-features --features qfbv`).
**Action:** make `axeyum-solver`'s default `qfbv`-equivalent (or empty) with
`full`/`z3` opt-in; set consumers to `default-features = false, features =
["qfbv"]`. Cheapest fix with the highest paper-credibility payoff. *(arch #1,#6)*

### R2 -- Fix the wide-constant truncation in glaurung's z3 adapter  [S1, effort S]
`glaurung/src/symbolic/solver/z3_backend.rs:122`:
`BV::from_u64(ctx, value as u64, ...)` truncates any constant wider than 64
bits; model read-back at `:82` (`.as_u64()`) drops wide symbol values the same
way. `Width` goes to `W512` (SIMD regs). Dormant today (no >64b constant site
in the current GPR engine) but a soundness landmine, and the axeyum translator
already handles this correctly via `WideUint`. This is the same defect the
benchmark's Tier-0 128-bit `concat` case surfaced. **Action:** mirror axeyum's
wide path or error explicitly; never silently truncate. Note: the axeyum core
was audited clean of live truncation (core #13). *(seam #5)*

### R3 -- Split the monolithic files along the conventions the code already uses  [S2, effort L]
`reconstruct.rs` (18.5k), `int_reconstruct.rs` (8.9k), `abv.rs` (15k, of which
a 3.5k-line test module is glued to the end) in axeyum; `axeyum_backend.rs`
(4.4k) in glaurung. Natural module seams already exist (proof-fragment families
`cover_*`/`residue_*`/`affine_*`; sibling files `array_memcpy.rs` etc. already
split out; glaurung: translate/config/oneshot/warm/profile/stats). 61 files
exceed 1,500 lines workspace-wide. **Action:** adopt a module-size budget and
apply the existing sibling-module convention consistently; move interleaved
test modules to trailing/sibling files. *(core #3,#6; arch #4; breadth #1,#5;
seam #3)*

### R4 -- Table-drive the proof-reconstruction dispatch  [S2, effort M-L]
Single biggest source of axeyum's largest file: a 331-line match over ~35
`ProofFragment` variants (`reconstruct.rs:3805`), each arm repeating an
identical skeleton, plus 43 `reconstruct_*_to_lean_module` functions
(`:3105,3162,3200,3231,...`) with the same shape. **Action:** one generic
`reconstruct_refutation_to_lean_module(rule, search_fn, cert_fn)` driven by a
`[(fragment, rule, search, reconstruct, timeout, limit)]` table. Likely removes
several thousand lines. *(core #1,#2)*

### R5 -- Unify glaurung's two warm engines and collapse the policy sprawl  [S1, effort M-L]
`SnapshotIncrementalAxeyumSolver::check_snapshot_for_path` (`axeyum_backend.rs:
1028`) and `DirectDeltaLineageAxeyumSolver::transition_and_check` (`:1781`)
implement the same pop-suffix/push-suffix/check/reset algorithm against two
session types, each with its own stats struct (a hand-written adapter at `:1891`
converts one to the other). The `WarmReusePolicy` enum (5 variants, `:141`)
crossed with 6 independent env-booleans materializes as a 200-line nested-match
dispatcher (`check_warm_thread_local_selected:2097`). **Action:** extract a
`WarmTransition` abstraction generic over the session backend; resolve all
policy into one `WarmConfig` struct via `OnceLock`; replace the nested match
with table/enum dispatch. *(seam #1,#2,#9)*

### R6 -- Move the scenario/certificate catalog out of the core solver crate  [S2, effort M]
Dozens of single-benchmark proof modules (`array_fifo`, `array_memcpy`,
`array_xor_swap`, and ~25 `quant_*_cert`/`quant_*_search` pairs) live in
`axeyum-solver`'s public namespace instead of `axeyum-scenarios`, inflating
what "the solver API" means. They also share an identical shape with no
unifying trait. **Action:** relocate to `axeyum-scenarios` (or a
`-solver-catalog` crate); extract a common `SourceBoundCertificate` trait.
*(arch #3,#5)*

### R7 -- Namespace the `axeyum-solver` public API  [S2, effort M, PAPER-RELEVANT]
The crate root flat-exports ~567 items via a `full_exports!()` macro
(`lib.rs:213-595`) with no submodule grouping -- an undifferentiated wall for
anyone reading the docs or the paper's artifact. **Action:** introduce
`pub mod` groupings (`certificates::`, `theories::`, `proofs::`) and re-export
only the core surface (`SolverBackend`, `IncrementalSolver`, `Model`, `solve`,
`check_auto`) at the root. *(arch #2)*

### R8 -- Replace invalid-state boolean configs with enums  [S3, effort S-M]
Three instances of the same smell: `SolverConfig.demand_bit_slicing: bool` +
`range_demand_slicing: Option<..>` (`backend.rs:201`, authors' comment admits
both-on is "a configuration error") -> `enum BitLoweringMode`; glaurung's
`DirectDeltaLineageAxeyumSolver` path invariants guarded by 6 `.expect()`
across 150 lines (`axeyum_backend.rs:1644..1799`) -> `enum { Missing |
Live(..) }`; 6 identical off/false/0//on/true/1 env parsers (`:201-313`) -> one
`parse_bool_env`. **Action:** make illegal states unrepresentable. *(core #5;
seam #4,#7)*

### R9 -- Consolidate the duplicated stats / profile structs  [S3, effort M]
glaurung has 9 `*Stats` structs each with hand-rolled `AtomicU64::load(Relaxed)`
getters (`axeyum_backend.rs:897,1556,2430,2451,2460,2473,2486,2499,2588`), plus
`AxeyumCheckProfile`/`WarmAxeyumCheckProfile` duplicating ~10 phase-timing
fields verbatim, plus ~214 lines of field-to-BTreeMap boilerplate (`:1336-1550`).
**Action:** a shared `SolvePhaseTimings` sub-struct (`#[serde(flatten)]`), a
`load_relaxed!` macro or one sectioned `SolverTelemetry`; move the profile
plumbing into the `profile.rs` from R3. *(seam #6,#10,#13)*

### R10 -- Hoist cross-file duplicated utilities  [S2, effort S-M]
Mechanical, high-count DRY wins: `collect_top_conjuncts` copied identically in
17 solver files; `contains_quantifier` in 16; the `eval_bv` adapter shim in 5
(`axeyum-scenarios`, `axeyum-solver`, `axeyum-verify` x2); six one-line
`*_decline` helpers (`int_reconstruct.rs:1740..5504`); `.expect("base frame
always present")` x10 (`incremental.rs`). **Action:** one shared term-utils
module; hoist `eval_bv`/`eval_bool` into `axeyum-ir`; `base_frame()` helpers.
*(breadth #2; core #7,#9; arch #9)*

### R11 -- Parameterize the strict/nonstrict/algebraic and online-theory families  [S2, effort L]
`nra_real_root.rs` triplicates its CAD core along a strictness axis that already
exists as an enum (`decide_strict_cad_two_var:2894` vs `decide_nonstrict_*:3206`,
etc.); the `*_online.rs` family is 15.7k lines with uflia/uflra sharing 53 of 87
function names. **Action:** thread strictness as a parameter / small
`CellDecider` trait; extract a generic CDCL(T)-online skeleton. *(core #4;
breadth #6)*

### R12 -- Make the `IncrementalSolver` trait earn its keep (or narrow it)  [S3, effort M]
The trait is bypassed by the two adapters that matter: in axeyum only
`IncrementalBvSolver` implements it and most capability is inherent-method-only;
in glaurung the Snapshot and DirectDelta adapters don't use it at all
(`mod.rs:60`, `axeyum_backend.rs:921`). **Action:** either grow the trait to the
capabilities consumers need, or document it as a bounded extension point and
rebuild `SnapshotIncrementalAxeyumSolver` on top of `IncrementalAxeyumSolver`
(also removes the O(depth^2) full re-translation the snapshot path does per
check -- seam #14). *(arch #7; seam #8,#14)*

### R13 -- Reduce the non-test panic surface where it is real  [S3, effort M]
Production unwrap density is near-zero except two spots: `axeyum-scenarios` (788
non-test `.unwrap()` on arena-builder chains) and `axeyum-verify`
`reflect/mir.rs` (28) + `llvm.rs` (20), which unwrap while lowering real
compiler output (a genuine runtime-panic surface). **Action:** thread
`Result`/`expect`-with-context on the verify compiler-lowering path; consider a
builder that returns `Result` for scenarios. *(breadth #4,#7)*

### R14 -- Treat the suppression mass as a punch list  [S4, effort S ongoing]
485 `#[allow(...)]` workspace-wide (277 in solver), of which 102
`too_many_lines` and 65 `too_many_arguments` each mark a function the authors
already know is too big -- a ready-made refactor backlog that overlaps R3/R4/R11.
Also: closed rule-name enums instead of free-form `rule: String`
(`reconstruct.rs:96`) to prevent silent typo divergence across the ~40 hand-typed
call sites. **Action:** burn down alongside R3/R4; convert the string rule-ids to
a const/enum set. *(core #11,#14; breadth #8)*

---

## Sequencing suggestion

1. **Sprint 1 (quick, high-value, paper-facing):** R1 (qfbv profile), R2 (wide
   const), R7 (API namespacing), R10 (utility hoists). Days, not weeks; directly
   improves the artifact a reviewer would open.
2. **Sprint 2 (structural DRY):** R4 (reconstruct table), R5 (warm-engine
   unification + WarmConfig), R8 (config enums), R9 (stats consolidation).
3. **Sprint 3 (the big splits):** R3 (file splits), R6 (catalog relocation),
   R11 (strictness/online parameterization), R12 (trait), R13/R14 (panic
   surface, punch list).

Nothing here is a correctness emergency (R2 is dormant). The theme for the
paper: **the science is sound and safe; the engineering needs a de-duplication
and modularization pass before the artifact is reviewer-ready.**
