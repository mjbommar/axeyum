# axeyum-verify — STATUS

Live tracker for the Rust verifier (App C). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-26 — Phase 2 LANDED.** Macro array support, `usize`/`isize` widths,
  Lean-cert coverage metric, bounded `while` + a BMC `TransitionSystem` route,
  compound assignment, and the `if`-merge edge cases all shipped (details below).
  41 tests green; full gate (fmt + clippy `-D warnings` pedantic --all-features +
  tests + doc `-D warnings`) clean. DISAGREE=0 maintained on every counterexample.
- **2026-06-25 — Phase 1 LANDED.** `#[axeyum::verify]` works end-to-end over the
  restricted Rust surface: parse (syn) → lower to `axeyum-ir` terms (each panic
  class an explicit bad state) → decide via `axeyum_solver::prove` →
  `Verified{certified} | Counterexample{class, Witness inputs} | Unknown`. Every
  counterexample is re-validated by running the ORIGINAL fn on the witness under
  `catch_unwind` (DISAGREE=0). Two crates, both `#![forbid(unsafe_code)]`; full
  gate (fmt + clippy `-D warnings` pedantic + tests + doc) green.

## What Phase 2 added
- **Macro array support (#1):** the proc-macro now parses `[T; N]` and `&[T; N]`
  array params (`ArrayParam`) and lowers `a[i]` indexing (`Expr::Index`); index-OOB
  checks end to end. Unsized `&[T]` is a clean compile error (no fixed length to
  bound). Array modeling stays in the **one-shot** solver fragment (the runtime's
  fresh-symbol element vector + `ite`-select + `idx >= len` bad state), NOT the warm
  array path U6 forbids. Worked: `get([u8;4], usize)` OOB reproduces;
  `safe_get(&[u8;4], usize)` guarded → Verified.
- **`usize`/`isize` (#2):** mapped to a configured **64-bit** width (documented:
  a 64-bit model is the conservative over-approximation for index reasoning; a
  narrower target only removes reachable values). Reproductions write them back as
  `usize`/`isize` so the witness call type-checks. `usize` suffixes (`4usize`) parse.
- **Lean-cert coverage metric (#3):** `Verdict::Verified` carries
  `lean_module: Option<String>` (best-effort `prove_unsat_to_lean_module` over the
  flattened refuted safety query — split conjuncts, strip ¬¬, drop the `true` path
  conjunct). `cert_coverage(&[Verdict]) -> CertCoverage { verified, certified,
  lean_certified }` + `lean_fraction()`. tests/cert_coverage.rs reports
  **1/4 = 25% Lean-certified, 4/4 in-tree-certified** on the sample set; the
  antisymmetry example `if a<=b { assert!(!(b<a)); }` carries a real Lean module
  (asserted `theorem axeyum_refutation`/`False`). Coverage is capped by the upstream
  reconstructor's narrow QF_BV fragment — **inherits UPSTREAM-FEEDBACK U1/U4**, not a
  new gap (a single bitwise-bound refutation routes through DRAT and declines Lean;
  only the separate-conjunct comparison-contradiction shape reconstructs).
- **Bounded `while` + BMC route (#4):** `ast::Stmt::While { cond, bound, body }`
  bounded by `#[axeyum::unwind(K)]`, lowered as `K` sequential `if cond { body }`
  (reuses the proven If env-merge + path-condition accumulation → sound, in-fragment,
  certifiable). Separately, `bmc.rs` proves the **`bounded_model_check`
  `TransitionSystem` route is NOT U6-blocked for scalar state**: `CounterLoopSystem`
  drives the warm BMC engine (`check_loop` → `LoopSafety`). Verified the API: the
  array-free `bounded_model_check` rides the warm path; `_with_memory` decides arrays
  **one-shot** via validated eager elimination (NOT the warm array path U6 forbids).
  A fully general CFG→`TransitionSystem` lowering from arbitrary bodies is a recorded
  follow-up; the unrolling path covers the general `while` case today.
- **`if`-merge edge cases (#5) + a soundness fix:** locking env-merge semantics
  surfaced a real defect — the flat runtime env leaked an **arm-local `let` that
  shadows an outer binding** through the join as a reassignment, producing a
  *spurious* counterexample (false positive; the soundness floor would catch the
  non-reproducing witness, but reporting a phantom bug violates "Unknown never
  lies"). Fixed: per-scope tracking of `let`-declared names; `lower_scoped` restores
  a shadowed outer value (or removes a freshly-introduced one) on leaving an `if`
  arm / loop body. tests/if_merge.rs (5) pin partial reassignment, both-arms
  ite-merge, the shadow no-leak regression, and panic-inside-arm reachability.
- **Compound assignment:** `x op= rhs` (`+=`,`-=`,`*=`,`/=`,`%=`,`&=`,`|=`,`^=`,
  `<<=`,`>>=`) desugared to `x = x op rhs;`.
- **Reproduction rendering (#6):** `reproduce::render_counterexample_test` turns a
  Counterexample into the SOURCE of a committed regression `#[test]` via App B's
  `axeyum_property::render_reproduction_test`/`Reproduction`/`WitnessBinding`
  (scalars, `[T; N]` arrays, signed decimals). Aligns App C with App A/B output.

## What Phase 1 covers
- **Crates:** `axeyum-verify` (runtime: `ast`, `lower`, `verify`, `reproduce`) +
  `axeyum-verify-macros` (proc-macro: `verify`, `unwind`). Wired into the
  workspace; `syn`/`quote`/`proc-macro2` added to `[workspace.dependencies]`
  (additive only).
- **Surface:** params/locals `uN`/`iN` (→ `BitVec(N)`) and `bool`; `let`,
  reassignment, `if`/`else` (env merge via `ite`), arithmetic/bitwise/comparison,
  `&&`/`||`, `assert!`/`assert_eq!`, `panic!`/`unreachable!`,
  `axeyum_verify::opt(is_some, value).unwrap()/.expect()`,
  `#[axeyum::unwind(K)]`-bounded `for i in 0..N` (fully unrolled, fn-level
  attribute — expression-position attrs are nightly-only, so the bound goes on
  the fn). Untyped int literals coerce to the sibling/declared type.
- **Panic classes → bad states:** {un,}signed add/sub/mul overflow (picks
  `bv_{u,s}{add,sub,mul}o` by operand signedness, matching Rust debug panics),
  negation overflow, explicit `÷0`/`%0` (BV div is SMT-total ≠ Rust panic, so
  checked), index-out-of-bounds (`idx >= len` over a fresh-symbol element vector
  + `ite` chain — runtime supports it; macro array parsing is Phase 2),
  `assert!` false, `panic!`/`unreachable!` reached, `unwrap`-on-`None`.
- **Verdict + reproduction:** `Verified` carries an independently re-checked
  certificate (`prove` re-checks before returning `Proved`; we also re-run
  `evidence.check`). `Counterexample` lifts the model into typed `Witness`es;
  the macro-generated `#[test]` converts them to the fn's arg types and asserts
  the original fn panics. Out-of-fragment constructs (floats, `while`, methods,
  heap, traits, closures, recursion) are a clean compile error or honest
  `Unknown` — never a silent mis-model.
- **Worked examples (all green):** `tests/macro_examples.rs` —
  `clamp` (mask ≤ 15) Verified+certified; `safe_div` (guarded) Verified;
  `add(u8,u8)` add-overflow / `loopy` unwound-loop-assert / `maybe` unwrap-None
  Counterexample with witnesses that concretely reproduce. `tests/runtime.rs` —
  7 AST-level checks incl. i8 signed overflow + ÷0 + guarded-div Verified. Plus
  a `compile_fail` doctest (float param rejected).

## Gates / discipline
`#![forbid(unsafe_code)]`; `cargo fmt`; `cargo clippy -p axeyum-verify
-p axeyum-verify-macros --all-targets -- -D warnings` (pedantic, fixed not
allowed); `cargo test -p axeyum-verify`; `RUSTDOCFLAGS=-D warnings cargo doc`.
All run via `./scripts/mem-run.sh -j4`. New-crate-only + additive root
`Cargo.toml`; no edits to existing crates or the main tree.

## vs-Kani scoreboard — DEFERRED (Kani not installed)
Kani is **not installed** in this environment and the network is offline, so the
PLAN's "≈20 Kani integer harnesses, DISAGREE=0 vs Kani" scoreboard is **deferred**.
The soundness floor is met *without* Kani: each counterexample is independently
re-validated by executing the original Rust fn on the witness (a
panic/overflow), and each `Verified` carries a re-checked `Certificate` (the moat
Kani/CBMC cannot produce). When Kani becomes available: run its
`tests/`-integer/array fragment through both and record agreement + cert-coverage.

## Next actions (Phase 3 / hardening — none blocking Phase 2)
1. **General CFG→`TransitionSystem` lowering.** `bmc.rs` proves the warm BMC route
   works for scalar state (the worked `CounterLoopSystem`); a general adapter from
   any `#[verify]` body — mapping every live local to a step-indexed state var and
   building `trans` from the body — would give warm-solver reuse across unroll
   depths for deep loops. Arrays-in-loop-state route through `_with_memory`
   (one-shot per depth); keep off the warm array path (U6).
2. **Widen Lean-cert coverage.** Currently 25% on the sample (one antisymmetry-
   shaped example). Inherits UPSTREAM-FEEDBACK U1/U4 — when the upstream
   reconstructor flattens conjunctions / covers more QF_BV arithmetic, verify's
   coverage rises for free. Add more in-fragment safe examples to the metric set.
3. **vs-Kani scoreboard** once Kani is installable (DISAGREE=0 + cert-coverage).
4. **MIR consumer (PLAN Phase 3).** `stable-mir-json` front-end behind the same
   lowering core; demo verifying one real `axeyum-bv` leaf fn (self-hosting PoC).
5. **`isize`/signed-`usize` arithmetic edge cases** and wider-than-64 native types
   if a target needs them (width is configurable).

## Changelog
- **2026-06-26** — Phase 2 landed: macro array params (`[T;N]`/`&[T;N]`) + `a[i]`
  indexing; `usize`/`isize` → 64-bit; `Verdict::Verified.lean_module` +
  `cert_coverage` (1/4=25% Lean, 4/4 in-tree-certified on the sample); bounded
  `while` (unrolled) + a `bounded_model_check` `TransitionSystem` route confirmed
  NOT U6-blocked for scalar state; compound assignment; `if`-merge edge tests that
  surfaced + fixed an arm-local-`let` shadow-leak (spurious-counterexample) defect;
  `render_counterexample_test` via App B's reproduction layer. 41 tests green;
  two compile_fail doctests (float param, unsized `&[T]`). DISAGREE=0 throughout.
- **2026-06-25** — Phase 1 landed: scaffold → runtime (ast/lower/verify/
  reproduce) + proc-macro (parse/verify/unwind) → 16 green tests + compile_fail
  doctest, DISAGREE=0 on every counterexample. vs-Kani scoreboard deferred
  (Kani not installed).
- **2026-06-25** — PLAN/STATUS written; crate scaffold queued behind B + A's helper.
