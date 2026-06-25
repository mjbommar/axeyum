# axeyum-verify — STATUS

Live tracker for the Rust verifier (App C). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-25 — Phase 1 LANDED.** `#[axeyum::verify]` works end-to-end over the
  restricted Rust surface: parse (syn) → lower to `axeyum-ir` terms (each panic
  class an explicit bad state) → decide via `axeyum_solver::prove` →
  `Verified{certified} | Counterexample{class, Witness inputs} | Unknown`. Every
  counterexample is re-validated by running the ORIGINAL fn on the witness under
  `catch_unwind` (DISAGREE=0). Two crates, both `#![forbid(unsafe_code)]`; full
  gate (fmt + clippy `-D warnings` pedantic + tests + doc) green.

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

## Next actions (Phase 2 / hardening — none blocking Phase 1)
1. **Macro array support.** The runtime already models fixed `[T;N]`/`&[T]`
   (index-OOB + element symbols); the proc-macro does not yet *parse* array
   params/indexing — add `ArrayParam` parsing + `Expr::Index` lowering.
2. **Native-type widths.** Map `usize`/`isize` to a configured width; today only
   explicit `uN`/`iN` are accepted.
3. **CFG/BMC for unbounded loops.** Phase-1 unrolls `for 0..N`; wire a
   CFG→`TransitionSystem` adapter onto `bounded_model_check_with_memory` for
   `while`/data-dependent loops (PLAN Phase 2).
4. **Cert coverage metric + Lean modules.** Surface `Certificate::to_lean_module`
   coverage as the headline moat number (PLAN Phase 2).
5. **vs-Kani scoreboard** once Kani is installable.
6. **`if`-merge edge cases.** The env-merge keeps a binding's pre-branch value
   when types diverge across arms; add tests for shadowing / partial reassignment
   to lock the semantics.

## Changelog
- **2026-06-25** — Phase 1 landed: scaffold → runtime (ast/lower/verify/
  reproduce) + proc-macro (parse/verify/unwind) → 16 green tests + compile_fail
  doctest, DISAGREE=0 on every counterexample. vs-Kani scoreboard deferred
  (Kani not installed).
- **2026-06-25** — PLAN/STATUS written; crate scaffold queued behind B + A's helper.
