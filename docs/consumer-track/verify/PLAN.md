# axeyum-verify — PLAN

> **App C.** A `#[axeyum::verify]` proc-macro that bounded-checks a Rust function
> for panics / integer overflow / `unwrap` failures / assertion violations and
> returns a failing input (as a runnable `#[test]`) — or "verified up to bound K"
> with a re-checked certificate. Self-hosting horizon (verify axeyum with axeyum).
> Full scoping: [02-research-synthesis §C](../02-research-synthesis.md).

## Goal (worked backwards)
A Rust dev annotates a function and gets, in their normal `cargo test` loop, either
a concrete reproducing input or a bounded verification with a certificate — **no
annotation burden** (unlike Verus/Creusot's `requires`/`ensures`/invariants) and
**no C++/CBMC dependency** (unlike Kani), all in one pure-Rust stack that can run in
WASM. The differentiator vs Kani: a checkable proof Kani/CBMC cannot produce; vs
Verus/Creusot: no-annotation + single-stack kernel cert (not "proves more").

## Why it's tractable (days-to-demo, not months)
The lowest-effort path is a **`syn` proc-macro over a restricted Rust surface, NOT
a MIR frontend.** `crates/axeyum-solver/tests/symbolic_execution.rs` is already a
working symbolic executor for a register VM — the MVP is "swap the toy ISA for a
small Rust-surface AST + add the panic-class checks," lowering to App B's typed
terms and driving `SymbolicExecutor`.

## MVP scope (the restricted surface)
- **Covered:** integer/bool params + locals (`uN/iN` → `Bv<N>`, `bool` → `Bool`),
  arithmetic/bitwise/comparison, `if`/`match`-on-int, `assert!`/`assert_eq!`,
  `#[axeyum::unwind(K)]`-bounded `for i in 0..K`/`while`, fixed `[T;N]` / `&[T]` via
  `Sort::Array`. Panic classes: arithmetic overflow (widened-compare miter — reuse
  the `bv_*_overflows` helper shared with App A), `unwrap()`/`expect()` on
  `Option`/`Result` (model the discriminant as a symbolic bool, assert `Some`/`Ok`),
  index-out-of-bounds (`idx >= len` is a bad state), explicit `panic!`/`unreachable!`.
- **Deferred (scope by fragment, like Verus/Flux):** heap (`Box`/`Vec`/`Rc`), trait
  objects, closures-with-capture, unbounded recursion, floats, non-mono generics.
- **Caveat:** BV div is SMT-LIB-total (÷0 = all-ones) ≠ Rust's panic → emit an
  explicit `÷0`/`%0` bad-state check; don't rely on the operator.

## Phases
- **Phase 1 (smallest demo):** `#[axeyum::verify]` over straight-line +
  `#[unwind(K)]`-bounded integer/bool fns; check overflow + `assert!` + `panic!` +
  `unwrap`-on-`Option`; drive `SymbolicExecutor` directly (no BMC/CFG yet); output
  `Verified(K) | Counterexample(concrete inputs as a runnable #[test]) | Unknown`.
  Bench ~20 Kani integer harnesses. Reuses App B + the counterexample→test layer.
- **Phase 2:** `Sort::Array` for `[T;N]`/`&[T]` (index-OOB); a CFG→`TransitionSystem`
  adapter onto `bounded_model_check_with_memory` for loopy/stateful fns; wire
  `produce_evidence`/`prove_unsat_to_lean` so verified results carry a cert
  *when in fragment*; report cert-coverage as the headline moat metric.
- **Phase 3:** a `stable-mir-json` MIR consumer behind the same lowering core to
  widen language coverage toward Kani parity; demo verifying one real `axeyum-bv`
  leaf function (the self-hosting proof-of-concept).

## Success criteria
1. **Clean** — `axeyum-verify` (lib + proc-macro), `#![forbid(unsafe_code)]`.
2. **Functional** — checks real Rust fns end-to-end; counterexample is a runnable
   failing `#[test]`; `Unknown` never lies; honest unwind bound surfaced.
3. **SOTA-measured** — corpus = Kani's own `tests/` (integer/array fragment); metric
   = fns decided agreeing with **Kani** on the shared subset (**DISAGREE = 0**) +
   **cert-coverage** (the number Kani/CBMC can't produce). Avoid SV-COMP (C, off-mission).
4. **Certifying where it can** — verified results carry the App-B `Certificate`.

## Coordination
New crate(s) `crates/axeyum-verify` (+ a proc-macro crate if needed), consumer-track
worktree, consumes axeyum-solver + axeyum-property as black boxes. Self-hosting is a
long-horizon flagship — demo on a single leaf fn first, do not claim solver-wide.
