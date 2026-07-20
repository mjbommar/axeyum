# Verifying real Rust (not a DSL) — feasibility & design

> **Status:** feasibility spike + design (2026-06-29). The goal: stop verifying a
> hand-built DSL (the [protocol toolkit](protocol-toolkit.md)'s `step` tables) and
> start verifying **actual implementation Rust** — the original "two readings of
> one Rust function" idea and the documented Phase-3 direction. This note records
> what is *buildable in this environment* and picks the path.

## Environment facts (measured 2026-06-29)

- **Toolchain:** `rustc 1.96.0-nightly`. Nightly is available.
- **`rustc -Zunpretty=mir` works driverless** on a `--crate-type=lib` file and
  emits clean, parseable MIR (basic blocks, `switchInt`, place assignments,
  `goto`/`return`) — **no rustc driver, no new dependency**. Caveat printed by
  rustc itself: *"This output format is intended for human consumers only and is
  subject to change without notice."*
- **No MIR tooling clones** in `references/` (only `CreuSAT`, a Creusot-verified
  artifact — not a runnable extractor) and none in the cargo registry; `charon`,
  `aeneas`, `stable-mir-json`, `rustc_smir` are absent.
- **Network is reachable** (`cargo search` works), but a `rustc_private` /
  rustc-driver MIR extractor would pull heavy compiler-internal deps and a custom
  driver — against the project's lean-build rule (default build = no heavy/C++
  deps; backends are feature-gated leaves). So the production driver path is **not**
  a first increment here.

## The key reframe: the toolkit already reflects real Rust (finitely)

The protocol toolkit's `next_under_event` builds the symbolic transition **by
calling the user's real `step` closure at each concrete from-state** and interning
the results as IR constants. That *is* "reflect a real Rust function into the IR" —
by **partial evaluation over a finite domain**. For finite-state code it is sound
*and* complete: the IR is an exact image of the executable Rust, and the *same*
closure is both run (the [fuzzing oracle](fuzzing-and-multi-peer.md)) and proven
(the IR). The closure is genuine, compilable, runnable Rust — not a DSL term.

What's missing for "real systems Rust" is **idiom and scale**: a stack author
writes `enum State { Closed, SynSent, … }` and `fn step(State, Event) -> State`,
not bare `u8` magic numbers; and real code has data-dependent state too large to
enumerate.

## The three paths, and the plan

| Path | What it reflects | Driverless? | Scope | Status |
|---|---|---|---|---|
| **Finite reflection** | a real `fn(State,Event)->State` over an enumerable domain | yes (call the fn) | finite state, sound+complete | **build now (A2)** |
| **MIR-text reflection** | the *compiled* MIR of a real function → symbolic IR | yes (`-Zunpretty=mir`) | data-dependent, prototype-grade | **prototype (A3)** |
| **`stable_mir` driver** | arbitrary Rust via the stable MIR API | no (rustc driver + deps) | the real Phase-3 endgame | documented, deferred |

**A2 — finite reflection on idiomatic Rust (the robust now-increment).** A small
adapter so the user writes an idiomatic `#[repr(u8)] enum State`, an `enum Event`,
and an ordinary `fn step(State, Event) -> State`, and the adapter enumerates the
finite state/event space, calls the *real* `step`, and builds the toolkit `Fsm` —
yielding the unbounded proof + the fuzzing oracle over the user's actual Rust. The
"two readings" made concrete on idiomatic code, no `u8` plumbing exposed.

**A3 — MIR-text reflection prototype (the frontier).** Parse the
`-Zunpretty=mir` of a tiny real function (the `switchInt`/assign/`goto`/`return`
subset that protocol steps compile to) into an `axeyum-ir` term over symbolic
inputs, and verify it — cross-checked against finite reflection (same verdict).
This reflects the *compiled* semantics (what the CPU runs), generalizes past the
finite domain, and proves the MIR pipeline is real. Honest limits: the MIR text
format is unstable (pin the rustc version; treat as prototype), and only a tiny
opcode subset is handled.

**Deferred — `stable_mir` driver.** The production path to arbitrary Rust; needs a
rustc driver + compiler-internal deps, so it waits behind an ADR and a deps
decision (it changes the build's trust/dependency surface).

## B — symbolic proof of reflected MIR (scale past enumeration)

A3 cross-checks the reflected term by *exhaustive evaluation* (all `u8` inputs).
That does not scale: a `u32` function has 2³² inputs. The fix is to feed the
reflected term to the **solver** and prove a property *symbolically* —
`axeyum_solver::prove(arena, &[], goal, cfg)` returns `Proved` / `Disproved(model)`
/ `Unknown`, where `Proved` is a re-checked refutation of `¬goal`. So "reflect
real compiled Rust → prove a property for all inputs" works at any width.

- **Width generalization (cheap).** A wider lookup `fn(u32)->u32` compiles to the
  *same* `switchInt`/`const` MIR shape, only with `_u32` literals — so the A3
  reflector generalizes by reading the bit-width from the `_uN` suffix. A `u32`
  function with five arms is reflected and `T(x) <= 9` is **proved symbolically**
  (instant), where enumerating 2³² inputs is infeasible — the concrete payoff of
  reflect-then-prove over reflect-then-enumerate. A false bound yields a
  `Disproved` countermodel (the verifier catches wrong claims on real code).
- **Arithmetic is the boundary.** Functions using `+`/`<<`/etc. compile (in debug)
  to MIR with *overflow/range-check* branches (`CheckedAdd`, `Assert` terminators,
  panic blocks) — a much larger opcode surface than the clean `switchInt`/`const`
  lookups. Reflecting that robustly is real front-end work; this prototype stays in
  the branch/const subset and documents arithmetic-MIR as the next parser frontier
  (or sidestepped via `-O` / `wrapping_*` ops, which emit check-free MIR).

## Honest boundary

- Finite reflection is *sound and complete* but only for enumerable state — the
  right tool for control-state machines (protocols, capability lifecycles), not
  for data payloads.
- MIR-text reflection is *prototype-grade*: a real-compiled-code demonstration, not
  a maintained front end (unstable format, tiny subset).
- Neither replaces the eventual `stable_mir` front end for arbitrary code; they are
  the achievable, driverless, lean-build-respecting steps that make "verify real
  Rust" concrete *today* and de-risk the bigger investment.

## Status (2026-06-29)

- **A2 — finite reflection: DONE** (`tests/protocol_toolkit.rs`). A `Finite` trait
  + `reflect()` adapter lets a user write idiomatic `#[repr(u8)]` enums and a real
  `fn step(State, Event) -> State`; the capability lifecycle re-expressed this way
  proves Safe for all traces and yields the *same* verdicts as the hand-encoded
  `u8` version — the enum reflection is faithful. The same `step` is run (fuzz)
  and proven (IR): two readings of one real Rust function.
- **A3 — MIR-text reflection: DONE (prototype)** (`tests/mir_reflection.rs`).
  Parses a committed real-MIR fixture into an `axeyum-ir` term and exhaustively
  verifies the term equals the real Rust function on all 256 inputs — the
  *compiled* semantics reflected into the solver, faithfully. Tiny opcode subset,
  unstable-format fixture; a proof-of-concept, not a maintained front end.

## The `stable_mir` decision (deferred — needs an ADR)

The production path to *arbitrary* Rust is a `stable_mir` (or `charon`) front end
behind a rustc driver. It is deferred deliberately, and the call is **not** a
consumer-lane one to make unilaterally, because it changes the project's
dependency and trust surface:

- **Pro:** arbitrary real Rust → IR; the genuine "verify your network stack"
  capability; the documented Phase-3 target.
- **Con:** pulls a rustc driver + compiler-internal crates (`rustc_private`) or an
  external tool (`charon`) — a heavy, version-pinned dependency that cuts against
  the lean-build hard rule (default build = no heavy/non-leaf deps). It also adds a
  *large new trusted component* (the MIR extractor) to the soundness story.

Recommendation: open an ADR scoping (a) the dependency/feature-gating model
(extractor as an optional, feature-gated tool — never in the default build), and
(b) the trust story (the extractor is untrusted; faithfulness is established the
way A3 does it — cross-check the reflected IR against execution, now symbolically
over the input domain rather than exhaustively). Until that ADR lands, finite
reflection (A2) is the robust real-Rust path and the MIR prototype (A3) is the
de-risking evidence that the bigger investment will pay off.

## Reproducible MIR fixture update (2026-07-20, ADR-0287)

The prototype's hand-copied fixture boundary now has a checked capture seam.
The committed package in `crates/axeyum-verify/tests/fixtures/mir/` binds an
ordinary Rust source to raw `-Zunpretty=mir` stdout, exact rustc 1.97.0-nightly
commit/LLVM identity, ordered argv, capture environment, and
source/output/provenance SHA-256 values. It includes checked/clamped reads and a
real store-then-load shape for the next semantic slice.

Run the stable-CI/content gate through Cargo or directly:

```sh
cargo test -p axeyum-verify --test mir_fixture_capture --all-features
python3 scripts/check-verify-mir-fixture.py --verify
```

When the registered compiler is installed, require byte-for-byte regeneration:

```sh
python3 scripts/check-verify-mir-fixture.py --require-replay
```

`--verify` reports `compiler_replay=unavailable` rather than fabricating replay
success on another toolchain; source/output/provenance drift still fails through
the committed hashes. ADR-0288 subsequently adds the separate checked path:
named located syntax, non-panicking stable errors, access-derived panic,
initialized byte stores, branch memory joins, and source-replayed store/load
proofs. The old compatibility reflector remains panic-oriented, but it is no
longer the checked consumer boundary.

## One-command Cargo-owned reflection (2026-07-20, ADR-0289)

`axeyum-mir-build` now selects a function from a target package's own locked
Cargo build instead of compiling a copied source directly. Every path is
absolute and canonical; the target directory and output must not already exist.
For example, from the Axeyum root with two fresh `/tmp` names:

```sh
cargo run -p axeyum-verify --bin axeyum-mir-build -- \
  --manifest-path "$(pwd)/crates/axeyum-verify/tests/fixtures/mir-target-crate/Cargo.toml" \
  --package axeyum-mir-target-fixture --lib \
  --function cargo_store_then_load --target-usize-width 64 \
  --cargo "$(rustup which cargo)" --rustc "$(rustup which rustc)" \
  --target-dir /tmp/axeyum-mir-build-target-1 \
  --output /tmp/axeyum-cargo-store-1.mir
```

The command requires the ADR-0287 compiler (`nightly-2026-05-01`), clears
ambient rustc wrappers/rustflags, invokes one explicit `cargo rustc --locked`
target, and captures raw stdout. It selects and checks the requested function
before atomically retaining the bytes, then prints stable JSON containing the
Cargo/rustc identities and arguments, typed shape, and canonical result/panic/
final-memory terms. Existing outputs are never overwritten and failures remove
a newly created target directory.

The selected Cargo build can execute its own build scripts and is therefore not
a sandbox for hostile packages. The accepted profile is still intentionally
narrow: one acyclic function with scalar values and one by-value bounded byte
array. General places, references, calls, loops, drops/unwinds, generics,
cross-target builds, and `stable_mir` remain future gates.
