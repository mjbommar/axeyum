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

## Honest boundary

- Finite reflection is *sound and complete* but only for enumerable state — the
  right tool for control-state machines (protocols, capability lifecycles), not
  for data payloads.
- MIR-text reflection is *prototype-grade*: a real-compiled-code demonstration, not
  a maintained front end (unstable format, tiny subset).
- Neither replaces the eventual `stable_mir` front end for arbitrary code; they are
  the achievable, driverless, lean-build-respecting steps that make "verify real
  Rust" concrete *today* and de-risk the bigger investment.

## Plan

- A2: finite-reflection adapter + an idiomatic enum-based real-Rust protocol
  verified through it (cross-checked vs the existing toolkit verdicts).
- A3: the MIR-text reflection prototype on one tiny function, cross-checked vs
  finite reflection; honest limits documented.
- A4: gates, scoreboard, plan the `stable_mir` decision.
