# Iteration 1 — candidate apps + first-pass ranking (2026-06-25)

First pass. Score each on four axes (1–5), grounded in the measured
[SCOREBOARD](../../bench-results/SCOREBOARD.md) / [DOMINANCE](../../bench-results/DOMINANCE.md)
and the exposed API (see [README](README.md)):

- **Leverage** — does axeyum *already* decide this well? (BV/ABV are 88–100%
  dominant; NRA/infinite-quantifiers are weak → low leverage.)
- **Tractability** — frontend effort (lowering a program/property → IR terms).
- **Moat-fit** — does it showcase *pure-Rust + certifying + WASM* where incumbents
  structurally can't follow?
- **Demand** — real-world pull + a live competitive field to measure against.

## First, a reframe: apps vs cross-cutting layers

Several of the 10 brainstormed ideas are not standalone apps — they are **layers**
that apply to whichever frontend we build:

- **Counterexample → runnable test** — an output layer for any frontend.
- **WASM in-browser delivery** — a delivery surface for any frontend.
- **SV-COMP / neutral-corpus measurement** — the per-app scoreboard discipline.
- **`#[axeyum::verify]` annotations** — a *surface* of the Rust verifier, not its own app.

So the distinct **apps** are A–D below; the layers (E) are built once and reused.

## Candidate apps

### A. EVM / smart-contract symbolic bug-hunter (halmos-class)
Symbolically execute EVM bytecode; hunt overflow / reentrancy / assertion-violation
/ invariant-break; emit a replayable exploit witness.
- Leverage **5** — EVM is finite-domain: 256-bit words = `BV256`, no floats,
  bounded; lands on axeyum's *strongest* rows (QF_BV/QF_ABV, 88–100% dominant).
- Tractability **4** — the "frontend" is an EVM interpreter: ~150 well-specified
  opcodes, a word stack, and `BV256`/array memory+storage. Far smaller and more
  precise than general binary lifting; no disassembler/CFG-recovery needed.
- Moat-fit **5** — WASM-native (runs in a browser tab — no Z3-via-Emscripten),
  certifiable witnesses, money-critical domain where proof matters.
- Demand **5** — hot field (halmos/a16z, Mythril, Manticore); clear competitor.
- **Σ 19.** The single best strategic fit.

### B. Bounded-property SDK — a typed Rust "prove-or-counterexample" library
A clean Rust API: state a property over bounded ints / bit-vectors / small arrays
in a typed builder (no external program lifting), get `Proved(bound) | Counterexample(inputs) | Unknown`,
**with a Lean-checkable certificate on `Proved`**.
- Leverage **5** — directly the decidable BV/LIA core; no weak fragment involved.
- Tractability **5** — *no program frontend at all*; the "lowering" is a typed
  builder over the existing IR. Lowest effort to a working, clean product.
- Moat-fit **5** — the certificate is the whole point; pure-Rust embeddable + WASM.
- Demand **3** — smaller headline than EVM, but it is the cleanest showcase of the
  cert moat and the foundation other apps reuse.
- **Σ 18.** The fastest path to a clean, functional, SOTA artifact; dogfoods.

### C. Rust verifier (Kani/Prusti/Verus-class), incl. `#[axeyum::verify]` + proptest-prove
Lower Rust (MIR or a `stable_mir`/`charon` subset) → IR; bounded-check panics /
overflow / `unwrap` / assertions; or upgrade `proptest` properties from "256 random
tries" to "no counterexample up to N + certificate." Self-hosting (verify axeyum
with axeyum).
- Leverage **4** — bounded BV/LIA + arrays (rides the in-flight array keystone).
- Tractability **2** — MIR is large; a faithful frontend is real work. Scope to a
  subset (arithmetic + bounded loops + slices) to start.
- Moat-fit **5** — pure-Rust, self-hosting, certifying — a position Kani (CBMC/C++)
  structurally lacks.
- Demand **5** — Rust verification is a hot, crowded, credible field.
- **Σ 16.** Highest narrative/dogfood value; heaviest frontend. Phase it.

### D. Differential QA / outward bug-hunting + neutral-corpus measurement
Aim axeyum's soundness (DISAGREE=0) outward: where axeyum disagrees with a
fast-but-unproven tool (a fuzzer, or another solver via the existing differential
harness), you've found a bug in the *tool or its model*. Plus the SV-COMP / neutral
corpus harness that gives every app an honest scoreboard.
- Leverage **5** — reuses axeyum's exact strengths (soundness + cert).
- Tractability **4** — reuses the existing differential-fuzz infra + shells external
  tools; the measurement harness mirrors `measure_corpus`.
- Moat-fit **4** — "the sound second opinion"; cert-backed.
- Demand **3** — a QA/research tool, lower headline but high trust value, and it is
  the *discipline* that keeps A–C honest.
- **Σ 16.** Best as the measurement/QA backbone for the track.

### E. Cross-cutting layers (build once, reuse across A–D)
- **Counterexample → `#[test]`** — turn a `Model` into a runnable failing test.
- **WASM delivery** — wrap A/B in the existing playground (client-side).
- **Neutral-corpus + competitor scoreboard** — per-app "bugs found / proved vs SOTA."

## First-pass ranking

| Rank | App | Σ | One-line |
|---|---|---|---|
| 1 | **A. EVM bug-hunter** | 19 | best fit: BV/ABV strength + WASM + hot field + finite/decidable |
| 2 | **B. Bounded-property SDK** | 18 | fastest clean SOTA artifact; cleanest cert showcase; foundation |
| 3 | **C. Rust verifier** | 16 | best dogfood/narrative; heaviest frontend → phase it |
| 3 | **D. Differential QA + measurement** | 16 | the honesty backbone for A–C |
| L | **E. Layers** | — | counterexample→test, WASM, scoreboard — reused, not picked alone |

## Open questions to resolve in iteration 2 (research vs SOTA)
1. **EVM:** how much of `halmos`/Mythril's value is the symbolic engine vs the
   Foundry/Solidity integration? Can we hit a useful slice (raw bytecode + a small
   harness) without the whole toolchain? What exactly does `BV256` + array
   storage/memory need that axeyum doesn't already have?
2. **Rust:** `stable_mir`/`charon`/`rustc` MIR vs a small surface IR — what is the
   *minimum* viable lowering that verifies real functions? How do Kani/Verus/Creusot
   actually scope it?
3. **SDK:** what does a *clean, idiomatic* Rust property API look like (vs z3.rs,
   vs `kani::any()`), and how do we make the certificate first-class in the API?
4. **Measurement:** is SV-COMP the right neutral corpus, or per-app (EVM test suites,
   Rust crate corpora)? What is each app's honest "vs SOTA" metric?

→ proceed to iteration 2: research A/B/C/D against the real tools + axeyum's API.
