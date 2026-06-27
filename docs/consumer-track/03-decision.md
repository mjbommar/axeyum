# Iteration 3 — decision: what we build (2026-06-25)

Synthesizing iterations 1–2 (three source-grounded opus scoping reports, all
candidates tractable + unblocked). **Build 3 user-facing apps + 1 shared
measurement backbone + reused layers** — working backwards from *clean, functional,
state-of-the-art applications of axeyum*.

## The picks (rank-ordered by build sequence)

| # | Deliverable | Crate | Kind | Why / moat | Scores (L/T/M/D) |
|---|---|---|---|---|---|
| 1 | **Bounded-property SDK** | `axeyum-property` | app + foundation | lowest-effort clean artifact (no frontend); cleanest cert showcase; A & C reuse its typed-term + cert plumbing | 5/5/5/3 |
| 2 | **Measurement / QA backbone** | `axeyum-bench` examples + `docs/consumer-track/*/SCOREBOARD.md` | shared infra | the honesty gate — every app commits a vs-SOTA scoreboard + DISAGREE=0 before claiming a number | 5/4/—/— |
| 3 | **EVM bug-hunter** | `axeyum-evm` | app (flagship) | lands on axeyum's strongest rows; Lean-checkable "no-bug" proof + WASM in-browser — incumbents (halmos/hevm) ship zero proofs, can't run client-side; money-critical | 5/4/5/5 |
| 4 | **Rust verifier** | `axeyum-verify` | app | `#[axeyum::verify]` proc-macro, days-to-demo; pure-Rust + WASM + certifying vs Kani; no-annotation + single-stack cert vs Verus/Creusot; self-hosting horizon | 4/3/5/5 |
| L | **Reused layers** | (in the above) | layer | counterexample→`#[test]`; WASM delivery — built once, reused by A & C | — |

**Why this set, worked backwards from the goal:** the goal is *clean, functional,
SOTA applications*. B is the cleanest and the foundation (build first, everything
reuses it). D makes "SOTA" measurable and honest (build alongside B). A is the
flagship where the moat is sharpest and demand is highest. C is the highest-demand
field with a genuinely days-to-demo MVP. Together they exercise the whole
consumer surface — SDK, symbolic execution, certification, measurement — and each
is a real product, not a toy.

## Build order & dependencies

```
B (SDK: typed terms + prove + cert)        ← foundation, start now
└─ D (measure_<app>.rs harness + scoreboard) ← honesty gate, alongside B
   ├─ A (EVM: interpreter → SymbolicExecutor) ← reuses B cert plumbing + D scoreboard
   └─ C (Rust: #[axeyum::verify] proc-macro)  ← reuses B + symexec template + D
      └─ E layers (counterexample→test, WASM)  ← reused by A & C
```

Rationale: B has no external frontend and the cleanest path to a working,
cert-carrying artifact (Tractability 5) — it de-risks the cert/model/lift plumbing
that A and C both reuse. D is cheap (generalizes `measure_corpus.rs` +
`audit_dominance`) and gates honesty from day one. A and C are then frontend work
over a proven core.

## Per-app success criteria (each must hit all four)
1. **Clean** — idiomatic Rust API / CLI, new-crate-only, no core edits.
2. **Functional** — solves/decides real inputs end-to-end (a real property, a real
   contract, a real Rust fn), emits a human-usable result (witness / `#[test]` / proof).
3. **SOTA-measured** — a committed per-app scoreboard vs the named competitor
   (proptest+Kani / hevm+halmos / Kani), with **DISAGREE = 0** as the soundness floor.
4. **Certifying where it can** — `Proved`/"no bug" carries a re-checked
   `EvidenceReport`, and a standalone Lean module *when in fragment* (honest
   `Option`, never a false promise).

## Coordination & isolation plan (do not step on the solver agent)
- The solver agent has a **large uncommitted Sort-IR change** in the main tree.
- This track builds on an **isolated `consumer-track` git worktree** off committed
  `origin/main`, so their WIP is never touched and our `target/` is separate.
- Footprint = **new crates only** (`axeyum-property`, `axeyum-evm`, `axeyum-verify`)
  + new `axeyum-bench` examples + new docs. The one shared edit is adding the new
  crates to `[workspace].members` in the root `Cargo.toml` — done *in the worktree*,
  merged as an additive, conflict-free line.
- Merges to `main` are new-crate-only → no collision with their IR edits. If the
  root `Cargo.toml` member-list conflicts, it's a trivial additive resolve.
- Capability gaps go to the solver agent **as notes** ([02-research-synthesis](02-research-synthesis.md) §"Notes filed"), never as reach-ins.

## Next actions
- Task 43 (scaffold): **partially landed on `main` for B** —
  `crates/axeyum-property` plus `docs/consumer-track/property/{PLAN,STATUS}.md`.
  Remaining scaffold work is D/A/C docs and crates. The earlier isolated-worktree
  instruction is superseded for this session by the thread rule to stay on
  `main`.
- Task 44 (build): continue **B (`axeyum-property` v0)** from the committed
  typed Bool/BV/Int proof slice: add ergonomic operator traits or
  `#[derive(Symbolic)]` over the landed `symbolic_struct` named-field builder,
  extend the native-scalar counterexample-to-`#[test]` layer to
  structured/domain replay, and add the SDK scoreboard gate before moving to D,
  A, C.
