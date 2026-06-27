# Consumer Track — software verification & bug-hunting *applications* of axeyum

> A demand-pull complement to the capability-push roadmap. Where [PLAN.md](../../PLAN.md)
> builds solver internals and measures vs SMT-LIB, this track starts from the
> **consumer end** — real software, real bugs, real verification workflows — and
> lets that demand *pull* on the stack. The north star: **clean, functional,
> state-of-the-art applications of the axeyum framework**, worked backwards from
> what a user actually wants.

## Why this track exists

1. **Prioritization by real demand**, not theory breadth — we build the capability
   a real bug-hunt pulls on, not the next ledger row.
2. **A forcing function for the frontend.** The solver-side symexec primitives are
   already built (`SymbolicExecutor`, `bounded_model_check`, k-induction +
   certified, `solve_horn`, `prove_safety_{pdr,imc}`); what's missing is the
   *consumer frontend* ([P4.2](../plan/track-4-usecases-frontend/P4.2-symexec-cfg.md)).
   Building real apps forces it to exist with a concrete target.
3. **Human-legible evidence.** Output is "found this bug, here's a reproducible
   witness" / "proved this property, here's a Lean-checkable certificate" — not a
   decide-rate row.
4. **The moat, made user-visible.** A **pure-Rust, certifying, WASM-deliverable**
   verifier is Pareto-dominant over angr (Python+C), Kani (CBMC/C++), KLEE
   (LLVM/C++), halmos (Python+Z3): none certify to a kernel, none run client-side.
   This track is where that advantage becomes a product.

## The consumer surface axeyum already exposes (what frontends call)

- `axeyum_solver::{solve, check_auto, Solver, Model}` — decide + model.
- `SymbolicExecutor` — full DFS path explorer: `enter`/`backtrack`/`assume`/
  `branch`/`status`/`model`/`enumerate_inputs`/`maximize`/`minimize(_signed/_int)`.
- `bmc::{bounded_model_check, bounded_model_check_with_memory,
  prove_safety_k_induction, certify_safety_k_induction}`.
- `{horn::solve_horn, prove_safety_imc, prove_safety_pdr*}` — reachability.
- `evidence::produce_evidence`, `prove_unsat_to_lean_module` — the certificate.
- `axeyum-property` — typed Bool / BV / Int prove-or-counterexample SDK over the
  evidence APIs, with `Symbolic` scalar/tuple inputs, named-field symbolic
  bundles, minimized scalar counterexamples, and Rust test skeletons.
- `axeyum-wasm` — `solve_smtlib_json` (client-side, the delivery substrate).

A frontend's job: lower a program/property → axeyum IR terms → call the above →
lift the result back to the user's domain (a failing input, a test, a proof).

## How this track works (process)

`research → rank → pick 3-5 → scaffold (PLAN.md + STATUS.md each) → build
iteratively with opus sub-agents + per-app task lists`. Every increment is sound,
tested, gated, and — where a verdict is involved — **DISAGREE = 0** against an
oracle. Each app gets its own measured scoreboard (bugs found / properties proved
vs the SOTA tool), the consumer-track analogue of the SMT scoreboard.

## Coordination / lane boundary (do NOT step on the other agent)

The other agent owns **solver internals** — `axeyum-ir`, `axeyum-rewrite`,
`axeyum-solver` deciders, the Sort-IR keystone (currently a large *uncommitted*
in-flight change). This track:
- adds **only new crates** (frontends/harnesses/SDKs) and **new docs** — never
  edits the core solver/IR/rewrite files;
- consumes `axeyum-solver` as a **black box** (a stable, committed dependency);
  when it hits a missing capability, it files a pull request *as a note* for the
  solver agent rather than reaching into the core;
- builds on an **isolated `consumer-track` git worktree/branch** once building
  starts, so the other agent's uncommitted surgery is never touched; merges to
  `main` are new-crate-only (no conflicts with their IR edits).

## Contents

- [`01-ideas-and-ranking.md`](01-ideas-and-ranking.md) — iteration 1: candidate
  apps + first-pass leverage×tractability×moat×demand ranking.
- (iteration 2) per-candidate SOTA research notes.
- (iteration 3) `decision.md` — the final 3-5 picks + rationale.
- [`property/`](property/) — bounded-property SDK plan/status.
- per-app subdirectories, each with its own `PLAN.md` + `STATUS.md`.
