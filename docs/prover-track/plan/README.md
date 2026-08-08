# Track 6 — Certificate-First Proof Assistant

**The build guide.** Design: [`../design/03-architecture.md`](../design/03-architecture.md).
Rationale: [`../design/00-thesis.md`](../design/00-thesis.md).
Entry ADR: [ADR-0167](../../research/09-decisions/adr-0167-prover-track-entry.md).

> **Current boundary (2026-08-07).** This page defines dependency order; root
> [PLAN.md](../../../PLAN.md) defines current project priority. P6.0 is partial
> with major kernel slices landed. P6.1 has no standalone bridge, and P6.2/P6.3
> have no goal/tactic implementation; the generated Lean registry reports the
> goals/tactics axis `not_started`.

Each phase has its own file with tasks, sizes, exit criteria, and its TCB
statement. **Every slice lands alone**; none is justified by a later one.

This track builds Axeyum's native certificate-first proof assistant. The
separate [Lean-system compatibility roadmap](../../plan/lean-system-compatibility-roadmap-2026-07-21.md)
and [implementation plan](../../plan/lean-system-implementation-plan-2026-07-21.md)
add versioned declaration/library import and staged native
source/Lake/editor/runtime/mathlib compatibility. They reuse P6.2/P6.3 for goals
and tactics rather than creating a second goal engine; Track 6 does not own a
competing theorem library or an Axeyum-only proof language.

---

## The shape

```
  agent / human            ── proposes motives, depths, witnesses     untrusted
  ─────────────────────────────────────────────────────────────
  axeyum-goal              ── Goal · Hole · tactics emit Steps        untrusted
  ═════════════════════════════════════════════════════════════
  axeyum-goal::check       ── one small checker per Step kind         ★ TRUSTED
  axeyum-lean-kernel       ── CIC                                     ★ TRUSTED
  ─────────────────────────────────────────────────────────────
  axeyum-solver / egraph   ── Alethe, LRAT, egg chains, models        untrusted
```

**The TCB is two boxes.** Everything that searches is outside it.

## Dependency order

| # | Phase | Size | Ships |
|---|---|---|---|
| **1** | **[P6.0](P6.0-kernel-trustworthiness.md)** — kernel trustworthiness | M | A kernel trustworthy **by adversarial test**, not by assertion. *Owed to P3.6/P3.7 regardless of this track.* |
| **2** | **[P6.1a](P6.1-obligation-bridge.md)** — extract IR→CIC into a real bridge | M | A reusable bridge. **Zero new capability** — it de-risks the seam, and **P3.7's T3.7.3 needs the identical work.** |
| **3** | **[P6.2](P6.2-goals-and-holes.md)** — `Goal`, `Hole`, delayed assignment, depth invariant | L | The layer that does not exist. **Get delayed assignment right or nothing above works.** |
| **4** | **`Decide` + `Intro` + `Apply`** ([P6.3](P6.3-certificate-tactics.md)) | M | **The smallest end-to-end proof.** `decide` reuses reconstruction, so this is plumbing — and it proves the protocol. |
| **5** | **[P6.1b/c/d](P6.1-obligation-bridge.md)** — CIC→IR; the **`sat` gate**; totality | L | Sound `unsat` **and** `sat`. |
| **6** | **`Refute`** ([P6.3](P6.3-certificate-tactics.md)) | M | The differentiator, once it is sound. **Never before P6.1c.** |
| **7** | **[P6.4](P6.4-agent-surface.md)** — MCP, ≤6 verbs, WASM | M | The agent surface. *"Fewer tools perform better."* |
| **8** | **`Simp` / `Induct` / `Instantiate`** ([P6.3](P6.3-certificate-tactics.md)) | L | Where the bet gets tested. |
| **9** | **[P6.5](P6.5-spec-surface.md)** — specs | L | **Test the reduction to P5.2 first.** May correctly cancel. |
| **—** | **[P6.6-probe](../process/quantified-uf-probe.md)** — historical quantified-UF measurement | S | The original collision and Skolemization blockers were superseded. A fresh rerun needs current preregistration; it is not an automatic next action. |

## Kernel prerequisite status

**P6.0 is partial.** Its first seam-fuzz increment and several later kernel
prerequisites are complete, but this does not start P6.1--P6.3.

Landed:

- T6.0.2/TL2.11 explicit strict positivity, retained through recursive-indexed,
  mutual, and nested inductive admission (TL2.12--TL2.14);
- T6.0.3's fixed-seed 768-case four-seam `False`-admission population;
- TL2.6 arbitrary-precision `NatLit(BigUint)` before TL2.7 checked Nat literal
  typing and reduction;
- the separate TL2.10 quotient grammar.

Still open includes generated projection/reduction/eta seam fuzzing under
TL2.15, the accepted prelude classification/discharge boundary, prelude
namespacing and fallibility, printer round-trip assurance, and a kernel
performance baseline. The exact task ledger is [P6.0](P6.0-kernel-trustworthiness.md).

The seam-fuzz starting point was **181 hand-written tests and zero fuzz**. The landed
[768-case seed](../../plan/lean-kernel-seam-fuzz-seed-2026-07-21.md) now covers
the four representable seams below, reruns its summary deterministically, and
rejects a `False` admission in every case. This does not erase the measured
finding: every historical Lean/Rocq kernel bug lived at a **feature seam**, and
the original `False` bug was found by reading the code against the metatheory.

Seams, in priority order:

1. **`Prop` × elimination** — ADR-0165's boundary matrix is the template. It landed
   for the fixed case; generalise it.
2. **universes × inductives**
3. **proof-irrelevance × iota**
4. **literals × reduction** — the original ordering hazard was fixed-width Nat
   storage preceding literal typing. TL2.6 closed it with `NatLit(BigUint)`
   before TL2.7 enabled checked Nat literal semantics; retain that order as a
   regression contract.

The negative class is now live: **"the kernel accepts `False`."** TL2.2--TL2.5
represent, infer, reduce/import, and eta-check projections and structures;
TL2.6--TL2.7 close arbitrary-precision Nat storage and checked semantics.
Generated projection/reduction/eta cases remain the explicit TL2.15 residual,
with every newly admitted seam required to join the same negative class.

## The five things not to get wrong

1. **Delayed assignment** ([architecture §4.3](../design/03-architecture.md)). A
   type-theoretic necessity, not a convenience — you cannot abstract a binder over a
   hole whose context contains it, so `?m := ?n x`. **Every `intro` hits it.** The
   most important thing to lift from Lean; the least obvious.
2. **The depth invariant** — level *N+1* fully assigned before returning to *N*. It
   is what stops a nested `simp` silently solving a sibling goal. Cheap now,
   near-impossible later. Same for **explicit metavariable coupling**.
3. **`check/` depends on the kernel and nothing else.** If a checker ever needs the
   solver, the design is wrong.
4. **`Refute` never ships before P6.1c.** A confident wrong counterexample is worse
   than none.
5. **Goals are data.** Never a pretty-printer an agent must parse back. **0/33
   across 660 attempts** is what inventing a syntax costs.

## What this track must never do

- Make mathlib part of this track's native trusted goal/tactic core. Selected
  pinned mathlib imports belong to the interoperability track as external
  compatibility and theorem-discharge evidence.
- Add a human proof-scripting language.
- Claim `sorry`. **`fail`.**
- Claim we decide more than Z3 (`PLAN.md:2901-2904` settles it).
- Ship a slice without its TCB statement.
- Depend on the Alethe/CPC resolution ([ADR-0166](../../research/09-decisions/adr-0166-alethe-target-reassessment.md)).
- Let a checker grow until it needs its own checker.

## Sizing

**Multiple person-years as a whole.** That is a slicing problem, not a veto — seL4
was ~12–20 person-years **as a monolith**; nothing here is. But the cost is real,
and it belongs in [ADR-0167](../../research/09-decisions/adr-0167-prover-track-entry.md),
not in a working-stance quote.

Each slice pays alone:

- **P6.0** pays whether or not P6.1 ever starts — P3.6/P3.7 need it.
- **P6.1a** pays as a reconstruction refactor *and* as P3.7's T3.7.3.
- **P6.4** pays as picks-and-shovels: *"not one of them builds their own solver;
  all of them rent Z3."*

## Owed

| Item | Status |
|---|---|
| **[ADR-0167](../../research/09-decisions/adr-0167-prover-track-entry.md)** — entry; supersedes the stale "implementing dependent type theory is out of scope" | filed, `accepted` |
| **[ADR-0166](../../research/09-decisions/adr-0166-alethe-target-reassessment.md)** — `lean-smt` uses **CPC, not Alethe**; cvc5's Alethe has **no bit-vectors** | filed, `proposed`; resolve before choosing a new Lean proof route, with priority owned by root `PLAN.md` |
| The prelude-assumption boundary — **65** runtime/type-digested rows; the generated ledger assigns 7 derivable, 41 external, and 17 primitive rows, while accepted TL3.2 classification and discharge remain open | T6.0.6 / TL0.4 / TL3.2 |
| The prover-side generic `Refute` checker/bridge (distinct from existing solver model replay) | P6.1c |
| **What the QF_UF 54% actually reflects** — the previous explanation was false ([note 08's correction](../research/08-solver-automation-assets.md)) | unwritten |
