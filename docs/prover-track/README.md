# Prover Track — a certificate-first proof assistant on axeyum

**Status: designed, not built.** Entry ADR:
[ADR-0167](../research/09-decisions/adr-0167-prover-track-entry.md).

> **A tactic is an untrusted procedure that emits a certificate. A small checker
> turns it into a kernel-checked term. The tactic never enters the TCB.**
>
> Reconstruction already does this for certificates about **formulas** (DRAT/LRAT →
> CIC terms). This does it for certificates about **goals**.

## Read in this order

| | |
|---|---|
| **1** | **[`design/03-architecture.md`](design/03-architecture.md)** — **what it is.** Layers, `Goal`/`Hole`, the `Step` certificate protocol, delayed assignment, crate layout. |
| **2** | **[`plan/README.md`](plan/README.md)** — **how to build it.** Build order, the first commit, the five things not to get wrong. |
| **3** | **[`design/00-thesis.md`](design/00-thesis.md)** — **why.** The argument, the constraints, the open bet. |
| **4** | **[`REFERENCES.md`](REFERENCES.md)** — 87 papers, 29 repos, 265 URLs, **with the gaps named**. |

[`SYNTHESIS.md`](SYNTHESIS.md) is the one-file summary of all four.

## Why the layer must exist

`auto.rs:5244` declines a residual quantifier, and its comment is a **correctness
statement, not a TODO**: *"Quantifiers left after instantiation … cannot be decided
by the quantifier-free engines."* Instantiation only **weakens** — so **the solver
cannot soundly guess an instantiation depth.**

Someone must choose it. Not the solver (unsound). Not the kernel (it does not
search). **The prover.**

> **A correct fragment boundary is what creates the need for a layer above it.**
> The solver declines honestly; the prover is where the untrusted choice lives;
> the certificate is what makes the choice safe.

A human writes `induction n`. An agent proposes a depth. Both are checkable.

## Phases

| Phase | | Size |
|---|---|---|
| **[P6.0](plan/P6.0-kernel-trustworthiness.md)** | Kernel trustworthiness — **start here** | M |
| **[P6.1](plan/P6.1-obligation-bridge.md)** | The obligation bridge (CIC ⇄ IR), sliced a/b/c/d | XL → sliced |
| **[P6.2](plan/P6.2-goals-and-holes.md)** | Goals, holes, unification | L |
| **[P6.3](plan/P6.3-certificate-tactics.md)** | Certificate-first tactics | L → per tactic |
| **[P6.4](plan/P6.4-agent-surface.md)** | Agent surface (MCP, ≤6 verbs, WASM) | M |
| **[P6.5](plan/P6.5-spec-surface.md)** | Definitions and specs | L |

## What this track already produced

Findings that stand on their own, whether or not the prover is built:

| Finding | Where |
|---|---|
| **A P0 unsoundness: the kernel admitted `theorem bad : False`** — found, reproduced, fixed | [`research/09`](research/09-P0-kernel-unsoundness.md); ADR-0165 |
| **[ADR-0166](../research/09-decisions/adr-0166-alethe-target-reassessment.md)** — `lean-smt` uses **CPC, not Alethe**, and cvc5's Alethe has **no bit-vectors**. A `[critical path]` keystone may be aimed wrong. **Urgent, and independent of this track.** | filed |
| **64 unproven prelude axioms** — ℝ's carrier is an opaque `Declaration::Axiom`; Lean accepts axioms *vacuously*, so the real-Lean gate cannot catch a false one | [`research/06`](research/06-kernel-gap-analysis.md) → T6.0.6 |
| **Positivity is enforced only *vacuously*** — land the next inductive gap and the rejection vanishes with no checker behind it | T6.0.2 |
| **The `!fn_app_0` Ackermann collision** — blocks every quantified-UF goal with a genuine (non-predicate) function; 7-line repro | [`process/quantified-uf-probe.md`](process/quantified-uf-probe.md) |
| **`sat` has no trust story** — the kernel gate covers `unsat` only | [`research/08`](research/08-solver-automation-assets.md) → P6.1c |

## Research

| Note | What it settled |
|---|---|
| [`01-itp-anatomy.md`](research/01-itp-anatomy.md) | The design space above a kernel. Metavariables are unavoidable. Coq: **78 critical bugs, 20 in conversion machines** — the Poincaré bill. Kernel bugs live at feature seams. |
| [`02-ai-assisted-proving.md`](research/02-ai-assisted-proving.md) | The agent loop won. **Verifier throughput is the scarce resource.** A rival ITP/library is DOA. |
| [`03-atp-itp-seam.md`](research/03-atp-itp-seam.md) | **CPC, not Alethe** → ADR-0166. Instability is a property of *undecidable encodings*: `KomodoD` 5.01% vs `KomodoS` **0.52%**. |
| [`04-software-ir-verification.md`](research/04-software-ir-verification.md) | The graveyard died of *assuming the spec is free*. **Verification Theatre**: 4 vulns **inside** verified code, from an undocumented boundary. |
| [`05-education-and-agentic.md`](research/05-education-and-agentic.md) | An IDE models a cursor; **an agent models a search over states.** Counterexample-first is unoccupied. |
| [`06-kernel-gap-analysis.md`](research/06-kernel-gap-analysis.md) | 64 axioms; vacuous positivity; `Lit::Nat` truncation; **zero fuzz**. |
| [`07-reconstruction-assets.md`](research/07-reconstruction-assets.md) | The kernel is a real, theory-neutral asset. Above it is greenfield. |
| [`08-solver-automation-assets.md`](research/08-solver-automation-assets.md) | The IR mismatch: **zero CIC→IR functions**. `sat` has no trust story. |
| [`09-P0-kernel-unsoundness.md`](research/09-P0-kernel-unsoundness.md) | The `False` incident, and why three gates missed it. |
| [`10-autoformalization.md`](research/10-autoformalization.md) | **0/33 across 660 attempts** — never invent a syntax. **Scope laundering 15.3–52.5%.** |
| [`11-dedukti-and-substrates.md`](research/11-dedukti-and-substrates.md) | Dedukti **grows** the TCB — rejected. *Don't build the universal thing; build the bridge someone wants.* MM0's split **is** this design. |
| [`12-elaboration-egraphs-fmf.md`](research/12-elaboration-egraphs-fmf.md) | **Delayed assignment** is the thing to copy. egg's explainer is **O(n log n)** — `simp`'s cost is the `Eq.trans` spine, not the chain. |

## Process record

[`process/`](process/README.md) — diary, four adversarial reviews, options
considered. **Not a plan.** Read it only to trace where a constraint came from.
