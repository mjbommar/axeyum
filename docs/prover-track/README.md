# Prover track — certificate-first proof construction

The design is accepted by
[ADR-0167](../research/09-decisions/adr-0167-prover-track-entry.md), but its
implementation state is split:

| Layer | Current state | Evidence / next authority |
|---|---|---|
| Independent Lean-core checker and fail-closed importer | Built for selected, explicitly gated profiles | [`axeyum-lean-kernel`](../../crates/axeyum-lean-kernel/README.md), [`axeyum-lean-import`](../../crates/axeyum-lean-import/README.md), [generated compatibility registry](../plan/generated/lean-complete-parity.md) |
| P6.0 kernel trustworthiness prerequisites | Partial, with major slices landed | strict positivity, arbitrary-precision Nat literals, recursive/mutual/nested inductives, and the first seam-fuzz population are complete; generated projection/eta seams and other P6.0 residuals remain |
| P6.1 CIC/IR obligation bridge | Not implemented as the planned `axeyum-bridge` boundary | [P6.1](plan/P6.1-obligation-bridge.md) |
| P6.2 goals/holes/unification and P6.3 tactics | Not started; no `axeyum-goal` crate exists | [generated A5 status](../plan/generated/lean-complete-parity.md#a0-a11-behavioral-axes), [P6.2](plan/P6.2-goals-and-holes.md), [P6.3](plan/P6.3-certificate-tactics.md) |
| P6.4 agent surface and P6.5 spec surface | Design only | [P6.4](plan/P6.4-agent-surface.md), [P6.5](plan/P6.5-spec-surface.md) |

So Axeyum already has proof reconstruction and an independent selected-profile
kernel; it does **not** yet have the native interactive goal state, holes,
unifier, or certificate-tactic protocol described by this track. Full Lean 4.30
parity is also explicitly unestablished. Project-wide priority remains in root
[PLAN.md](../../PLAN.md), not in this track's build-order documents.

> **A tactic is an untrusted procedure that emits a certificate. A small checker
> turns it into a kernel-checked term. The tactic never enters the TCB.**

Reconstruction already applies that discipline to certificates about formulas.
This track proposes applying it to proof goals.

## Read in this order

| | |
|---|---|
| **1** | This page for the built/planned boundary. |
| **2** | [`design/03-architecture.md`](design/03-architecture.md) for the accepted design. It is a design record, not an implementation claim. |
| **3** | [`plan/README.md`](plan/README.md) for dependency order and the current P6.0 prerequisite summary. Root `PLAN.md` still controls scheduling. |
| **4** | [`SYNTHESIS.md`](SYNTHESIS.md) for the research argument and method record. |
| **5** | [`REFERENCES.md`](REFERENCES.md) for the bibliography and named research gaps. |

## Why a layer above the solver is still needed

The solver correctly declines residual quantifiers that its quantifier-free
engines cannot decide; see the current comment in
[`auto.rs`](../../crates/axeyum-solver/src/auto.rs). Instantiation can weaken a
formula, so an incomplete instantiation pass does not license a definitive
verdict. A human or search agent may choose a depth, witness, motive, or split,
but the resulting proof step must remain independently checkable.

That separation is the design claim:

- the solver may search and return `Unknown` when its route is incomplete;
- a prover may make untrusted search choices above that boundary;
- small step checkers plus `axeyum-lean-kernel` validate what those choices
  establish.

## Planned phases

| Phase | Purpose | Current boundary |
|---|---|---|
| [P6.0](plan/P6.0-kernel-trustworthiness.md) | Kernel trustworthiness | Partial; several major tasks are done, residuals remain |
| [P6.1](plan/P6.1-obligation-bridge.md) | CIC ⇄ IR obligation bridge and checked refutation boundary | Planned |
| [P6.2](plan/P6.2-goals-and-holes.md) | Goals, holes, delayed assignment, unification | Not started |
| [P6.3](plan/P6.3-certificate-tactics.md) | Certificate-first tactics | Not started |
| [P6.4](plan/P6.4-agent-surface.md) | Bounded agent-facing surface | Planned |
| [P6.5](plan/P6.5-spec-surface.md) | Definitions and specifications | Planned |

## Findings and their current disposition

| Finding | Current disposition |
|---|---|
| The kernel once admitted `theorem bad : False` | Fixed by ADR-0165; retained as a negative regression. See [`research/09`](research/09-P0-kernel-unsoundness.md). |
| Prelude assumptions form part of the trust boundary | Still material. The [65-row generated ledger](../plan/generated/lean-axiom-ledger.md) now assigns 7 derivable-theorem, 41 external-assumption, and 17 primitive-interface rows; accepted TL3.2 classification/discharge work remains open. |
| Strict positivity was previously enforced only through a narrower rejection | Resolved by T6.0.2/TL2.11 before recursive-indexed, mutual, and nested admission widened. See [P6.0](plan/P6.0-kernel-trustworthiness.md). |
| Fixed-width Nat literals were an ordering hazard | Resolved in TL2.6/TL2.7 with `NatLit(BigUint)` storage and checked literal semantics. |
| Repeated function elimination could collide on `!fn_app_0` across result sorts | Resolved by integrated commit `c223ed8d4`, which derives the fresh identity from the source term and retains a repeated-elimination regression. |
| A generic prover-side `Refute` trust bridge is absent | Still open as P6.1c. This is narrower than saying solver `sat` has no trust story: supported solver models already replay against original terms, and selected quantified routes carry checked model certificates. |
| Alethe versus CPC for the Lean route remains an explicit decision | [ADR-0166](../research/09-decisions/adr-0166-alethe-target-reassessment.md) remains proposed. |

## Research and process records

The notes under [`research/`](research/) and [`process/`](process/README.md)
preserve the evidence and adversarial review that produced the design. They are
dated records: source line numbers, solver measurements, and implementation
status inside them may describe their audit point. Use the current source,
generated registries, this front door, and root `PLAN.md` for present tense.
