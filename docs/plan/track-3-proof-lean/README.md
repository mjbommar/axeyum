# Track 3 — Proofs & Lean

Take axeyum from "DRAT for the clausal layer (+ a bit-blast miter)" to
"machine-checkable, Lean-consumable proofs for full SMT queries." This track owns
the **second load-bearing front (reduction certificates)** and the **proof-format
keystone (the Alethe emitter)**. It can run largely in parallel with Track 1 — it
does not need the performance work.

Reference reading: [`../references/proof-and-lean.md`](../references/proof-and-lean.md).

## Phases

| Phase | Title | Size | Depends on | Note |
|---|---|---|---|---|
| [P3.0](P3.0-trust-ledger.md) | Reduction trust ledger (TrustId + pedantic levels) | S | — | makes the trust surface countable; do first |
| [P3.1](P3.1-lrat.md) | LRAT clausal upgrade (+ in-tree check_lrat) | S–M | — | what Lean SAT importers want |
| [P3.2](P3.2-alethe-ir.md) | Alethe term/proof IR + emitter (`axeyum-alethe`) **[critical path]** | M | P3.1 | the keystone |
| [P3.3](P3.3-alethe-qfbv.md) | Alethe for QF_BV (bitblast_* + CNF rules + resolution/drat; Carcara CI) | M | P3.2 | first SMT-level proof |
| [P3.4](P3.4-embedded-checker.md) | Embedded Alethe checker subset (self-checking) | M | P3.3 | trusted-checking above the clausal layer |
| [P3.5](P3.5-reduction-proofs.md) | Alethe for reductions (arrays → Ackermann → int-blast) | M (per theory) | P3.2, Track 2 lazy reductions | retires trust-ledger entries |
| [P3.6](P3.6-lean-kernel.md) | In-tree Rust Lean kernel (`axeyum-lean-kernel`, from nanoda) | L | — | Lean-grade trusted checker, no toolchain |
| [P3.7](P3.7-lean-reconstruction.md) | Alethe→Lean reconstruction (proof terms) | L | P3.3/P3.5, P3.6 | the capstone |
| [P3.8](P3.8-interpolation.md) | Craig interpolation (proof-based, theory-aware) | L | P3.2, P3.5, LRA Farkas | new feature column; read off the checked proof; **enables CHC ([P4.6](../track-4-usecases-frontend/P4.6-chc-horn.md))** |

## Order
`P3.0 → P3.1 → P3.2 (keystone) → P3.3 → P3.4`, with `P3.5` retiring ledger entries
as Track 2 theories gain lazy/checkable reductions, and `P3.6 → P3.7` as the
multi-month Lean capstone. P3.0–P3.3 can start immediately, in parallel with all
of Track 1. **P3.8 (interpolation)** rides P3.2/P3.5 (it reads interpolants off
the *already-checked* proof) and is the prerequisite lemma engine for CHC/PDR
([P4.6](../track-4-usecases-frontend/P4.6-chc-horn.md)) — the cheapest first slice
(Farkas interpolants for LRA) reuses certificates that already exist in tree.

## The trust-surface invariant
Every reduction is either **certified** (an Alethe step a checker re-derives) or a
**ledgered `TrustId`** with a pedantic level. "Modulo trusted reduction" becomes a
countable list that this track drives to zero. See
[P3.0](P3.0-trust-ledger.md).
