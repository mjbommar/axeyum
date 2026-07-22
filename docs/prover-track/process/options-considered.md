# Options considered — the design space, and what we chose

The map of what was considered, so the next person does not re-run the track.
Each option records what would change the call.

**Chosen: B** (certificate-first construction), **plus C** (P3.7 continues — it is
not an either/or), with **D** folded in as P6.4 rather than standing alone.
**A and E are refused.**

Current: [`00-thesis.md`](../design/00-thesis.md) (v4),
[`../plan/README.md`](../plan/README.md) (v4), [`../critique/`](critique/).
Sections below were first written under v3 ("do not build") and are corrected
where that framing leaked.

> **Current-boundary correction (2026-07-21):** the runtime-derived ledger now
> contains 65 prelude assumptions, not the historical 64 call-site count, and
> T6.0.3 now runs a deterministic 768-case generated gate over the four
> representable kernel seams. Positivity, prelude discharge, projection/eta,
> quotient, and typed-literal work remain open; the historical argument below
> is preserved rather than silently rewritten.

---

## A — A general proof assistant (elaborator + tactics + library)

**Refused. Permanently.**

Mathlib's network effect is real, compounding, and unbeatable by us. Rocq spent
~30 years and Lean 4 + Mathlib is in the hundreds of person-years; seL4 was
~12–20 person-years for **8.7k SLOC**. We would be building the lower half of an
ITP whose upper half we could never populate.

The counter-evidence that made this worth checking at all — Dafny's 1,221-line
library beating Lean's `grind` 38.9% to 32.4% on miniF2F-Dafny — is real but does
**not** rescue this option. It shows library scale is not the sole active
ingredient on arithmetic goals; it does not show a library is unnecessary, and
it is a *mathematics* benchmark being used to argue about *software*.

**Reopens if:** never. If this looks attractive again, re-read
`../critique/iteration-1.md`.

---

## B — Certificate-first construction ("tactics emit certificates, not terms")

**TAKEN.** v3 refused this; v4 takes it. See [`00-thesis.md`](../design/00-thesis.md).

The idea: generalize axeyum's existing discipline upward. A tactic is not a
function that builds a proof term (de Bruijn) nor a function over an abstract
`thm` (LCF); it is an **untrusted procedure emitting a certificate**, plus a small
checker that turns it into a kernel-checked term. This is what reconstruction
already does for certificates about *formulas*; the move is certificates about
*goals*.

It keeps the TCB flat, makes every decision procedure a tactic for free, is
agent-shaped (propose/dispose), and degrades honestly (`fail`, not `sorry`). Note
01 found the precedents exist but **unassembled** — DRAT/LRAT, Alethe/LFSC, Rocq's
reflective `ring`/`lia`, Sledgehammer's shape — with λΠ-modulo/Dedukti as the
substrate candidate. Nobody has built the general version.

### Why v3 refused it, and why each reason failed

1. **"The 0% column — the layer would be a shell over a hole."**
   **Backwards.** A goal layer is the mechanism by which an undecidable goal
   becomes decidable obligations. `pdr_lia.rs:40-46` is the working proof: PDR
   *synthesizes* an invariant, then discharges three obligations "over ℤ, each
   decided independently by the trusted decider `check_auto`" — quantifier-free,
   gated by `verify_invariant` (`:716`). The quantified problem is never decided;
   it is **decomposed**. The 0% column is the *reason for* the layer.
2. **"It does not escape unification, only relocates it."** True, and it stands as
   a **cost**, not a veto. Note 01: metavariables are unavoidable for
   goal-directed proof; *dependent* metavariables are a fragment choice. P6.2 is
   priced accordingly rather than pretending.
3. **"The IR mismatch is XL and unstarted."** True as a monolith. **Sliced**
   (P6.1a/b/c/d), starting where reconstruction already round-trips — pure
   de-risking with no new capability, which is exactly how you find out cheaply
   whether the seam exists.
4. **"Reconstruction is the known SMT→ITP bottleneck (lean-smt 71% vs Ethos 98%)."**
   Real, and it is an argument about *format and kernel speed*, not about whether
   a goal layer should exist. It feeds [ADR-0166](../../research/09-decisions/adr-0166-alethe-target-reassessment.md).

### The honest open risk

**Note 07 says reconstruction is ad-hoc**: `scan_proof_fragment` matches ~40
bespoke `ProofFragment` shapes named after individual benchmarks, and its control
flow "runs backward from the answer." If that cannot be extracted into a reusable
bridge, **P6.1a — the first slice — is a fiction**, and the slice plan's opening
move fails. That is precisely why P6.1a is scheduled first: it is the cheapest
place to be wrong.

## C — Lean tactic backend (P3.7) — *the plan of record*

**Keep — and note it is not an alternative to B.** v3 treated C and B as
competing; they are not. C makes axeyum useful *inside* Lean. B makes axeyum
useful *without* Lean. Both ship.

Note 04's finding is real and argues for C: *"Not one of them builds their own
solver. All of them rent Z3."* Be the thing they rent.

**But C cannot substitute for B**, which is the hole v3 missed. P3.7 makes **Lean
own the goal** — the elaborator, the proof state, the decomposition. So it
delivers nothing without a Lean toolchain, nothing in WASM or an agent's own
process, nothing when the goal is not already stated in Lean, and no way to make
progress on a goal we cannot one-shot decide. *(This is v4's load-bearing claim
and it is the first thing round 3 was asked to attack. If it is false, v4
collapses and v3 was right.)*

Two of this track's findings land on C directly:

- **[ADR-0166](../../research/09-decisions/adr-0166-alethe-target-reassessment.md)** — `lean-smt` uses **CPC, not Alethe**; cvc5's Alethe has **no bit-vectors**. P3.7 aims at Lean through the format Lean's own SMT tactic declined, in a fragment it doesn't cover, while QF_BV is our strength. **Track 6 must not depend on this resolving.**
- **Calibration.** Sledgehammer's ATP-free baseline is 46.8% vs 72.1% full — solver strength is *second-order* behind premise selection. `bv_decide` already occupies QF_BV-in-Lean, bottlenecked on **kernel reduction speed, not solve time**. "2× Z3" does not automatically convert into Lean value; the right head-to-head is **certificate size**, not PAR-2.

---

## D — Agent surface only (MCP + structured errors + WASM)

**Folded into the track as P6.4 — not a standalone alternative.**

v3 proposed this *instead of* a goal layer, which was the refusal wearing a
deliverable. In v4 it is a phase: valuable alone, and simultaneously the cheapest
falsification of the thesis.

Sized S/M. Our hard rules (determinism, `unknown` as a value, no global mutable
state, explicit seeds/limits, incrementality) already produce everything an agent
needs; **the gap is exposing it, not producing it**. Luck rather than foresight —
those rules came from reproducibility and soundness discipline.

**The experiment must not be rigged.** Run it against a `lean4check`-shaped loop
(87% on 189 proof-engineering tasks, **one tool**) on a **named, search-heavy** set
— note 05 says a rich surface pays "little for mechanical tasks and a lot for
search-heavy ones," so a mechanical benchmark tests the case where the surface is
known to lose. Both branches carry the same burden of proof.

If the loop matches it, **the surface is not the product — say so**, and the rest
of the track has to justify itself on decomposition alone (P6.6).

---

## E — Do nothing

**Refused**, and it is the only option this track definitively killed.

Doing nothing left in place at this decision point: a kernel that had admitted
`False`, the then-under-counted prelude-assumption boundary, a positivity checker
enforced only *vacuously* and liable to go live-broken when the next inductive
gap lands, `Lit::Nat` truncation guarded by nothing, no generated seam fuzz in a
trusted component, a keystone format bet that might be aimed at the wrong
target, and `sat` results with no trust story at all. The correction above records
the two boundaries subsequently closed without weakening the residual case.

"No prover" is not "no work." Gate 0 exists because doing nothing is the one
answer the evidence rules out.

---

## F — Close the 0% column and the trust ledger *instead of* building

**Refused as an alternative; retained as parallel work.**

v3 made this the recommendation: don't build, go do theory. The framing was wrong
in one specific way, and it is the same error twice — **it treats the 0% column as
a precondition for a goal layer when the goal layer is how you attack it.**

`pdr_lia.rs:40-46` settles it: PDR never decides quantified LIA. It *synthesizes*
an invariant with untrusted search and discharges quantifier-free obligations
through `check_auto`, gated by `verify_invariant`. Decomposition is what converts
an undecidable goal into decidable ones. That is the mechanism, and P6.6 tests
whether it generalizes.

The work itself remains real and is owed regardless — it just is not a substitute:

| Item | Owner | Relation to Track 6 |
|---|---|---|
| Quantified **UF** 0/5 (**not** quantified LIA — see above) | Track 2 | P6.6 attacks it by decomposition; Track 2 attacks it by deciding. Both, not either |
| Trusted-reduction ledger — **6 of 14** `TrustId` variants open; `IntBlast`, `XorGaussian` "unsound with no recovery" at pedantic 3 | Track 3 | The layer inherits every hole |
| **65** unproven prelude assumptions (64 arithmetic/integer + string `append`) | Track 3 / **T6.0.6** / TL3.2 | Bounds what "kernel-checked" means; TL0.4 now freezes names/types but does not prove them |
| `sat` has no trust story | **P6.1c** | Counterexamples are unsound until it lands |

*(v3 cited "6/14" here. Uncited and wrong: `trust.rs` defines 13 `TrustId`
variants. Corrected.)*

## The option nobody proposed, recorded for completeness

**A different type theory.** Every option above assumes CIC, because that is what
`axeyum-lean-kernel` implements. The P0 was not a Lean-compatibility defect — it
was an inconsistency in *the theory we chose*: proof irrelevance + impredicative
`Prop` + unrestricted large elimination.

A system designed for **decidable software obligations** and **agent drivers**
might not want impredicative `Prop`, proof irrelevance, or a Mathlib-compatible
universe hierarchy at all. Those exist to support a mathematics library we have
explicitly refused to build.

Nobody costed this, and it is not a recommendation — the Lean-compatible
acceptance criterion is a genuine asset (an export target, an interop story,
kernel diversity in the north star's sense), and abandoning it to design a theory
from scratch is how research projects disappear.

But it is the one question this track never asked, and it is the one where
"Lean-compatible, not Lean-copying" would actually bite. Worth an hour before
anyone reopens B.
