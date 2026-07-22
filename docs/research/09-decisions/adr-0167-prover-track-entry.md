# ADR-0167: Enter the proof-construction rung — scope, and supersede the stale exclusion

Status: accepted
Date: 2026-07-15

## Context

`docs/research/00-orientation/north-star.md:53` states the process: *"Out of scope:
Commitments or schedules for any horizon rung (**each gets its own ADR**)."* This
is that ADR. It was never written because the rung was never entered.

The corpus is currently **self-contradictory** on whether the rung may be entered
at all:

| Document | Says |
|---|---|
| `01-foundations/proof-assistant-lessons.md:6-19` | Purpose is to learn from proof assistants *"**without turning Axeyum into a proof assistant**"*; **"Implementing dependent type theory"** is out of scope. |
| `00-orientation/mission-and-scope.md:60-65` | *"A fully general / dependent-type proof assistant"* is out of scope **"for the current phase"** — *"these are **later destinations**, not permanent exclusions."* |
| `00-orientation/north-star.md:125` | *"...and **eventually dependent-type proving**."* |

**The first row is stale and must be superseded**: axeyum *has* implemented
dependent type theory. `axeyum-lean-kernel` (ADR-0036) is CIC — universes,
dependent `Pi`, inductives with recursors, definitional equality, a trusted
admission gate. The note was written before the kernel shipped and was overtaken
by events; it now forbids something we did.

The research supporting this ADR is [`docs/prover-track/`](../../prover-track/README.md)
— 12 research notes, three independent adversarial reviews, four thesis drafts.
Read [`SYNTHESIS.md`](../../prover-track/SYNTHESIS.md) first.

## Decision

**Enter the rung for a *certificate-first goal layer*, scoped as below, and
supersede `proof-assistant-lessons.md`'s "implementing dependent type theory" 
exclusion as overtaken by ADR-0036.**

A **goal layer** is: a representation of a proof obligation with holes, plus
tactics that are **untrusted procedures emitting certificates**, plus **small
checkers** that turn certificates into kernel-checked terms. Tactics never enter
the TCB.

### In scope

- Goals as **data**, forkable, with tracked holes (`fail`, never `sorry`).
- Certificate-first tactics, each serving **one consumer we can name**.
- A CIC ⇄ `axeyum-ir` bridge over a **published, declining** fragment.
- An agent-facing surface (narrow — "fewer tools perform better").

### Out of scope for Track 6 ownership

- **A separate native mathematics library.** Track 6 does not grow a competing
  mathlib. Selected upstream theorem imports and the full pinned-mathlib
  compatibility build are owned by ADR-0345's L3/L10 program; Track 6 consumes
  theorem identities and checked terms through that boundary.
- **A novel human-facing proof language.** Track 6's stable surface is goals,
  holes, steps, and certificates. Native Lean-compatible syntax/macros and tactic
  scripts are owned by L6/L5.8, so this refuses invention of an Axeyum-only
  language rather than source compatibility. The low-resource-language evidence
  remains a warning against novel syntax
  ([`research/10`](../../prover-track/research/10-autoformalization.md)).
- **A universal proof substrate.** *Don't build the universal thing; build the
  bridge someone wants* ([`research/11`](../../prover-track/research/11-dedukti-and-substrates.md)).
- **A Dafny/Verus.** We do not sell push-button verification over an undecidable
  fragment.

### The gates — this ADR authorizes P6.0 only

**P6.0 (kernel trustworthiness) is authorized unconditionally and is exempt from
this rung** — it is a soundness obligation on a shipped component (ADR-0165), and
P3.6/P3.7 depend on it regardless.

**The consumer is named**: the project owner, who set the framing —
*Lean-compatible, not Lean-copying; narrow scoping is bad.* The first obligation
set is the five quantified-UF goals plus a SymCrypt-class BV slice (P6.1e measures
it). **This ADR enters the rung.**

**The phases below are ordered by risk, not by permission.** Each is a slice that
lands alone; a slice that stops paying is where we stop, and what shipped keeps
working. That is a sequencing discipline, not a referendum:

1. **P6.6-probe — a *measurement*.** **Fix the `!fn_app_0` Ackermann naming collision**, then
   implement Skolemization, then re-run the five quantified-UF goals, then publish
   the number. (Hand-Skolemizing PUZ001+1 and running it exposed the collision:
   Skolem functions are sort-valued functions under quantifiers, exactly the shape
   that trips it. Skolemization alone is **necessary but not sufficient** — and it
   **leaves EPR**, the only quantified-UF fragment where carrier-bounding is sound
   for `unsat`.) **Report instantiation rounds and term depth**: a "decides at
   depth *k*" result is a fact about *k*.
2. **P6.6-paper** (a week) — write the decomposition by hand for one goal we
   *demonstrably* cannot do.
3. **P6.1b** — CIC → IR for a named starter fragment.
4. **P6.4** — beat a `lean4check`-shaped loop on a named, search-heavy set.

**A slice that fails re-scopes the next one**; it does not close the rung. The
question "should this exist" is answered — what remains is what it should be, and
the phases are ordered so the cheapest information comes first.

**One exception, stated so it is not a contradiction:** the MCP server (T6.4.1-3)
ships regardless of K1 — it is picks-and-shovels, sized S/M, and note 04's finding
is *"not one of them builds their own solver; all of them rent Z3."* **Shipping a
tool is not entering the rung.** Everything else stops.

## Evidence

**For:**

- **P3.7's only input is a completed `unsat`** (`P3.7-lean-reconstruction.md`). It
  has no goal, no holes, no representation of *not yet knowing* — a
  proof-**exporter**. When axeyum returns `unknown`, it has nothing to do. P5.2
  cannot fill the gap: finite-and-decidable by construction, "recursion declined
  honestly in v1" (`P5.2:33`). **The residue is machine-found decomposition
  outside the decidable fragment.**
- **We are a rare genuinely independent kernel** — `coqchk` links
  `rocq-runtime.kernel`, the kernel it checks; `lean4lean`'s own README says *"not
  really an independent implementation."* This argues directly for P3.7 and for
  keeping imported declarations outside Track 6 ownership: ADR-0345 may feed the
  checker, while this rung remains responsible for goal construction and checked
  certificate consumption.
- **MM0's producer/consumer split is this design**, stated independently by
  Carneiro. **"Scope laundering" at 15.3–52.5%** — models claiming formal grounding
  without running the solver — makes the certificate the only thing separating a
  proof from a claim of one.
- **Library import and re-elaboration dominate workflow cost.** The older
  “nothing to import” premise is superseded by ADR-0345's versioned declaration
  importer and selected theorem-base plan; the cost evidence now motivates
  content-addressed imports and caches rather than a permanent import ban.

**Against — recorded, because this ADR should be refusable:**

- **The search premise is open.** Certificate-first is a *checking* discipline; it
  presumes a certificate exists to emit. Nothing in the design says how to **find**
  a decomposition. PDR is the one precedent and `TransitionSystem` *donates* its
  schema. **This is what the gates test.**
- **Cost.** Multiple person-years as a whole; seL4 was ~12–20 person-years for 8.7k
  SLOC. CLAUDE.md's *"big tasks get broken down"* is an **execution** stance and
  does not select the goal — it would equally justify Mathlib, which we refuse.
  **This ADR is where that argument belongs, and it is why the gates come first.**
- **The evidence previously offered against is invalid, and so was the evidence
  for.** "Quantified UF 0/5" is `Unsup=5, PAR-2=0.000` — five *declines*, three for
  want of Skolemization, one a parser rejection of arity-1 sorts. It measured our
  plumbing. **And the first fix is not sufficient**: hand-Skolemizing exposes a
  fourth blocker, an Ackermann symbol collision on any quantified goal with a
  genuine non-predicate function. The honest state is *unmeasured*, not *hard* —
  and not *easy* either.
  ([`P6.6-paper-attempt.md`](../../prover-track/process/quantified-uf-probe.md).)

## Alternatives

1. **Stay at P3.7 only** — be the Lean tactic backend. Real, and it continues
   regardless; C and B are not an either/or. But it delivers nothing when the goal
   is not already stated in Lean and nothing when we cannot one-shot decide.
2. **Refuse permanently** (thesis v3). Rejected: it reasoned "person-years,
   therefore no," which CLAUDE.md's working stance forbids, and it rested on the
   0/5 evidence now known to be invalid.
3. **Dedukti / λΠ-modulo as substrate.** Rejected: it **grows** the TCB (kernel +
   rewrite theory + external confluence + termination + adequacy proof), its export
   weakens to constructive simple type theory, no BV theory exists, and CoqInE has
   chased CIC universe polymorphism since ~2012.
4. **A general proof assistant inside Track 6.** Rejected as an ownership
   collapse. Track 6 supplies the one goal/tactic engine; the broader compatible
   source/workflow/runtime system is independently staged by ADR-0345 and the
   Lean-system implementation plan.

## Consequences

- **Easier:** the corpus stops contradicting itself; P6.0 proceeds with an owner;
  the cost argument has a home.
- **Harder:** every phase above P6.0 now owes a gate result before it starts. That
  is deliberate — draft 1 scheduled both deciding experiments *after* the spend
  they justified.
- **Revisited when:** any gate fails, or the search premise is settled either way.
- **Supersedes:** `proof-assistant-lessons.md:19`'s "implementing dependent type
  theory" exclusion (overtaken by ADR-0036). That note's *architectural* lessons
  stand; only the scope line is withdrawn.
- **Does not touch:** ADR-0011/0012 (DRAT/LRAT), ADR-0036 (the kernel), or
  [ADR-0166](adr-0166-alethe-target-reassessment.md) — Track 6 must **not** depend
  on the Alethe/CPC resolution.
- **Interlocks with:** [ADR-0345](adr-0345-preregister-lean-system-interoperability.md),
  which owns declaration/library import, native source compatibility,
  modules/packages/editor/runtime integration, and mathlib build compatibility.
  It reuses this ADR's goal/tactic engine and does not create a second one.

## Boundary

Stated per *Verification Theatre*'s lesson — the undocumented boundary is what
bites.

- **In the TCB today:** `axeyum-lean-kernel` (including the historical
  2026-07-15 `False`-admission defect and its fix), the checkers, the current
  **64 arithmetic/integer plus one string prelude assumptions**, `rustc`, and
  the still-open reduction-ledger entries.
- **Not in the TCB:** the solver, the translator, the search, any agent, any tactic.
- **Not covered:** `sat` results until P6.1c; anything outside the published
  fragment; whether the fragment covers anything anyone wants (unmeasured until
  P6.1e).
