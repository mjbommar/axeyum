# Architecture — a certificate-first proof assistant

**This is the design document.** What the system is, how it is layered, what the
data structures are, and what makes it different from Lean and Rocq.

Rationale and evidence: [`00-thesis.md`](00-thesis.md).
Sources: [`../REFERENCES.md`](../REFERENCES.md).

---

## 1. The idea in one paragraph

Lean and Rocq are **de Bruijn** systems: a tactic is a program that *builds a proof
term*, and the kernel checks the term. Isabelle and HOL Light are **LCF** systems:
a tactic is a function over an abstract `thm`, and there is no artifact at the end.

Axeyum takes a third position it already runs everywhere else:

> **A tactic is an untrusted procedure that emits a certificate. A small checker
> turns the certificate into a kernel-checked term. The tactic never enters the
> TCB.**

Reconstruction already does exactly this for certificates about **formulas**
(DRAT/LRAT → CIC terms). The system below does it for certificates about **goals**.

## 2. Why this shape, and not Lean's

**Because a correct fragment boundary creates the need for a layer above it.**

`auto.rs:5244` declines a residual quantifier, and its comment is a correctness
statement rather than a TODO: *"Quantifiers left after instantiation ... cannot be
decided by the quantifier-free engines."* Instantiation only **weakens**, so a
residual quantifier licenses no verdict. **The solver cannot soundly guess an
instantiation depth.**

Somebody has to choose the depth, the motive, the case split, the witness. That
choice is:

- **not the solver's** — it would make it unsound;
- **not the kernel's** — it does not search;
- **the prover's.** A human writes `induction n`. An agent proposes a depth. The
  **certificate is what makes either one safe.**

That is the whole architecture, and it is why the design is *not* "Lean in Rust."

## 3. The layers

```
   ┌──────────────────────────────────────────────┐
   │  agent / human                                │  untrusted
   │  proposes: motives, depths, witnesses, splits │
   ├──────────────────────────────────────────────┤
   │  GOAL LAYER            (axeyum-goal)          │  untrusted
   │  Goal · Hole · forkable state · tactics       │
   │  tactics emit Step certificates               │
   ├══════════════════════════════════════════════┤
   │  CHECKERS              (axeyum-goal::check)   │  ★ TRUSTED ★
   │  one small checker per Step kind              │
   ├──────────────────────────────────────────────┤
   │  axeyum-lean-kernel    (CIC)                  │  ★ TRUSTED ★
   └──────────────────────────────────────────────┘
                    ▲ bridge (untrusted)  ▼
   ┌──────────────────────────────────────────────┐
   │  axeyum-solver · axeyum-egraph · pdr/imc/chc  │  untrusted
   │  produces: Alethe/LRAT, egg explanations,     │
   │            invariants, models                 │
   └──────────────────────────────────────────────┘
```

**The TCB is two boxes**: the checkers and the kernel. Everything that *searches*
is outside it — the solver, the e-graph, PDR, the bridge, the agent, every tactic.

Contrast: in Lean, a buggy tactic produces a bad term the kernel rejects — safe but
opaque. Here a buggy tactic produces a bad **certificate** the checker rejects, and
the checker can say **which step and why**.

## 4. The core data structures

### 4.1 `Goal`

```rust
/// A proof obligation. Data, not text — an agent never parses a pretty-printer.
pub struct Goal {
    pub id: GoalId,
    pub ctx: LocalCtx,          // binders in scope: (name, type)
    pub target: ExprId,         // the proposition, in CIC
    pub holes: Vec<HoleId>,     // tracked; never silently discharged
}
```

Canonically serializable: our determinism rule (stable iteration order, no
hash-map iteration in output) means **two identical goals produce identical bytes**
— free dedup, caching, and hashing for an agent's search. Lean cannot promise this.

### 4.2 `Hole` — representing *not yet knowing*

Reconstruction has never needed this: a certificate dictates the proof, so nothing
ever has a hole (`reconstruct.rs:7921` — it "otherwise builds closed terms"). A
goal layer is the opposite, and this is the layer's reason to exist.

```rust
pub struct Hole {
    pub id: HoleId,
    pub ctx: LocalCtx,          // the hole's OWN context — see §4.3
    pub ty: ExprId,
    pub kind: HoleKind,         // Natural | SyntheticOpaque | Delayed
    pub depth: u32,             // see the depth invariant, §4.4
}
```

`SyntheticOpaque` is Lean's name for *"this is an unsolved subgoal — do not let
unification close it by accident."* Adopt the concept and the name.

### 4.3 Delayed assignment — **the one thing to copy, and the least obvious**

From [note 12](../research/12-elaboration-egraphs-fmf.md): this is a
**type-theoretic necessity, not a syntactic convenience**, and every
`intro`/`induction` hits it.

The problem: you cannot abstract a binder over a hole whose local context *contains*
that binder — the result is ill-formed. Lean's answer is to assign the metavariable
to an *application* of a fresh one:

```
?m := ?n x        -- a delayed substitution
```

**If P6.2 gets this wrong, `intro` is wrong, and everything above it is wrong.**
This is the single highest-value thing to lift from Lean, and it survives deleting
the parser.

### 4.4 The depth invariant

> **Level *N+1* must be fully assigned before returning to level *N*.**

This is what stops a nested `simp` call from silently solving a *sibling* goal. It
is cheap to design in and near-impossible to retrofit. So is **explicit
metavariable coupling** — when two goals share a hole, an agent must be able to ask
*"what else does solving this constrain?"*

## 5. The certificate protocol — the novel part

A proof is a **tree of `Step`s**. Each `Step` is emitted by an untrusted procedure
and validated by a small checker that returns a kernel-checked `ExprId` or a typed
failure.

```rust
pub enum Step {
    /// The solver decided it. The whole solver becomes one tactic.
    Decide  { fragment: FragmentId, cert: SolverCert },   // Alethe | LRAT | Farkas | congruence

    /// The e-graph rewrote it. `chain` is egg's explain_equivalence output.
    Simp    { chain: EggExplanation },

    /// THE UNTRUSTED CHOICE, made explicit and checkable.
    Induct  { motive: ExprId, recursor: NameId },
    Instantiate { terms: Vec<ExprId>, round: u32 },       // the depth policy lives HERE
    Split   { on: ExprId, cases: Vec<Step> },
    Witness { term: ExprId },                             // for an existential

    /// Structural.
    Intro   { binder: NameId },
    Apply   { lemma: ExprId, args: Vec<ExprId> },

    /// NOT a proof. A first-class refutation. See §6.
    Refute  { model: Model },
}
```

**Read `Instantiate { terms, round }` against §2.** The solver refuses to guess an
instantiation depth because guessing would be unsound. Here the caller *supplies*
the terms and the round, the checker validates that each instance is a genuine
instance of the universal, and the kernel checks the resulting term. **The unsound
guess became a checkable proposal.** That is the mechanism the whole design exists
to provide.

### 5.1 What each checker must do

| Step | Checker's job | Cost |
|---|---|---|
| `Decide` | Reconstruct the solver certificate to a CIC term; `infer` + `def_eq` against the goal. **This route already exists** (~20 `reconstruct_*_to_lean_module` fns). | reuse |
| `Simp` | Walk the egg explanation and build an `Eq.trans`/congruence spine. **The chain is free** — egg's greedy explainer is O(n log n) with no asymptotic overhead. **The cost is the spine**, not the chain. | the real work |
| `Induct` | Check the motive typechecks and the recursor application is well-typed. The kernel already generates recursors *with* induction hypotheses (`inductive.rs:45-53`). | small |
| `Instantiate` | Check each `term` is well-sorted in `ctx` and each instance really is an instance. **Report `round` and term depth** — "decides at depth *k*" is a fact about *k*. | small |
| `Split` | Check the cases are exhaustive for `on`. | small |
| `Witness` | Check the term inhabits the existential's domain. | trivial |
| `Refute` | **Lift the model to CIC and evaluate the original goal against it in the kernel.** | the `sat` gate |

**The template already exists and someone else wrote it**: Rocq's `lia` is
*untrusted search + a reflective checker + a certificate*. Micromega is our
identity sentence in someone else's codebase. Cite it; do not reinvent it.

## 6. `Refute` — the thing nobody else has

Every other system treats "not proved" as an absence. We treat it as a **result
with a certificate**.

> *"Most 'theorems' initially given to an ITP do not hold."* — Blanchette & Nipkow

DeepSeek-Prover found **≥20% of autoformalized statements false**, called it
"significant computational waste," and built a concurrent disproof channel.
FormalMATH retains 72.09% pre-human-review using **negation-based disproof
filtering**. Disproof is load-bearing infrastructure, not a nicety — and it is
**unoccupied**.

The agent's most valuable question is not *"prove this."* It is **"is this worth a
proof search?"** A goal refuted in 50 ms beats one that times out at 300 s, and the
saving compounds across a search tree.

**Non-negotiable:** `Refute` ships **only** after its checker (P6.1c). Until the
model is lifted back to CIC and evaluated against the original goal *in the
kernel*, a counterexample is a confident wrong answer with nothing checking it —
worse than no answer.

## 7. What is deliberately not here

| Not building | Why |
|---|---|
| **A mathematics library** | Mathlib's network effect is real, compounding, unbeatable. We import nothing. |
| **A surface syntax / proof script language** | **0/33 across 660 attempts** — LLMs cannot write a low-resource formal language. Any syntax we invent inherits that number. Goals are **data**; where an agent must write, it writes SMT-LIB or Lean and we compile down. |
| **A universal substrate** | Dedukti *grows* the TCB (kernel + rewrite theory + confluence + termination + adequacy proof). *Don't build the universal thing; build the bridge someone wants.* |
| **Hygiene, `do`, coercions, overloading** | They exist to disambiguate *what a user typed*. API-built goals are unambiguous. Ullrich's thesis is literally *An Extensible Theorem Proving Frontend* — a thesis about the part we skip. |
| **`sorry`** | `fail`. A hole is never a theorem. |
| **Push-button verification of an undecidable fragment** | That product's failure mode is documented: Dafny users report "soul crushing." |

## 8. What makes it unique

Not aspirations — properties that already hold or fall out of the design.

| Property | Why it is ours and not theirs |
|---|---|
| **Certificate-first construction** | The precedents exist **unassembled** — DRAT/LRAT, Alethe/LFSC, Rocq's reflective `ring`/`lia`, Sledgehammer's shape. **Nobody has built the general version.** |
| **The solver *is* the automation** | `decide` is one dispatch to `check_auto`. Every decision procedure is a tactic for free. Lean must *write* `omega`, `bv_decide`, `grind`; we have them. |
| **Refutation as a first-class result** | Unoccupied. ITPs are famously bad at counterexamples (Nitpick, `plausible`). |
| **No library to import** | **~99.9% of agent per-branch wall time is import + re-elaboration** (~60 s import; tactic execution <0.1%). We have nothing to import. The field's entire cost model is a tax we do not pay. |
| **A genuinely independent CIC kernel** | `coqchk` **links the kernel it checks**; `lean4lean` says outright it is *"not really an independent implementation."* Almost nobody has one. |
| **Determinism as an API promise** | Identical goals → identical bytes. Everest reports Z3 *"behaves differently on Windows versus macOS"*; F* pinned Z3 at 2019 for years. |
| **WASM / no toolchain** | Runs in the agent's process. Lean4Web runs Lean **server-side behind gVisor**. |

## 9. Crate layout

```
crates/axeyum-goal/           NEW
  src/
    goal.rs        Goal, LocalCtx, GoalId — data, serializable
    hole.rs        Hole, HoleKind, delayed assignment (§4.3)
    mvar.rs        the metavariable context + depth invariant (§4.4)
    unify.rs       Miller-pattern only; decline outside it
    step.rs        the Step enum (§5)
    check/         ★ TRUSTED ★ one small checker per Step kind
      decide.rs      reuse reconstruct.rs
      simp.rs        egg chain → Eq.trans spine
      induct.rs      motive + recursor
      instantiate.rs instance validation + depth reporting
      refute.rs      model → CIC → evaluate (gated on P6.1c)
    tactic.rs      untrusted procedures emitting Steps

crates/axeyum-bridge/         NEW — CIC ⇄ axeyum-ir, untrusted (P6.1)
crates/axeyum-goal-mcp/       NEW — the agent surface, ≤6 verbs (P6.4)
```

**Boundary discipline**: `check/` is the only trusted module in `axeyum-goal`, and
it may depend on `axeyum-lean-kernel` and nothing else. If a checker ever needs the
solver, the design is wrong.

## 10. Build order, and why

1. **[P6.0](../plan/P6.0-kernel-trustworthiness.md)** — the kernel. It admitted
   `False` this morning; zero fuzz; positivity enforced vacuously; **64** unproven
   prelude axioms. Everything here stands on it, **and it is the product**: a
   kernel that admitted `False` cannot be anyone's independent check.
2. **[P6.1a](../plan/P6.1-obligation-bridge.md)** — extract IR→CIC from
   reconstruction into a real bridge. Zero new capability; it de-risks the seam,
   and **P3.7's T3.7.3 needs the same work anyway.**
3. **[P6.2](../plan/P6.2-goals-and-holes.md)** — `Goal`, `Hole`, delayed
   assignment, the depth invariant. **Get §4.3 right or nothing above works.**
4. **`Decide` + `Intro` + `Apply`** — the smallest end-to-end proof. `decide`
   reuses reconstruction, so this is plumbing, and it proves the protocol.
5. **[P6.1c](../plan/P6.1-obligation-bridge.md)** → then `Refute`. The
   differentiator, once it is sound.
6. **[P6.4](../plan/P6.4-agent-surface.md)** — the MCP surface. **≤6 verbs**;
   MCP-Solver's measured lesson is *"fewer tools perform better."*
7. **`Simp`, `Induct`, `Instantiate`** — where the search premise gets tested for
   real.

## 11. The open question, stated so it can be answered

**Certificate-first is a *checking* discipline. It presumes a certificate exists to
emit.** `Decide` is safe — the solver already found the proof, so the certificate
is a transcript. `Instantiate`, `Induct`, and `Simp` are different: something must
*choose* the terms, the motive, the rules.

The design's answer is **the choice is the caller's, and the certificate makes it
safe** — that is §2, and it is why the layer exists. What the design does *not*
claim is that the caller will choose *well*. A human writing `induction n` chooses
well. An agent proposing depths chooses well *sometimes*, and the certificate is
what makes cheap wrong guesses safe to try — which is exactly the loop
AxProverBase won with (98.0% miniF2F, a ReAct proposer around a fast verifier).

**That is the bet, and it is testable**: does proposing-and-checking beat guessing
soundly? Nobody has run it, because nobody has had a fast checkable substrate to
run it on.
