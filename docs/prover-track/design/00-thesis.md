# Thesis — why this system, and why it is ours to build

**What it is and how it is built:** [`03-architecture.md`](03-architecture.md).
**Sources:** [`../REFERENCES.md`](../REFERENCES.md).
**Process record** (how this was arrived at, and every constraint's provenance):
[`../process/`](../process/README.md). Kept deliberately out of here.

---

## The claim

**Build a certificate-first proof assistant on `axeyum-lean-kernel`.** A tactic is
an untrusted procedure that emits a certificate; a small checker turns it into a
kernel-checked term; the tactic never enters the TCB.

It is not Lean-in-Rust. It is a different design, and the reason is a fact about
our own solver.

## 1. Why the layer must exist

`auto.rs:5244` declines a residual quantifier, and the comment is a **correctness
statement, not a TODO**:

> *"Quantifiers left after instantiation (nested, existential, or non-top level)
> **cannot be decided by the quantifier-free engines**."*

Instantiation only **weakens**. A residual quantifier therefore licenses no
verdict, and **the solver cannot soundly guess an instantiation depth.** Closing
even Dreadbury Mansion needs `pel55_7`/`pel55_9` instantiated at `f(butler)` — a
term that exists only after a *second* round, over an infinite Herbrand universe.

Someone must choose the depth. That someone is:

- **not the solver** — guessing would make it unsound;
- **not the kernel** — it does not search;
- **the prover.**

> **A correct fragment boundary is what creates the need for a layer above it.**
> The solver declines honestly; the prover is where the untrusted choice lives;
> the certificate is what makes the choice safe.

A human writes `induction n`. An agent proposes a depth. Neither is the solver
guessing, and both are checkable.

## 2. Why certificate-first, and not LCF or de Bruijn

| Design | A tactic is… | The TCB grows with | Artifact |
|---|---|---|---|
| **LCF** (Isabelle, HOL Light) | a function over an abstract `thm` | every primitive inference | **none** — nothing to hand a skeptic |
| **de Bruijn** (Lean, Rocq) | a program that builds a term | the kernel's accelerators | the term |
| **Ours** | **a procedure that emits a certificate** | **checkers only** | **the certificate *and* the term** |

The precedents exist **unassembled** — DRAT/LRAT, Alethe/LFSC, Rocq's reflective
`ring`/`lia`, Sledgehammer's shape. **Nobody has built the general version.**
Rocq's `lia` — *untrusted search + reflective checker + certificate* — is our
identity sentence already written in someone else's codebase.

Independent validation from the person who thought hardest about it: **Metamath
Zero's producer/consumer split is this design.**

And it is the only shape where **our existing automation is an asset rather than a
liability**: `decide` is one dispatch to `check_auto`, so every decision procedure
becomes a tactic for free. Lean has to *write* `omega`, `bv_decide`, `grind`. We
have them.

## 3. What is uniquely ours

Properties that already hold or fall out of the design — not aspirations.

| | Why it is ours |
|---|---|
| **A genuinely independent CIC kernel** | `coqchk` **links `rocq-runtime.kernel`** — the kernel it checks. `lean4lean`'s own README: *"not really an independent implementation."* Almost nobody has one. The entire empirical case for kernel diversity is one data point: **`lean4checker` rejected a `native_decide` proof of `False` that Lean's kernel accepted.** |
| **The solver is the automation** | 24 measured fragments, ~2× Z3 on QF_BV, certificates already shipping. |
| **Refutation as a first-class result** | **Unoccupied.** *"Most 'theorems' initially given to an ITP do not hold"* (Blanchette & Nipkow). DeepSeek found **≥20%** of autoformalized statements false and built a disproof channel out of desperation. |
| **No library to import** | **~99.9% of agent per-branch wall time is import + re-elaboration** (~60 s import; tactic execution **<0.1%**). We have nothing to import. **The field's entire cost model is a tax we do not pay** — and it falls straight out of refusing to build a Mathlib. |
| **Determinism as an API promise** | Identical goals → identical bytes: free dedup, caching, hashing for an agent's search. Everest reports Z3 *"behaves differently on Windows versus macOS"*; F\* pinned Z3 at 2019 for years. |
| **WASM, no toolchain** | Runs in the agent's process. Lean4Web runs Lean **server-side behind gVisor**. Pantograph's practical win over LeanDojo was *dropping Docker* — startup, not algorithms. |

Uncomfortable and worth stating: **most of these came from soundness and
reproducibility discipline, not foresight.** Determinism, `unknown`-as-a-value, no
global mutable state, explicit seeds and limits, checkable `sat` — the hard rules
happen to be the agent-fitness checklist. The work left is **exposing** what those
rules already forced.

## 4. Constraints the research bought

Each earned, each non-negotiable. This is why the plan is better than one written
on day one.

| Constraint | Source |
|---|---|
| **P6.0 first.** The kernel admitted `False`; its former **zero-fuzz** boundary now has a 768-case four-seam seed, while positivity remains enforced only *vacuously*; **65** runtime-ledgered but unproven prelude assumptions; `Lit::Nat` truncation remains unguarded. Foundation **and** product. | ADR-0165; T6.0.3/TL2.15 seed; TL0.4; notes 01/06 |
| **`Refute` ships only after its checker.** A mistranslated goal returning `sat` is a confident wrong answer with nothing checking it — worse than none. | note 08 → P6.1c |
| **Never invent a surface syntax.** LLMs score **0/33 across 660 attempts** on a low-resource formal language. Goals are **data**; where an agent must write, it writes SMT-LIB or Lean and we compile down. | note 10 |
| **Binary certificates; checking throughput as a defended gate.** MM0 checks ZFC in **<200 ms**. `bv_decide`'s bottleneck is *kernel reduction*, not solve time — that is the axis to win. | note 11 |
| **One named consumer per certificate format.** *Don't build the universal thing; build the bridge someone wants.* Dedukti **grows** the TCB and is out. | note 11 |
| **Copy delayed assignment; skip the parser.** Hygiene, `do`, coercions, overloading all die with the surface syntax. **Delayed assignment is a type-theoretic necessity** and every `intro` hits it. | note 12 |
| **`simp`'s cost is the `Eq.trans` spine, not the chain.** egg's greedy explainer is **O(n log n), no asymptotic overhead** — "the first certifying equality saturation engine." | note 12 |
| **Report instantiation depth as a first-class quantity.** "Decides at depth *k*" is a fact about *k*. | round 4 |
| **Ship every slice with its TCB statement.** *Verification Theatre*: 13 vulns escaped, **4 inside verified code**, from an undocumented boundary. | note 04 |
| **Don't sell "SMT is broken."** Contested by **Z3's own author**. The uncontested claim is stronger: instability is a property of *undecidable encodings* — `KomodoD` **5.01%** vs `KomodoS` (decidable) **0.52%**. | note 03 |

## 5. What we are not building

- **A mathematics library.** Ever. Mathlib's network effect is real and compounding.
- **A proof scripting language.** Refused with a number (**0/33**), not a preference.
- **A universal substrate.** Dedukti's lesson: value scales with adoption, adoption
  with encoding fidelity, and CIC fidelity is a 13-year research problem.
- **A Dafny/Verus.** Push-button verification over an undecidable fragment; users
  call the failure mode "soul crushing."
- **`sorry`.** `fail` instead. A hole is never a theorem.

## 6. The open question, stated so it can be answered

**Certificate-first is a *checking* discipline. It presumes a certificate exists to
emit.** `Decide` is safe — the solver already found the proof, so the certificate
is a transcript. `Instantiate`, `Induct`, `Simp` are not: something must **choose**
the terms, the motive, the rules.

The design's answer is §1 — *the choice is the caller's, and the certificate makes
it safe.* What it does **not** claim is that the caller chooses *well*.

**That is the bet, and it is exactly the loop that has already won**: AxProverBase
— a ReAct proposer around a fast verifier — reaches **98.0% miniF2F pass@1**,
beating the specialised provers; Aleph took PutnamBench to **668/672** via *"highly
parallel Lean verification calls."* Whole-proof generation, stepwise neural search,
and corpus fine-tuning all lost to **an agent loop around a fast checker**.

**The certificate is what makes cheap wrong guesses safe to try.** Nobody has run
that loop on a substrate with no import tax, native counterexamples, and an
independent kernel — because nobody has had one.

## 7. Build order

**P6.0** (kernel) → **P6.1a** (bridge extraction; P3.7 needs the same work anyway)
→ **P6.2** (`Goal`/`Hole`/delayed assignment) → **`Decide`+`Intro`+`Apply`** (the
smallest end-to-end proof) → **P6.1c** → **`Refute`** → **P6.4** (≤6 MCP verbs) →
**`Simp`/`Induct`/`Instantiate`** (where the bet gets tested).

Each slice lands alone. A slice that stops paying is where we stop, and what
shipped keeps working.

Detail: [`03-architecture.md`](03-architecture.md) §10 and
[`../plan/README.md`](../plan/README.md).

## 8. The verification boundary

Stated first, per *Verification Theatre* — the undocumented boundary is what bites.

- **In the TCB:** `axeyum-lean-kernel` (which admitted `False` on 2026-07-15), the
  `check/` module, **65** unproven prelude assumptions, `rustc`, **6 of 14** open
  reduction-ledger entries.
- **Not in the TCB:** the solver, the e-graph, PDR, the bridge, every tactic, any
  agent.
- **Not covered:** `sat` results until P6.1c; anything outside the published
  fragment; whether that fragment covers anything anyone wants — **unmeasured**
  until P6.1e.
