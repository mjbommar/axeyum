# Synthesis — what this track learned

The one file to read. Everything else is evidence for it; sources are indexed in
[`REFERENCES.md`](REFERENCES.md) (87 papers, 29 repos, 265 URLs, gaps named).
Recommendation and design: [`design/00-thesis.md`](design/00-thesis.md) (v4).
Plan: [`plan/README.md`](plan/README.md). Why you should distrust both:
[`critique/`](process/critique/). How it went wrong four times: [`DIARY.md`](process/DIARY.md).

---

## What we are building

**A certificate-first proof assistant on `axeyum-lean-kernel`.**

> **A tactic is an untrusted procedure that emits a certificate. A small checker
> turns it into a kernel-checked term. The tactic never enters the TCB.**

Reconstruction already does this for certificates about **formulas** (DRAT/LRAT →
CIC terms). This does it for certificates about **goals**.

Full design: **[`design/03-architecture.md`](design/03-architecture.md)**.
Why: **[`design/00-thesis.md`](design/00-thesis.md)**.
Build guide: **[`plan/README.md`](plan/README.md)**.

## Why the layer must exist — one fact from our own solver

`auto.rs:5244` declines a residual quantifier, and its comment is a **correctness
statement, not a TODO**: *"Quantifiers left after instantiation … cannot be decided
by the quantifier-free engines."* Instantiation only **weakens**, so **the solver
cannot soundly guess an instantiation depth.**

Someone must choose the depth. Not the solver (unsound). Not the kernel (it does
not search). **The prover.**

> **A correct fragment boundary is what creates the need for a layer above it.**
> The solver declines honestly; the prover is where the untrusted choice lives;
> the certificate is what makes the choice safe.

A human writes `induction n`. An agent proposes a depth. Both are checkable.

## Why it is not Lean-in-Rust

| Design | A tactic is… | TCB grows with | Artifact |
|---|---|---|---|
| **LCF** (Isabelle, HOL Light) | a function over abstract `thm` | every primitive inference | **none** |
| **de Bruijn** (Lean, Rocq) | a program that builds a term | the kernel's accelerators | the term |
| **Ours** | **a procedure emitting a certificate** | **checkers only** | **certificate *and* term** |

The precedents exist **unassembled** — DRAT/LRAT, Alethe/LFSC, Rocq's reflective
`ring`/`lia`, Sledgehammer's shape. **Nobody has built the general version.**
Metamath Zero's producer/consumer split is independent validation of exactly this.

And it is the only shape where our automation is an asset: **`decide` is one
dispatch to `check_auto`** — every decision procedure becomes a tactic for free.
Lean must *write* `omega`, `bv_decide`, `grind`.

## What is uniquely ours

| | Why |
|---|---|
| **A genuinely independent CIC kernel** | `coqchk` **links the kernel it checks**; `lean4lean` says outright it is *"not really independent."* The whole empirical case for kernel diversity is one data point — `lean4checker` rejecting a `False` that Lean's kernel accepted. |
| **Refutation as a first-class result** | **Unoccupied.** *"Most 'theorems' initially given to an ITP do not hold."* DeepSeek found ≥20% of autoformalized statements false and built a disproof channel out of desperation. |
| **No library to import** | **~99.9% of agent per-branch wall time is import + re-elaboration.** We have nothing to import. The field's entire cost model is a tax we do not pay. |
| **Determinism as an API promise** | Identical goals → identical bytes. Z3 *"behaves differently on Windows versus macOS"*; F\* pinned it at 2019 for years. |
| **WASM, no toolchain** | Lean4Web runs Lean **server-side behind gVisor**. Pantograph beat LeanDojo by *dropping Docker*. |

## Build order

**P6.0** (kernel — it admitted `False`) → **P6.1a** (bridge; P3.7 needs it anyway)
→ **P6.2** (`Goal`/`Hole`/**delayed assignment**) → **`Decide`+`Intro`+`Apply`**
(smallest end-to-end proof) → **P6.1c** → **`Refute`** → **P6.4** (≤6 MCP verbs)
→ **`Simp`/`Induct`/`Instantiate`**.

**First commit:** P6.0 T6.0.3 — **fuzz the kernel, seam-first.** 181 hand-written
tests, **zero fuzz**, and every historical Lean/Rocq kernel bug lived at a feature
seam.

## The bet, stated so it can be lost

**Certificate-first is a *checking* discipline; it presumes a certificate exists to
emit.** `Decide` is safe — the solver already found the proof. `Instantiate`,
`Induct`, `Simp` need something to **choose**.

The design's answer: *the choice is the caller's, and the certificate makes it
safe.* It does **not** claim the caller chooses well.

**That is exactly the loop that has already won.** AxProverBase — a ReAct proposer
around a fast verifier — hits **98.0% miniF2F pass@1**, beating the specialised
provers; Aleph took PutnamBench to **668/672** via *"highly parallel Lean
verification calls."* Whole-proof generation, stepwise neural search, and corpus
fine-tuning all lost to **an agent loop around a fast checker**.

**The certificate is what makes cheap wrong guesses safe to try.** Nobody has run
that loop on a substrate with no import tax, native counterexamples, and an
independent kernel — because nobody has had one.

---

## Appendix: the method record

> **"A decline is missing plumbing."**

I read `PAR-2 = 0.000` / `Unsup=5` as *we never tried*. It isn't:

- `auto.rs:5244-5252` declines on `residual_quantifier`, and the comment is a
  **correctness statement, not a TODO** — instantiation only *weakens*, so a
  residual quantifier licenses no verdict. **Fast is what a correct boundary looks
  like. I read speed as unseriousness.**
- **`Unsup` is a harness bucket** (`bench/src/main.rs:4626`); the solver returns
  `Unknown(Incomplete)`. The split the whole finding turned on is a classification
  artifact **nobody traced — including me, while claiming to have traced it.**
- **The fix inverts**: Skolemizing `pel55_10` **leaves EPR**, the only quantified-UF
  fragment where carrier-bounding is sound for `unsat`. Closing PUZ001+1 then needs
  a second instantiation round over an infinite Herbrand universe
  (`quantifiers.rs:475` collects ground terms **once**) — **a depth policy, which
  is a search heuristic.**

**Which is exactly the open premise** (certificate-first is a *checking* discipline
sold as a *search* discipline). **The goal I offered as the plumbing example is
where the search premise bites hardest.**

### Six premises, one shape

| # | Premise |
|---|---|
| 1 | "software is 88–100%" — quoted correctly, read backwards |
| 2 | "round 1 is right" — deference to the grader |
| 3 | "residue = MCP + WASM" — assumes every goal is one-shot decidable |
| 4 | "certificate-first ⇒ decomposition" — checking sold as search |
| 5 | "the 0% column is the reason" — conclusion outlived its reason |
| 6 | **"a decline is missing plumbing" — a correct boundary read as a bug** |

> **Every one is a number, correctly quoted, whose *meaning* was assumed rather
> than traced to the code or the model theory that produced it.** — round 4

My own maxim, *only the world checks your premises*, was applied **one level too
shallow**: running the goals checked the **scoreboard**, not the **engine**, and
never asked whether the boundary the engine reports is a bug or a theorem. **It is
a theorem.**

---

## What we learned about the world

Ranked by how much they should change someone's mind. All primary-sourced; see
the notes for citations.

### 1. Instability is a property of undecidable encodings, not of SMT

The cleanest A/B in the literature — same system, two encodings:

| | Unstable |
|---|---|
| `KomodoD` (Dafny, undecidable) | **5.01%** |
| `KomodoS` (Serval, **decidable fragment**) | **0.52%** |

Corroborating: timeout failures show **~59×** more quantifier instantiations than
quick-unknowns (270,396 vs 4,587 median). AWS's Zelkova does **a billion decidable
queries a day** without this being the story.

**And "SMT is brittle" is contested by Z3's own author** — Bjørner co-signed a
conjecture that instability is "often caused by fixable engineering problems, and
is thus **not fundamental**," with 11 root-caused cases (6 solver bugs, 2
misconfigs, 3 trigger misunderstandings). Mariposa's own bisect traced **67% of a
cross-version regression to two ~10-line commits**, which Z3 fixed. Everest ran
**>600,000 proof obligations** at 2:1 proof-to-code and called SMT "on the whole,
positive."

**So do not sell "SMT is broken."** The uncontested version is stronger: a
finite-domain, bit-blast-to-SAT core is structurally on the good side of the
decidable line.

### 2. The 99% / 78% pair — our architecture, described by someone else

**96.23–99.94% of the context sent to a solver is irrelevant**, and that
irrelevance causes **78.3% of instability**. Replace a query with its unsat core
and **90.3% of unstable queries become stable**.

Verus prunes natively; **F\* adopted pruning from Verus and it is now on by
default**, reported as matching unsat-core replay for stability. "Untrusted fast
search over the slice you actually need" is not our idea — it is the field's
best-in-class mitigation, and unsat-core replay is a weaker version of what proof
artifacts do natively.

### 3. Small trusted kernels get verified; the bugs live in the parts that aren't small

Coq documents **78 critical bugs**, 5 unfixed — "**on average, one critical bug has
been found every year in Coq**." The largest category is **conversion machines:
20 of 78** — the Poincaré principle's bill, i.e. exactly what putting an evaluator
inside a trusted kernel costs. Predicted in 2001: "**This puts somewhat of a
strain on the de Bruijn criterion.**"

**And verification coverage is anti-correlated with risk.** MetaCoq verifies PCUIC
*minus* the module system, template polymorphism, and η — precisely the areas
holding **23 of the 78**. The guard checker, verified by nobody, produced a
relative inconsistency latent from **1997 to 2025** that still has an open issue.

**Our P0 lived in `inductive.rs`** — 1,081 lines, the largest trusted blob, the one
P3.6's own task table calls "the biggest trusted blob." We reproduced the field's
dominant failure mode exactly.

### 4. Independence is rare, and mostly claimed falsely

- **`coqchk` is not independent** — its `checker/dune` links
  `rocq-runtime.kernel`, the same 43,709-line kernel. A conversion bug escapes it
  *by construction*. **Coq ships no independent kernel.**
- **`lean4lean` is not independent** — its own README: "likely shares some
  implementation bugs with it."
- **The entire empirical case is one data point**: `lean4checker` rejected
  Carneiro's `native_decide` proof of `False` that Lean's kernel accepted.

**`axeyum-lean-kernel` is a genuinely independent, from-scratch CIC kernel in a
different language. There are almost none.** That is true *today* — no goal layer,
no bridge, no person-years — and it is the strongest claim this track produced. It
took four drafts and a straggler to notice.

### 5. Capability tracks target-language data volume — do not invent a syntax

SPEAC/UCLID5, on a low-resource formal language:

| Method | Correctness |
|---|---|
| One-shot prompting | **0/33 — no LLM produced code that parses, across 660 attempts** |
| Fine-tuned on 317 examples | 6.1% |
| **Pivot through a high-resource IR + compiler repair** | **84.8%** |

Against ~80% on Python. This is the Mathlib network-effect argument sharpened —
about *syntax and idiom*, not library size — and **any novel textual surface we
invent inherits the 0%**. It forecloses a human-facing proof language of our own
with a number rather than an argument.

### 6. The certificate thesis, argued by someone not trying to argue it

**"Scope laundering" in 15.3–52.5% of predictions: models claim formal grounding
without ever executing the solver.**

An agent that says it proved something is, between 15% and 52% of the time, saying
so having run nothing. **A certificate is the only thing separating a proof from a
claim of a proof** — measured, not asserted.

Second, independent: FormalMATH retains 72.09% pre-human-review via
**negation-based disproof filtering**; DeepSeek built a concurrent disproof channel
after finding **≥20% of autoformalized statements false**. Disproof is load-bearing
infrastructure, not a nicety.

### 7. The agent loop won, and the scarce resource is the verifier

AxProverBase (a ReAct loop around a compiler) reaches 98.0% miniF2F pass@1,
beating the specialized provers. Aleph took PutnamBench to 668/672 via "highly
parallel Lean verification calls."

And **~99.9% of agent per-branch wall time is import + re-elaboration** (~60s
import; tactic execution <0.1%). **We have no library to import.** The field's
entire cost model is a tax we do not pay — structural, and bigger than the WASM
claim.

**But do not oversell the surface:** `lean4check` + Claude Code reaches **87% on
189 proof-engineering tasks with one tool**, and MCP-Solver's measured lesson is
"**fewer tools perform better**." A rich surface pays on *search-heavy* work only.

### 8. The graveyard died of assuming the spec is free

ESC/Java, Spec#, VCC, Code Contracts — one cause. The middle is occupied only by
controlling the language (Dafny, SPARK), having a regulator, or abandoning
soundness (Infer survived by *leaving*).

**Verification Theatre**: 13 vulnerabilities escaped verification in
libcrux/hpke-rs — **four inside verified code**, including a false serialization
proof — diagnosed as the **undocumented verification boundary**, not bad proofs.
*The proofs were fine; nobody could tell what they covered.*

---

## What we learned about ourselves

Every item below was found by **running something**, not by reading it.

| Finding | Status |
|---|---|
| **The kernel admitted `theorem bad : False`** — unrestricted `Prop` large elimination + proof irrelevance | **Fixed** (ADR-0165, `d26ad887`), exploit inverted into a regression + boundary matrix |
| **64 unproven prelude axioms** (arith 30 + int 34), counted. ℝ's carrier is an opaque `Declaration::Axiom`; Lean accepts axioms **vacuously**; `#print axioms` is an *inventory, not a validation* | **Open** — T6.0.6 |
| **Positivity is enforced only *vacuously*** — an accident of `ReflexiveOrNestedNotSupported`. Land the obvious next inductive gap and it **vanishes with no checker behind it** | **Open** — T6.0.2, the P0 pattern pre-loaded |
| **`Lit::Nat` is `u128`; truncation guarded by nothing** — inert only because `UnsupportedLit` rejects literals first | **Open** — T6.0.4, an ordering hazard |
| **ℝ and ℤ preludes cannot coexist — it panics.** 28 shared names; the gate *correctly rejected* rather than aliasing `add : R→R→R` onto `add : ℤ→ℤ→ℤ`, but the builder `.expect()`s | **Open** — T6.0.8 |
| **181 hand-written tests, zero fuzz.** By CLAUDE.md's own rule, every corner is an avoided corner | **Open** — T6.0.3 |
| **Alethe may be aimed wrong** — `lean-smt` uses **CPC**; cvc5's Alethe has **no bit-vectors** | **[ADR-0166](../research/09-decisions/adr-0166-alethe-target-reassessment.md) filed** |
| **`sat` has no trust story** — the kernel gate covers `unsat` only | **Open** — P6.1c |
| **We are a rare genuinely independent kernel** | **True today** |

### The pattern, which is worth more than any single item

**Three times, a corroborating gate took the contested thing on trust:**

1. `lean_pp` emitted recursors **as axioms** — so real-Lean re-checked our
   recursor's *use*, never its *generation*. That is why it could not see the P0.
2. The preludes **axiomatize** ℝ/ℤ — and Lean accepts axioms vacuously, so the
   same gate cannot catch a false axiom either.
3. **Positivity** is enforced only as a side effect of an unrelated rejection.

One design habit, not three bugs. Hence the rule this track contributes, which
generalizes far beyond the kernel:

> **Deferral by rejection is safe. Deferral by permission is not.**

And the uncomfortable mirror: **Lean's kernel is sound only relative to a trusted
prelude** — `lean4lean/divergences.md` admits it does not check that primitives
have the correct types, "**required for soundness**," excused because "Lean ships
its prelude." Same shape as ours. **Ours is worse**: Lean's prelude is at least
*definitional*; our arithmetic carrier is an opaque axiom. So "the kernel" was
never the TCB boundary — **the kernel plus its prelude** is, and every kernel-size
comparison in the field flatters everyone, us included.

---

## The verification boundary of this track

Per *Verification Theatre*'s own lesson — the undocumented boundary is what bites.

**Researched and primary-sourced:** ITP anatomy and kernel soundness (measured
from source clones); AI-assisted proving; the ATP/ITP seam and SMT instability;
autoformalization; education and agentic surfaces; our own kernel, reconstruction,
and solver assets (verified by execution).

**Not researched — do not read this track as covering:**

- **Isabelle** — essentially nothing verified.
- **Metamath Zero** — not covered. A real omission, since we make a minimal-TCB
  argument and it is the central artifact for one.
- **Systems-verification economics** — a research thread on seL4 adoption
  (NASA/cFS, NIO SkyOS, Cog Systems, the seL4 Foundation) and the CACM
  Woodcock/Larsen and Brooker material was **started and killed mid-flight**. Note
  04's person-year figures stand; the *adoption and economics* picture does not
  exist and should not be inferred from what is here.
- **Dedukti/Logipedia** — search-only; no LoC, no coverage numbers.
- Metamath quantitative claims beyond `mmverify.py` — search-derived.

**Premises checked and found false** (recorded so nobody re-derives them): Coq
#7825 is a tactics PR, not a kernel bug. `nanoda_lib` is a current **Lean 4**
checker, not a Lean-3 artifact. "Lean cannot compile to WASM" is unverified —
what is known is that Lean4Web runs Lean *server-side behind gVisor*.

---

## The method lesson

Four drafts. Each died of exactly one unexamined premise, each fully cited:

| Draft | Said | Died of |
|---|---|---|
| 1 | Build a substrate | *"software is 88–100%"* — cited its own evidence backwards |
| 2 | Don't build | *"round 1 is right"* — ten concessions of ten, uniformly, toward the grader |
| 3 | Don't build, better | *"residue = MCP + WASM"* — assumes every goal worth having is one-shot decidable |
| 4 | Build it, sliced | *"certificate-first ⇒ decomposition"* — checking sold as search |

Three independent adversaries, pointed in opposite directions, killed three
distinct failure modes: **advocacy**, **deference**, and **self-congratulation**.
Round 2's finding is the one to keep: *"Real revisions are lumpy. This one is
uniform, and it is uniform in the direction of the person grading it."*

**But none of the three found any of the facts in §1–§8 above.** They were
reasoning about the *document*. Those facts came from five agents I had written
off as dead, every one of which used `gh` against upstream, `pdftotext` on real
papers, line-counting in source clones, or running the kernel. Two of them caught
their *own* summarizers confabulating numbers that flattered the thesis — the
session's failure mode in miniature, and they caught it in themselves more
reliably than I did.

> **The adversary checks your reasoning; only the world checks your premises.**

---

## What to do first

1. **P6.0.** Not contingent on anything here. The kernel admitted `False`, has
   zero fuzz, enforces positivity vacuously, carries 64 unproven axioms, and
   P3.6/P3.7 route all their assurance through it. **And it is the product** — a
   kernel that admitted `False` cannot be anyone's independent check.
2. **[ADR-0166](../research/09-decisions/adr-0166-alethe-target-reassessment.md).**
   Decide it rather than inherit it.
3. **P6.6-paper.** One week. It can end the track, and that is the point.

The entry ADR (`north-star.md:53`) is owed before P6.1. This document does not
pre-empt it — the cost argument belongs there, and CLAUDE.md's "big tasks get
broken down" is an *execution* stance, not a *selection* criterion. It would
equally justify building Mathlib, which we refuse.
