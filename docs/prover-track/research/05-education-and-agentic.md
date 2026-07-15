# Education and Agentic Proving Surfaces

Research note for the prover track. Scope: what the formal-methods-in-education
literature actually reports, what browser-based provers have and have not
achieved, whether controlled natural language helps learners, what an AI agent
needs from a prover, and whether counterexample production is a real
differentiator. Ends with **What this implies for axeyum**.

Status: research note, not a decision. Nothing here is an ADR. Claims are
sourced; where a claim is an inference rather than a reported result, it is
marked *(inference)*.

---

## 1. Formal methods in math education

### 1.1 The landscape

The most useful single entry point is Tran Minh, Gonnord, and Narboux,
*Proof Assistants for Teaching: a Survey* (2025), which covers both purpose-built
tutoring systems and general-purpose assistants "enhanced for educational use
through custom user interfaces and specialized input/output languages"
(<https://arxiv.org/abs/2505.13472>). The framing matters: the survey's own
taxonomy splits the field along exactly two axes — **UI** and **input/output
language** — which is a strong hint about where the pedagogical leverage has
historically been found. Not in the kernel.

Concrete programs worth knowing:

- **Xena Project** (Buzzard, Imperial College London) — the explicit aim is "to
  get mathematics undergraduates using computer theorem provers." The Natural
  Number Game is a Xena artifact
  (<https://cbirkbeck.github.io/natural_number_game/>).
- **Natural Number Game (NNG4)** — 79 levels across 9 worlds (addition,
  multiplication, exponentiation, inequalities), introducing induction,
  equational rewriting, and propositional logic
  (<https://github.com/leanprover-community/NNG4>). Described in the community
  literature as "widely successful in introducing newcomers to Lean" and "a rite
  of passage for many Lean beginners."
- **Mechanics of Proof** (Macbeth, Fordham) — a full proofs course taught on
  Lean (<https://hrmacbeth.github.io/math2001/>).
- **Lean Verbose** (Massot) — controlled natural language tactics
  (<https://github.com/PatrickMassot/verbose-lean4>), written up as *Teaching
  Mathematics Using Lean and Controlled Natural Language*, ITP 2024
  (<https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.27>).
- **Diproche**, **Elfe**, **Waterproof**, **ProofBuddy** — the smaller
  purpose-built end of the survey's spectrum
  (<https://arxiv.org/pdf/2202.08131>, <https://arxiv.org/pdf/1801.10513>,
  <https://arxiv.org/pdf/2211.13513>, <https://arxiv.org/pdf/2505.13474>).

### 1.2 What works pedagogically

**Skill transfer is the stated goal, not ease of input.** This is the single
most important pedagogical finding and it is easy to misread. Massot is explicit
that in Verbose Lean "the primary objective is not simplicity of input, but
rather transfer of skills to traditional mathematics" — students should write
proofs that "are easy to transfer to paper because they look like natural
language" (ITP 2024). The prover is a *training harness for paper proofs*, not a
destination. A tool that makes formal proof easy but teaches nothing that
survives contact with a blackboard has failed on this metric.

**Assistance must be a dial, not a setting.** Verbose Lean "supports several
proof styles interpolating between standard Lean proofs and paper proofs" and is
used "with varying levels of assistance," including a point-and-click interface
"for courses with a low time budget" (ITP 2024). The gradation is the design.
Different courses sit at different points, and students move along the dial
during a term.

**Staffing is the real constraint, and it is brutal.** Macbeth reports a
sustainable student:staff ratio of **20:1**, and that going beyond it "would
require very strong students or an experienced and enthusiastic TA." The course
depends on in-class circulation, office hours, email, and oral examinations —
"significant time spent interacting with individual or small groups of students"
(<https://hrmacbeth.github.io/math2001/>). *(Inference)* This is the number that
should govern any education pitch: the binding constraint on formal methods in
the classroom is **human tutoring hours per confused student**, and any tool
whose value proposition is "answers a question a TA would otherwise answer" is
attacking the actual bottleneck. Any tool that merely adds surface for students
to get stuck on makes the ratio worse.

**Don't teach the mathematics and the prover at the same time.** The Edinburgh
"Foundations of Mathematics" experience report is blunt: "Learning mathematics
and Lean simultaneously is too overwhelming for beginning undergraduates," and
their mitigation is to run Lean labs on topics students met in lectures **at
least a week previously** (<https://arxiv.org/html/2501.03352v3>). Cognitive
load is additive and the budget is already spent.

### 1.3 Reported barriers

Four recur across the literature, in rough order of how often they are named:

1. **Installation and toolchain.** "For those not experienced in software
   development, installing Lean and its toolchain, and keeping it updated to the
   latest version, can be a nontrivial barrier"
   (<https://arxiv.org/html/2501.03352v3>). Macbeth's course routes around this
   entirely by running students in **Gitpod cloud dev environments** so that
   nobody installs Lean (<https://hrmacbeth.github.io/math2001/>). Note the
   shape of this workaround: it is not "we made installation easy," it is "we
   removed installation from the student's life by paying for servers."
2. **Error messages and elaboration mystery.** The general complaint is that
   prover errors are written for the elaborator's benefit, not the learner's.
   Even AI assistance inherits it: Copilot "does not always provide helpful code
   suggestions and occasionally proposes lines that result in error messages"
   (<https://arxiv.org/html/2501.03352v3>). The deeper problem is that a failure
   in a dependently-typed elaborator is often *non-local* — the reported error
   is not where the misunderstanding is.
3. **Dependent type theory as a prerequisite tax.** "Dependent type theory is
   still new to most researchers, and those uncomfortable with programming
   encounter significant barriers on this front"
   (<https://arxiv.org/html/2501.03352v3>). The learner pays for the kernel's
   expressive power whether or not their course needs it.
4. **Mathlib size and API discovery.** Large enough that an entire tool
   ecosystem exists purely to find things in it: **Loogle** (type-shape search),
   **LeanSearch** (natural language), **Moogle**, **Lean Finder**, **Lean State
   Search**. Measured relevance on 300 AI-generated Mathlib queries: LeanExplore
   **55.4% ± 0.7%**, LeanSearch **46.3%**, Moogle **12.0%**
   (per the lean-lsp-mcp / LeanExplore line of work,
   <https://github.com/oOo0oOo/lean-lsp-mcp>). Read those numbers carefully —
   the *best* premise search over the flagship library is right about half the
   time. Discovery is not solved for humans or agents.

---

## 2. Browser-based provers: does no-install actually drive adoption?

### 2.1 The evidence for

**jsCoq** is the strongest case. It targets HTML5/ES2015 and "typically runs
inside a standards-compliant browser **without the need for external servers or
services**," ships 10+ Coq libraries, supports Software Foundations and CPDT,
and — the operative sentence — "since jsCoq requires no installation, it is
often used in workshops to introduce people to Coq"
(<https://arxiv.org/abs/1701.07125>). That is a reported behavioral consequence,
not a vibe: the no-install property changed *where and how the tool gets used*
(workshops, books, drive-by readers).

**NNG** is the strongest adoption case by raw reach — a web game, no install,
and by common consent the single most effective on-ramp Lean has ever had
(<https://github.com/leanprover-community/NNG4>). The survey-level reading is
that "web-based interfaces require minimal setup and installation and are
thought to be less intimidating to new users, especially students."

Note the hedge in that sentence — **"are thought to be."** That is the honest
state of the evidence.

### 2.2 The evidence against, and a very sharp fact

Here is the finding that should reframe this entire section.

**Lean4Web does not run Lean in the browser.** From the README: "In contrast to
the Lean 3 web editor, in this web editor, the **Lean server is running on a web
server, and not in the browser**"
(<https://github.com/leanprover-community/lean4web>). The reason reported in the
project's surrounding material is that there are **issues compiling Lean 4 to
WebAssembly**, and consequently the server must be defended — Lean runs inside a
**gVisor container** for isolation.

Three things follow, and they matter more than any adoption anecdote:

- **Lean 4 regressed on this axis.** Lean *3* had a genuine in-browser editor.
  Lean 4 gave it up. The flagship "browser Lean" experience today is a
  thin client in front of somebody's rented compute.
- **The no-install property was preserved by paying for servers, not by
  engineering.** Same trick as Macbeth's Gitpod. From the student's side these
  look identical; from the operator's side one is free and one is a per-user
  cost with an abuse surface.
- **Server-side execution creates an adversarial sandboxing problem that
  in-browser execution does not have.** gVisor is there because you are running
  a Turing-complete elaborator on your own metal on behalf of anonymous
  internet users. A WASM prover running in the *user's* tab has the browser's
  own sandbox doing this work, for free, with the blast radius on the user's
  machine. *(Inference, but a strong one.)*

**Server-dependent lineage.** ProofWeb is explicitly server-dependent — "a web
interface to a Coq server and many other theorem provers"
(<https://arxiv.org/pdf/2211.13513>). **Edukera** is a commercial web app
integrating Coq for verification. **PeaCoq** likewise. So the field's dominant
pattern is *client in browser, prover on a server*, and jsCoq is the outlier
that actually put the prover in the tab.

### 2.3 Honest assessment

Does no-install drive adoption? The most defensible reading:

- **Yes for the on-ramp.** NNG and jsCoq-in-workshops are real, reported effects
  on first contact. Removing installation demonstrably widens the top of the
  funnel.
- **It is necessary, not sufficient.** NNG's success is not just "it's a web
  page." It is 79 curated levels with a designed difficulty curve. Lean4Web is
  also a web page and is a *tool*, not a phenomenon. **The no-install property
  bought the audience; the curriculum earned the retention.** *(Inference)*
- **Nobody has published the clean causal study.** There is no RCT of
  install-vs-browser holding curriculum fixed. The literature says "are thought
  to be less intimidating." Treat stronger claims as marketing, including our
  own.
- **The genuinely defensible claim is not about adoption at all — it is about
  cost and operations.** In-browser execution means zero marginal compute per
  student, no gVisor, no abuse surface, no cloud bill that scales with course
  enrollment, and the thing works on a Chromebook on hotel wifi. Lean cannot
  currently offer that and *tried*. That is a durable structural fact, not a
  preference.

---

## 3. Controlled natural language and structured proof

### 3.1 Isar — the success case, and why

Isar is the one CNL-adjacent design that unambiguously won, so its reasons are
worth extracting precisely. Wenzel's framing: bridge "the semantic gap between
internal notions of proof given by state-of-the-art interactive theorem proving
systems and an appropriate level of abstraction for user-level work"
(<https://isabelle.in.tum.de/Isar/>,
<https://wwwbroy.in.tum.de/~wenzelm/papers/isar-framework.pdf>).

The design constraints, in Wenzel's own terms, were "quite contradictory": both
**declarative** and immediately **executable**. Against Mizar specifically, Isar
"is based on a few basic principles only, it is quite independent of the
underlying logic, and integrates a broad range of automated proof methods."

Why it succeeded, decomposed:

- **It solved a legibility problem that was real and acute.** "Somebody looking
  at a machine proof can have no idea what is being proved at a given point." An
  Isar proof is instead "a hierarchical structure containing explicit statements
  of assumptions and conclusions."
- **It was not a veneer.** Isar is *interpreted*, not translated-then-forgotten.
  This is the difference between a proof language and a skin.
- **It bought performance, which nobody expects.** "The proof engine is able to
  check well-structured Isar proofs more efficiently than traditional tactic
  scripts: the hierarchical structure helps to keep internal goals concise,
  without the intrusion of redundant assumptions or unused lemmas." **Structure
  is not just for humans — explicit context makes the machine's job smaller.**
  *(This is the single most transferable lesson in this note.)*
- **It stayed logic-agnostic**, so it did not have to be rebuilt per theory.

And the modern coda: Isar's readability is now cited as an *AI* asset — "one of
the specific strengths of the Isabelle platform is the Isar proof language that
allows to express formal reasoning in a way that is both human-readable and
machine-checkable," and there is active work on minimalist Isar-like proof
languages *for neural theorem proving* (<https://arxiv.org/pdf/2507.18885>).
**The thing built for human legibility in 1999 turned out to be the thing LLMs
can write.** That is not a coincidence and it is a design instruction.

### 3.2 Mizar and Naproche/SAD

**Mizar** is the ancestor and the cautionary tale. The critique from the
Naproche camp: Mizar-style proofs "are still not very readable for an average
mathematician, mainly because the syntax is more similar to a programming
language than natural mathematical language and they contain much information
that human readers consider redundant"
(<https://orbilu.uni.lu/bitstream/10993/30185/1/SDV.pdf>). Declarative is not
the same as readable.

**Naproche/SAD** pushes furthest: ForTheL input, and SAD is called "the most
successful system for producing automatically checkable formal mathematics that
can be read by humans almost like natural mathematical texts." Isabelle/Naproche
adds PIDE integration, **incremental proof checking**, and a **LaTeX dialect of
ForTheL** enabling literate formalization
(<https://link.springer.com/chapter/10.1007/978-3-030-79876-5_36>,
<https://naproche.github.io/publications.html>). Teaching use is real but small:
"various Bachelor and Master students completed formalization projects in
Naproche-SAD" across representation theory, number theory, set theory, category
theory. Bachelor's and Master's projects — not a lecture course at scale.

The EuroProofNet WG5 CNL white paper is the field's own synthesis
(<https://europroofnet.github.io/_pages/WG5/EPN_Deliverable_14___CNL_white_paper.pdf>).

### 3.3 Do NL-ish languages help learners or hinder them?

The honest answer is **it depends on what you are teaching, and the field knows
it**.

**For:**
- Massot's transfer argument is the strongest pedagogical case in the
  literature, and CNL is the mechanism: proofs that "look like natural language"
  transfer to paper (ITP 2024).
- CNL surfaces the *rhetorical* structure of proof — "let", "assume", "it
  suffices to show" — which is precisely the skill an intro-to-proofs course
  exists to build. Tactic scripts hide it.
- The Isar evidence: structure aids both reader and engine.

**Against / cautions:**
- **Uncanny valley.** A CNL that *looks* like English but accepts only a narrow
  grammar invites students to write English, get rejected, and learn that the
  computer is capricious. The failure mode is worse than an obviously formal
  syntax, because the affordance lies. Massot's mitigation is instructive and
  should be read as an admission: Verbose Lean ships a **point-and-click
  interface**, built on ProofWidgets with features contributed by Nawrocki (ITP
  2024). *(Inference)* If your CNL needed a menu so students could discover what
  sentences exist, the grammar is not discoverable by looking at it. **The
  widget is the API documentation.** That is a real finding, and any CNL we ship
  inherits the obligation.
- **Mizar's lesson:** declarative ≠ readable. Verbosity can *reduce* legibility.
- **CNL adds a layer to debug.** When a CNL step fails, the student must
  localize among: the mathematics is wrong; the CNL phrasing is unsupported; the
  underlying automation is too weak. Three very different fixes, one error
  message. *(Inference)*
- **Scale evidence is thin.** Naproche's teaching record is individual student
  projects. Verbose Lean is used in real courses at Orsay, but the ITP 2024
  paper is a design-and-experience paper and **does not report quantitative
  student outcomes**. There is no controlled study showing CNL beats tactics for
  learning. Anyone claiming otherwise is over-reading.

**Synthesis:** CNL is well-evidenced as a *transfer* device for courses whose
goal is paper-proof skill, and it is the natural front-end when the automation
underneath is strong enough that steps are chunky. It is poorly evidenced as a
general accessibility win, and it actively backfires when the grammar is
narrower than it looks.

---

## 4. Agentic proving surfaces — concrete requirements

This is the section with the clearest, most actionable evidence, because the
agent community has been unusually explicit about what the existing interfaces
get wrong.

### 4.1 The primary source: Pantograph's critique of LSP

Pantograph (<https://arxiv.org/abs/2410.16429>,
<https://github.com/leanprover/Pantograph>) is a machine-to-machine interface
for Lean 4, and its central argument is a direct indictment of using an
IDE protocol as an agent protocol. LSP "suffers from a number of problems as a
machine interface" because it requires **tracking cursor positions** and
**parsing verbose messages**. Pantograph was instead "designed from the ground
up as an efficient and convenient interface for machine (and especially machine
learning) agents."

That sentence is the thesis of this whole section: **an IDE protocol models a
human moving a cursor through a document; an agent protocol should model a
search over proof states.** These are different objects, and retrofitting the
first into the second is where the pain lives. LeanDojo
(<https://leandojo.readthedocs.io/en/latest/user-guide.html>) is the other major
entry, and Pantograph's reported advantages over it are instructive: written
entirely in Lean 4, **no Docker dependency**, faster interaction, and support
for tactics LeanDojo omits — notably `have`.

### 4.2 Enumerated requirements

Derived from Pantograph, LeanDojo, lean-lsp-mcp, and the agentic-verification
literature. This is the design checklist.

**R1 — Machine-readable goal state, as data, not as rendered text.**
The whole point. Pantograph exposes structured goal states rather than
text-based feedback. If the agent has to regex your pretty-printer, you have
built an IDE, not an agent surface. Corollary: **the pretty-printer must not be
the only serializer.** Requires a stable, versioned, sharing-preserving
serialization.

**R2 — Goal states as independent, addressable, resumable first-class values.**
Pantograph's structured goals "can be manipulated independently," and this
"enables more powerful search algorithms such as Monte Carlo Tree Search
(MCTS)." This is the deepest requirement. An agent does **tree search**: fork a
state, try a tactic, discard, backtrack, retry, compare siblings. A prover whose
only interface is "append text to a file and re-elaborate" makes every node
expansion cost a full re-check. **Proof state must be a value you can hold,
name, copy, and return to** — not a position in a buffer.

**R3 — Metavariable coupling made explicit.**
Pantograph's novel contribution. When tactics create interdependent goals —
solving one constrains another, as in existentials — those relationships must be
*visible* to the agent. An agent that treats coupled goals as independent
subproblems will "solve" them inconsistently and burn the search. Any prover
with unification variables owes the agent this dependency graph. *(This is the
requirement most likely to be overlooked in a first design.)*

**R4 — Incremental execution with feedback from partial steps.**
Pantograph "supports the use of the advanced reasoning steps (called tactics)
`have`, `let`, `conv`, and `calc`" and — critically — provides "feedback from
partially executed `conv` and `calc` tactics, which was not possible in
preceding works." An agent writing a 12-step calculation must learn that step 7
broke *at step 7*. All-or-nothing checking destroys the credit assignment an
agent needs to improve. Cf. Isabelle/Naproche's incremental checking via PIDE.

**R5 — Draft/sketch-then-refine (`sorry`-resumption).**
Pantograph allows resuming proofs marked with `sorry`, so models "produce a
proof draft before resolving the details in the proofs," separating high-level
structure discovery from low-level completion. This matches how LLMs are
actually good: strong at architecture, weak at mechanics. **A hole must be a
legal, checkable, resumable program state**, not a compile error. LeanDojo-v2
drives Pantograph-based provers specifically to "fill in sorrys"
(<https://github.com/lean-dojo/LeanDojo-v2>).

**R6 — Deterministic, localized errors.**
Implied throughout and named in the education literature independently. The
agent's next action is a function of *where* and *why* it failed. Non-local
errors (blame the wrong line) and nondeterministic errors (timeout-dependent,
hash-order-dependent) both poison the loop — the latter worse, because they
destroy the agent's ability to learn from repetition, and they destroy *our*
ability to reproduce a bug report. Determinism is an agentic requirement, not
just a hygiene one.

**R7 — Fast startup and low per-call latency.**
Pantograph's headline practical win over LeanDojo is removing Docker and
improving interaction speed. Agent loops are thousands of calls. Startup cost
multiplies by the search width. **Process-per-query is a non-starter.** This is
where "warm, incremental, resumable" stops being an optimization and becomes the
product.

**R8 — Sandboxing.**
The Lean4Web/gVisor situation is the existence proof: if you host execution, you
inherit an adversarial isolation problem
(<https://github.com/leanprover-community/lean4web>). For agents this is sharper
— an agent *will* emit hostile or runaway input, not from malice but from search.
Resource limits must be explicit, enforced, and per-call.

**R9 — Premise selection / library search as a first-class API.**
lean-lsp-mcp bundles LeanSearch, Loogle, Lean Finder, Lean Hammer, Lean State
Search precisely because agents cannot find lemmas otherwise
(<https://github.com/oOo0oOo/lean-lsp-mcp>). Recall the numbers: best-in-class
LeanExplore **55.4%**, LeanSearch **46.3%**, Moogle **12.0%** on 300 Mathlib
queries. *(Inference)* A library small enough to fit in context, or searchable
symbolically rather than semantically, sidesteps a problem the Lean ecosystem
must solve with ML. **Being small is a feature here.**

**R10 — Proof-state diffing.**
Both Pantograph and LeanDojo extract training triples of *(goal state, tactic,
post-tactic goal state)* — data "usually not available in raw Lean 4 scripts."
The delta is the learning signal and the search heuristic. A prover that can
report *what changed* is worth more than one that reports the new state and
makes the agent diff it.

**R11 — Counterexample surfaces.** See §5. Currently the weakest link across all
of these systems.

**R12 — A protocol agents already speak.**
MCP has become the integration point. **lean-lsp-mcp** (Dressler, 2025) bridges
LLMs to Lean via LSP, exposing diagnostics, goal states, term info, hover docs,
plus the search tools (<https://github.com/oOo0oOo/lean-lsp-mcp>,
<https://pypi.org/project/lean-lsp-mcp/>). It is "foundational" in agentic math
systems including **Numina-Lean-Agent** (built on **Claude Code** +
Numina-Lean-MCP, <https://arxiv.org/pdf/2601.14027>) and **LeanExplore**, where
it "acts as the exclusive mediator for all formal interactions, abstracting away
direct shell or binary invocations." There is a **Rocq-MCP** doing Putnam 2025
problems (<https://arxiv.org/pdf/2603.20405>). *(Inference)* MCP is now the de
facto agent-prover boundary; shipping without it means being driven by shell
scraping.

### 4.3 How much does the surface matter? A calibrating datapoint

From the agentic proof automation literature: **Claude Code with a single
`lean4check` tool achieves 87% success on 189 proof engineering tasks**, with
analysis showing agents "excel at mechanical proof development while still
requiring human creativity for non-trivial strategy choices."

This number cuts **both ways** and should be sat with rather than spun:

- **Against elaborate surfaces:** *one* tool, 87%. A frontier model with a
  check-this-file button is already good at mechanical proof work. The marginal
  value of R1–R12 over `lean4check` is not obviously large for that task class.
  This is a genuine argument that agentic prover tooling is over-engineered.
- **For elaborate surfaces:** 87% on *proof engineering* — mechanical work in an
  existing codebase, where the strategy is given. The residual is "non-trivial
  strategy choices," which is exactly where MCTS-style search (R2), sketching
  (R5), and counterexamples (R11) are supposed to pay. And the F*/Pulse
  "agentic proof-oriented programming" vision — humans on specs and key
  invariants, agents on proof mechanics
  (<https://risemsr.github.io/blog/2026-02-04-nik-agentic-pop/>) — presumes the
  mechanics are cheap, which presumes R7.

*(Inference)* The defensible synthesis: **a good agent surface is worth little
for mechanical tasks and a lot for search-heavy ones.** We should not claim the
former. Related: *What's in a Proof? Analyzing Expert Proof-Writing Processes in
F* and Verus* (<https://arxiv.org/pdf/2508.02733>) and *Characterizing initial
human-AI proof formalization workflows*
(<https://arxiv.org/pdf/2606.04273>) are the empirical grounding for what the
loop actually looks like.

---

## 5. The counterexample angle

### 5.1 The problem is real and it is quantified

The foundational statement is Blanchette and Nipkow's, and it is much stronger
than a hedge:

> **"Most 'theorems' initially given to an interactive theorem prover do not
> hold"** — and counterexample generators exist "to spare users the **Sisyphean
> task** of trying to prove non-theorems."
> (<https://www.tcs.ifi.lmu.de/staff/jasmin-blanchette/lpar2010-nitpick.pdf>,
> <https://isabelle.in.tum.de/doc/nitpick.pdf>)

*Most.* From the authors of the tooling. That is the thesis of this section
handed over by the ITP community itself.

**Quantified for the agentic case — this is the number that matters:**
DeepSeek-Prover reports that during large-scale autoformalization, **at least
20% of generated formal statements were incorrect even after quality
filtering**, "leading to significant computational waste if addressed with brute
force." Their mitigation is telling: **dual concurrent proof searches** on each
statement and its negation, terminating as soon as either resolves, "exploiting
logical symmetry" to prove unprovability
(<https://arxiv.org/html/2405.14333v1>).

Read that as an engineering confession. **A frontier lab burned enough compute
proving false things that they built a parallel disproof channel to stop the
bleeding — and their disproof channel is still just the prover, run backwards.**

**Learning to Disprove: Formal Counterexample Generation with LLMs**
(<https://arxiv.org/html/2603.19514v1>) makes the case an agenda:
- Motivation: current AI "focus[es] almost exclusively on proofs, neglecting
  counterexamples — which are vital for theory development, conjecture
  refinement, and strengthening LLM self-verification."
- Training on false statements yields **sparse rewards**; models plateau at low
  success without special handling.
- Benchmarks built because none existed: **For-Counter** (1,058 formal
  counterexample problems from CounterMath), **Veri-Formalize** (3K unprovable
  problems), **Veri-Reason** (3K from failed DSP+ proving attempts). *That third
  dataset is literally 3,000 recorded instances of an agent failing to prove
  something*, and it was worth curating.
- Method: symbolic mutation over **321,929 seed theorems** by dropping necessary
  hypotheses → **575K counterexample problems**; multi-reward training.
- Results: **47–74% relative improvement** in pass@1 over strongest baselines.

### 5.2 ITP counterexample tooling is weak, and its own authors say so

- **Quickcheck** "is restricted to the executable fragment of HOL (which
  excludes unbounded quantifiers) and may loop endlessly on inductive
  predicates" (<https://link.springer.com/chapter/10.1007/978-3-642-35308-6_10>).
- **Refute** "copes well with logical symbols, but inductive datatypes and
  predicates are mostly out of reach due to **combinatorial explosion**."
- **Nitpick** is the good one — SAT-based via **Kodkod**, handling unbounded
  quantification, (co)inductive predicates and datatypes, (co)recursive
  functions (<https://www.tcs.ifi.lmu.de/staff/jasmin-blanchette/tap2009-nitpick.pdf>).
  Note *what* makes it the good one: **it is the one that delegates to a
  model finder.**
- And the 2026 verdict from Learning to Disprove: symbolic tools like Isabelle's
  **nitpick** and Lean's **plausible** "rely on SAT/SMT solving but struggle
  with higher-order logic's inherent complexity," which is offered as the
  motivation for going to LLMs instead.

That last sentence deserves adversarial reading, because it is the strongest
available argument *against* our thesis and we should state it at full strength:
**the 2026 state of the art, having looked at SAT/SMT-based counterexample
finding, walked away from it and trained a model instead.** Any "we are a solver,
therefore we win at counterexamples" pitch must answer this.

The answer, such as it is: their complaint is *higher-order logic's* complexity,
not the model finder's inadequacy. Nitpick struggles because it must
approximate HOL into Kodkod's relational logic. **On a decidable fragment there
is no approximation to fail** — a QF_BV model is a complete, checkable
refutation, not a bounded search that gave up. *(Inference)* This is a real
distinction and also a much narrower claim than "solvers beat LLMs at
disproof." The honest position: **on the fragment we decide, we are not a
heuristic — and that fragment is where a large share of undergraduate and
verification-adjacent goals actually live.** Outside it we have nothing to say,
and we should say so.

### 5.3 Is "your goal is FALSE, here's why" a differentiator?

**For learners — yes, and it attacks the measured bottleneck.**
*(Inference, but well-supported.)* Recall Macbeth's 20:1. The most expensive
student interaction is the one where a student is stuck and cannot tell *which*
of these is true: (a) the statement is false; (b) it's true but my approach is
wrong; (c) it's true, approach fine, I can't find the lemma; (d) I typed it
wrong. Today only a TA distinguishes these. A **concrete falsifying assignment**
collapses (a) instantly and mechanically — and (a)/(d) together are a large
fraction of homework errors, because students mis-transcribe hypotheses and drop
side conditions constantly. Note that Learning to Disprove's *entire symbolic
mutation method* is "drop a necessary hypothesis" — they generate false
statements by simulating **exactly the mistake students make**. A counterexample
is also pedagogically superior to an error message on the dimension that
matters: it is *checkable by the student*, in their own head, against the
original statement. No elaborator literacy required. It says "n = 3 breaks
this," and the student can verify that with arithmetic. **That is the only
feedback in the entire stack that does not require understanding the tool.**

**For agents — yes, and it is nearly unclaimed.**
DeepSeek's 20%-and-dual-search and the whole Learning to Disprove agenda say the
demand is proven and the supply is bad. Every existing answer is *another prover
run* (search the negation) or *another model* (train to disprove). Both are
expensive, neither is decisive, and both fail silently. A **decision procedure
returning a model** is: cheap, terminating, and gives a certificate the agent
can check without trusting us. In R1–R12 terms: an agent that can ask "is this
even true?" before opening a proof search prunes 20% of its workload at solver
cost rather than proof-search cost. *(Inference)* **The right frame is not
"axeyum proves theorems." It is "axeyum tells you which of your goals are worth a
proof search."** That is a smaller claim and a much more defensible one.

Caveats, stated plainly:
- Decidable fragment only. Most *interesting* undergraduate analysis is out of
  reach. Bounded/finite-model refutation on the rest is exactly the
  approximation game Nitpick already loses.
- A counterexample to a goal *mid-proof* may reflect a wrong intermediate step,
  not a false theorem — this is a UX trap, and mis-labeling it would be worse
  than silence.
- No one has published that learners benefit. §5.3's learner claim is inference
  from the 20:1 constraint plus Blanchette's "most theorems don't hold," not a
  measured result. It is a hypothesis worth testing, and it is testable.

---

## 6. Creative directions: what would a 2026-native prover look like?

If designed **agent-first, browser-first, counterexample-first** rather than
retrofitted:

1. **Proof state as a value, not a cursor.** Pantograph's whole argument is that
   Lean's agent interface is an IDE protocol wearing a disguise. Design the
   *state algebra* first — fork, resume, diff, compare — and derive the human IDE
   from it. **The IDE is a client of the agent API, not vice versa.**
2. **Refutation and proof as one query, not two channels.** DeepSeek runs dual
   concurrent searches because prove-or-disprove is bolted on. A solver-native
   design answers `{proof, counterexample, unknown}` from *one* call.
   **`unknown` first-class** — already an axeyum hard rule, and it is exactly the
   discipline this needs.
3. **Every answer self-certifying.** UNSAT → checkable proof; SAT → model that
   replays against the original term. Both checkable by a small kernel the
   consumer runs themselves. This is the axeyum identity ("untrusted fast search,
   trusted small checking") pointed at a prover, and it is also the right answer
   to "why trust an agent's output."
4. **Zero-marginal-cost execution.** Lean4Web needs gVisor because it hosts
   compute; Macbeth needs Gitpod. A WASM prover in the student's tab has neither
   bill nor sandbox problem — the browser is the sandbox. This is the one place
   where a structural advantage exists rather than a preference.
5. **A library small enough to search, or searchable without ML.** LeanExplore's
   55% is what "world's best premise search over a huge library" buys. Not having
   Mathlib's size is not only a weakness.
6. **CNL as an emitted view, not the input grammar.** Invert Verbose Lean: don't
   make students guess which sentences parse (hence the point-and-click
   admission). Let them act, and *render* the result as prose. Isar's lesson —
   structure serves reader *and* engine — plus the 2026 coda that Isar-like
   languages are what LLMs write well (<https://arxiv.org/pdf/2507.18885>).
7. **Errors as counterexamples wherever possible.** "This step is wrong" is an
   elaborator's answer. "This step is wrong **at x = 3**" is a mathematician's.
8. **Incrementality as the substrate.** R4/R7 are not features; if warm
   incremental checking is not the base case, every agent loop and every
   keystroke pays full price.

**Is anyone arguing this?** Partially, and never all at once — which is the gap:
- **Agent-first:** yes, loudly. Pantograph's "designed from the ground up as an
  interface for machine agents" (<https://arxiv.org/abs/2410.16429>); MCP servers
  (<https://github.com/oOo0oOo/lean-lsp-mcp>); Numina-Lean-Agent
  (<https://arxiv.org/pdf/2601.14027>); agentic PoP
  (<https://risemsr.github.io/blog/2026-02-04-nik-agentic-pop/>); ProofWright
  (<https://arxiv.org/pdf/2511.12294>); Agentic Verification of Software Systems
  (<https://arxiv.org/pdf/2511.17330>). **But all of it is retrofit** — every one
  wraps a prover built for humans in 2015 or 1989.
- **Browser-first:** jsCoq argued it and largely won its point
  (<https://arxiv.org/abs/1701.07125>); Lean 4 conceded the ground.
- **Counterexample-first:** essentially **nobody**. Learning to Disprove
  (<https://arxiv.org/html/2603.19514v1>) is the closest and it is a *training*
  agenda, not an architecture — it accepts the prover as given and teaches a
  model to compensate.

*(Inference)* The union — agent-first + browser-first + counterexample-first,
with a solver rather than an elaborator at the center — does not appear to be
argued by anyone. That is either a real opening or a well-signposted cliff, and
the honest reason to suspect it is at least partly a cliff is §5.2: the people
who tried SAT/SMT refutation in a prover context found it insufficient and left.

---

## What this implies for axeyum

**The properties we already have that this literature says are scarce:**

1. **In-browser execution is a genuine structural asset, and rarer than it
   looks.** Lean4Web runs on a *server* with **gVisor** because Lean 4 cannot
   compile to WASM (<https://github.com/leanprover-community/lean4web>) — Lean 3
   could, and Lean 4 regressed. Macbeth pays for **Gitpod** so students don't
   install. Both are buying with money what ADR-0017 gives us for free. Zero
   marginal compute per student, no abuse surface, no cloud bill scaling with
   enrollment. **But:** no-install is documented to widen the *top of the funnel*
   (jsCoq in workshops, NNG) — it is not documented to drive retention. NNG won
   on 79 designed levels. **The WASM property buys a hearing; a curriculum earns
   the audience.** Do not confuse the two in any pitch.
2. **Determinism is an agentic requirement (R6), not just hygiene.** Our existing
   hard rule — stable iteration, explicit seeds, explicit limits, no hash-map
   order in output — is precisely what agent loops need for credit assignment and
   reproducibility. This is already-paid-for differentiation. Say so.
3. **`unknown` as a first-class result is exactly right** for a
   `{proof, counterexample, unknown}` surface. Already a hard rule.
4. **"Every `sat` must be checkable by evaluating the original term against the
   lifted model"** is, verbatim, the counterexample product. The rule that
   forbids dropping lift maps is the rule that makes §5 possible. **The
   counterexample differentiator is not new work — it is exposure of an existing
   invariant at the prover layer.**
5. **Small library is an asset (R9).** Best-in-class Mathlib premise search is
   ~55%. We should not build Mathlib.

**The honest counter-case, stated at full strength:** the 2026 SOTA looked at
SAT/SMT counterexample finding — Nitpick, `plausible` — judged it to "struggle
with higher-order logic's inherent complexity," and trained an LLM instead
(<https://arxiv.org/html/2603.19514v1>). Our answer is that their complaint is
about *approximating HOL*, and on a decidable fragment there is no approximation
to fail: a QF_BV model is a complete checkable refutation. That answer is
correct and it is **narrow**. It commits us to a claim about *which goals* live
in our fragment, and we do not currently know that number. Separately,
`lean4check` + Claude Code already hits **87%** on 189 proof-engineering tasks —
so R1–R12 are worth little for mechanical work and a lot only for search-heavy
work. We must not sell the former.

**What follows, concretely:**

- **Lead with refutation, not proof.** The framing that survives scrutiny is not
  "axeyum proves theorems" but **"axeyum tells you which goals are worth a proof
  search."** Blanchette: *most* putative theorems don't hold. DeepSeek: **≥20%**
  of filtered autoformalized statements are false, causing "significant
  computational waste," mitigated only by running the prover backwards. That is
  a measured, unclaimed, adjacent market.
- **Design the state algebra before the IDE (R1, R2, R10).** Pantograph's
  critique — LSP forces cursor-tracking and message-parsing — is a warning we can
  still act on because we have no IDE to protect. Goal states as forkable,
  resumable, diffable values; the human UI as a client of that API. Retrofitting
  this later is the single most expensive mistake available to us.
- **Metavariable coupling (R3) is the sleeper requirement.** Whatever we build
  with unification variables owes agents an explicit dependency graph. Cheap now,
  near-impossible to add later.
- **Holes must be legal states (R5), and partial steps must give feedback (R4).**
  `sorry`-resumption and per-step `calc`/`conv` feedback are what let a model do
  what models are good at (structure) and not what they're bad at (mechanics).
- **Incrementality is the substrate (R7).** `IncrementalCnf`, `IncrementalBvSolver`,
  `IncrementalLowering` (ADR-0009) are not optimizations — they are the reason an
  agent loop is affordable. Pantograph's headline win over LeanDojo was dropping
  Docker for speed. We start with no process boundary at all.
- **Ship MCP (R12).** MCP is the de facto agent-prover boundary — lean-lsp-mcp,
  Numina-Lean-Agent (on Claude Code), Rocq-MCP. Without it we get driven by shell
  scraping, which forfeits R1.
- **CNL: emit, don't parse.** If we ever do CNL, render prose *out* rather than
  parse prose *in*. Verbose Lean needed a point-and-click widget so students could
  discover the grammar — that widget is an admission the grammar isn't
  discoverable. And Isar's real lesson is the one nobody expects: **explicit
  structure made the engine faster, not just the reader happier**
  (<https://isabelle.in.tum.de/Isar/>).
- **Education is downstream, and its bottleneck is TA hours.** Macbeth's **20:1**
  is the number to design against. The pitch is not "formal proof in a browser";
  it is "the tool answers the question a TA would otherwise answer, and answers
  it in a form the student can check without understanding the tool." A
  counterexample is the only output in the whole stack with that property.
- **Two things we do not know and should stop asserting:** (i) no study shows
  CNL beats tactics for learning; (ii) no study shows counterexamples help
  learners — §5.3 is inference from 20:1 plus "most theorems don't hold." Both
  are testable. Testing (ii) on a real course would be the first evidence in the
  literature, which is a reason to do it rather than a reason to hedge.

**Foundational-DAG note:** none of this is public surface yet. Per CLAUDE.md,
prover-layer operators/encodings/evidence formats need semantics, model/proof
lifting, and replay routes made explicit before they go public, and the
research questions here (does CNL help? does counterexample feedback help
learners? which fraction of target goals fall in a decidable fragment?) belong
in `docs/research/08-planning/research-questions.md`, closed by ADR — not
settled in code.

---

## Source index

Education / CNL:
- Proof Assistants for Teaching: a Survey — <https://arxiv.org/abs/2505.13472>
- Massot, Teaching Mathematics Using Lean and CNL, ITP 2024 —
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.27>
- verbose-lean4 — <https://github.com/PatrickMassot/verbose-lean4>
- Macbeth, The Mechanics of Proof — <https://hrmacbeth.github.io/math2001/>
- Teaching "Foundations of Mathematics" with Lean — <https://arxiv.org/html/2501.03352v3>
- Natural Number Game — <https://github.com/leanprover-community/NNG4>,
  <https://cbirkbeck.github.io/natural_number_game/>
- Waterproof — <https://arxiv.org/pdf/2211.13513>; ProofBuddy —
  <https://arxiv.org/pdf/2505.13474>; Diproche — <https://arxiv.org/pdf/2202.08131>;
  Elfe — <https://arxiv.org/pdf/1801.10513>
- Isar — <https://isabelle.in.tum.de/Isar/>,
  <https://wwwbroy.in.tum.de/~wenzelm/papers/isar-framework.pdf>
- Minimalist proof language for neural theorem proving over Isabelle/HOL —
  <https://arxiv.org/pdf/2507.18885>
- Naproche/SAD — <https://naproche.github.io/publications.html>,
  <https://orbilu.uni.lu/bitstream/10993/30185/1/SDV.pdf>,
  <https://link.springer.com/chapter/10.1007/978-3-030-79876-5_36>
- EuroProofNet WG5 CNL white paper —
  <https://europroofnet.github.io/_pages/WG5/EPN_Deliverable_14___CNL_white_paper.pdf>

Browser:
- jsCoq — <https://arxiv.org/abs/1701.07125>
- lean4web (server-side; not WASM) — <https://github.com/leanprover-community/lean4web>
- Nawrocki et al., An Extensible User Interface for Lean 4 (ProofWidgets) —
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.24>

Agentic:
- Pantograph — <https://arxiv.org/abs/2410.16429>, <https://github.com/leanprover/Pantograph>
- LeanDojo — <https://leandojo.readthedocs.io/en/latest/user-guide.html>;
  LeanDojo-v2 — <https://github.com/lean-dojo/LeanDojo-v2>
- lean-lsp-mcp — <https://github.com/oOo0oOo/lean-lsp-mcp>, <https://pypi.org/project/lean-lsp-mcp/>
- Numina-Lean-Agent — <https://arxiv.org/pdf/2601.14027>
- Rocq-MCP / Putnam 2025 — <https://arxiv.org/pdf/2603.20405>
- Agentic Proof-Oriented Programming (Swamy) —
  <https://risemsr.github.io/blog/2026-02-04-nik-agentic-pop/>
- ProofWright — <https://arxiv.org/pdf/2511.12294>; Agentic Verification of
  Software Systems — <https://arxiv.org/pdf/2511.17330>
- What's in a Proof? (F*/Verus expert processes) — <https://arxiv.org/pdf/2508.02733>
- Characterizing initial human-AI proof formalization workflows —
  <https://arxiv.org/pdf/2606.04273>

Counterexamples:
- Nitpick — <https://isabelle.in.tum.de/doc/nitpick.pdf>,
  <https://www.tcs.ifi.lmu.de/staff/jasmin-blanchette/lpar2010-nitpick.pdf>,
  <https://www.tcs.ifi.lmu.de/staff/jasmin-blanchette/tap2009-nitpick.pdf>
- The New Quickcheck for Isabelle —
  <https://link.springer.com/chapter/10.1007/978-3-642-35308-6_10>
- DeepSeek-Prover (≥20% false statements; dual concurrent search) —
  <https://arxiv.org/html/2405.14333v1>
- Learning to Disprove — <https://arxiv.org/html/2603.19514v1>
