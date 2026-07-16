# Agentic surface — designing for the driver we actually have

Draft 1. See [`../critique/`](../process/critique/) for what is wrong with it.

**Citations:** every empirical claim here is sourced in
[`../research/05-education-and-agentic.md`](../research/05-education-and-agentic.md)
(Pantograph, LeanDojo, MCP-Solver, `lean4check`, the counterexample evidence) and
[`../research/02-ai-assisted-proving.md`](../research/02-ai-assisted-proving.md)
(AxProverBase, Aleph). This document argues; those document the evidence. Index:
[`../REFERENCES.md`](../REFERENCES.md).

## Why this document exists separately

Every prover in use today was designed for a human at a keyboard and has been
*retrofitted* for agents. [`../research/05-education-and-agentic.md`](../research/05-education-and-agentic.md)
found no exception: agent-first exists only as retrofit; browser-first is conceded in
practice (**Lean4Web runs Lean server-side behind gVisor** — the stronger claim
"Lean 4 cannot compile to WASM" is *unverified* and was withdrawn); 
counterexample-first is essentially unoccupied. Nobody is arguing the union.

If axeyum builds a goal layer at all, it starts in 2026 with agents as the
primary driver and humans as a secondary one. That is not a slogan — it changes
specific data structures, and most of those changes are **cheap now and
near-impossible later**.

## The single most important design lesson

Pantograph's thesis, and the one to internalize:

> **An IDE models a cursor in a document. An agent models a search over states.**

LSP fails as an agent interface not because it is slow but because it demands
cursor-tracking and message-parsing from a client that wants neither. The agent
does not want to *edit a file and see what happens*. It wants to hold N candidate
states, expand the promising ones, and abandon the rest.

Everything below follows from taking that seriously.

## Requirements, in dependency order

Ordered by *when the decision must be made*, not by importance. The first three
are architectural and cannot be added later.

### 1. Goal state as data, not rendered text — **decide now**

A goal is a serializable value: context + proposition + metadata. Not a
pretty-printed string an agent must parse back.

Axeyum's determinism hard rule (stable iteration order, no hash-map iteration in
output) makes goals *canonically* serializable — which is worth more than it
sounds. Two identical goals produce identical bytes, so an agent can dedupe,
cache, and hash states for free. Lean cannot promise this.

### 2. Forkable, resumable states — **decide now; retrofitting is near-impossible**

A goal state must be cheap to clone and independently advanceable. This is what
makes MCTS, beam search, and parallel agent exploration possible at all.

Axeyum's existing architecture is unusually well-placed: `Copy` handles, interned
terms, no global mutable state, `IncrementalSat`/`IncrementalCnf` with push/pop.
The substrate should expose forking as a first-class operation from day one.

**The sleeper requirement**, called out in note 05 and easy to skip: **explicit
metavariable coupling** — when two goals share a metavariable, an agent must be
able to know that solving one constrains the other. It is cheap to record while
designing the goal representation and effectively unrecoverable afterward. If
P6.2 chooses an obligation type outside the kernel, this must be designed in
there.

### 3. Deterministic, localized, structured errors — **mostly already true**

Errors must say *what* failed, *where*, and *why*, as data — not prose.

Uncomfortable observation, recorded honestly: axeyum's hard rules (determinism,
explicit seeds and resource limits, `unknown` as a first-class result, no global
mutable state, incrementality) happen to be **exactly the agent-fitness
checklist**. That is luck, not foresight. The rules were adopted for
reproducibility and soundness, and they land on agent-fitness by coincidence.

The consequence is that **the real gap is exposing structured errors, not
producing them**. We already have the information; it is not on the wire. That
makes T6.4.2 much cheaper than it looks — and means we should not congratulate
ourselves for a property we got by accident.

### 4. Fast startup — cheap, and it decided a real competition

Pantograph's practical win over LeanDojo was **dropping Docker**. Not algorithms
— startup latency. An agent doing thousands of speculative checks pays startup on
every one.

A statically-linked Rust binary with no toolchain, no C++ dependency, and no
container is a structural advantage. Combined with WASM, the substrate can run
*in the agent's own process*.

### 5. Holes as legal states — `fail`, never `sorry`

An agent must be able to hold a partial proof with named holes and attack them in
any order. Two rules, both non-negotiable:

- A hole is **tracked** — never silently discharged, never assumed.
- A hole is **not a theorem**. `PLAN.md:619` already states it: *fail, not
  `sorry`*.

This is where an agent-first system is most tempted to cheat, because a plausible
hole makes the demo work.

### 6. Counterexamples as a first-class answer — **the differentiator**

The agent's most valuable question is not "prove this." It is **"is this worth
trying to prove?"**

Blanchette and Nipkow, from inside the ITP community: *"Most 'theorems' initially
given to an ITP do not hold."* DeepSeek-Prover found ≥20% of autoformalized
statements false after filtering, called it "significant computational waste," and
built a concurrent disproof channel — a lab ran its prover backwards because
proving false things was burning real money.

An agent that learns a goal is false in 50ms instead of after a 300-second search
is strictly better off, and the saving compounds across a search tree.

**The honest caveat, which the plan must carry:** this depends entirely on
T6.1.4 (`sat` lifted back into CIC and checked against the original goal). Until
that exists, a counterexample is a *confident wrong answer* waiting to happen —
worse than none. And the *Learning to Disprove* authors looked at SAT/SMT
refutation, judged it inadequate for higher-order logic, and trained an LLM
instead. Our reply — their complaint is about *approximating* HOL, and on a
decidable fragment there is nothing to approximate — is correct but narrow, and
it commits us to a fragment-coverage number we do not have.

### 7. Premise search — deprioritize

Best Mathlib premise search reaches 55.4%; LeanSearch 46.3%; Moogle 12.0%.

But we have no library, so we have no premise-selection problem. And LeanHammer's
residual is **43.6% translated-but-unproven** — solver strength, not premise
selection, which is already within ~6 points of its oracle ceiling.

For us this is a non-problem that we should not import out of imitation.

### 8. MCP — the transport, not the design

Last on purpose. MCP is how the surface is *reached*; it is not what makes the
surface good. Building MCP over a bad goal representation produces a bad agent
tool with good transport.

## The calibration that prevents overselling

**`lean4check` + Claude Code reaches 87% on 189 proof-engineering tasks with one
tool.** One. Not a rich search API — a checker and a loop.

And AxProverBase's own ablation ranks **iterative refinement ≫ memory ≫ tools
("marginal")**.

The honest reading: **a rich agent surface buys little for mechanical work and a
lot only for search-heavy work.** If the workload is "fix this proof until it
compiles," a checker and a loop win, and everything in this document is
overhead.

So the surface must be justified by search-heavy workloads — large obligation
sets, parallel exploration, counterexample-guided pruning — and we should not
sell it for the mechanical case. That also implies the cheapest honest test of
this whole thesis: **P6.4 over existing automation, before P6.3 exists.** If a
`lean4check`-shaped loop matches it, the surface is not the product.

## What we uniquely have

Not aspiration — properties that already hold or fall out of standing policy:

| Property | Status | Why agents care |
|---|---|---|
| WASM deployment | ADR-0017; **Lean 4 cannot do this at all** | Runs in the agent's process, in a browser, in a sandbox |
| No C/C++ dependency | Hard rule | No toolchain, no container, instant start |
| Determinism | Hard rule | Cacheable, dedupable, reproducible search |
| `unknown` as a value | Hard rule | Honest failure instead of a hang |
| Checkable `sat` | Hard rule | Counterexamples that can be trusted |
| Incrementality | ADR-0009 | Fork/resume is native, not bolted on |

The pattern is uncomfortable and worth stating: **we did not build these for
agents.** They came from soundness and reproducibility discipline. The agentic
story is largely a matter of *exposing* what the hard rules already forced —
which is why it is cheap, and why it is not evidence of foresight.

## The workload to design against

Not competition mathematics. Note 02 is blunt: miniF2F has >50% mis-formalized
statements, 16 unprovable, 300+ corrected. **Do not measure axeyum on
competition math.**

Design against: an agent handed a Rust crate, or a diff, or a SymCrypt-class
obligation set, that must decide which obligations are dischargeable, discharge
them, produce checkable evidence, and report legibly on the rest.

That workload is search-heavy, decidable-fragment-dominated, counterexample-rich,
and nobody's agent surface is shaped for it.
