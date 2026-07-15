# AI-Assisted Theorem Proving: State and Direction of Travel

Research note for the axeyum prover track. Compiled 2026-07-15. Every number
carries a source URL. Where a number is contested or measured under a broken
benchmark, that is stated inline — several headline figures in this field do
not survive contact with their own benchmarks.

**Bottom line up front.** The architecture question is settled in a direction
that was not obvious in 2024: *general agent + fast verifier feedback loop*
beats *specialized fine-tuned prover*. Competition-math benchmarks are
saturated and partly broken. The interesting open ground is no longer
"generate a Lean proof" — it is the automation the agent calls *into*, and the
speed and quality of the feedback it gets back. The counter-thesis (§6) is
half-right in a way that constrains axeyum sharply but does not kill it.

---

## 1. Neural proof search in ITPs: the 2023 baseline and what happened to it

The LeanDojo line established the modern setup: extract proof states from Lean,
train a retrieval-augmented tactic generator, do best-first search.

| System | Benchmark | Result | Source |
|---|---|---|---|
| ReProver | LeanDojo benchmark | 51.2% of theorems proved | [leandojo.org](https://leandojo.org/leandojo.html) |
| ReProver | miniF2F-test (Lean) | 26.5% Pass@1 | [arXiv:2306.15626](https://arxiv.org/pdf/2306.15626) |
| ReProver | ProofNet | 13.8% Pass@1 (first reported result on the dataset) | [arXiv:2306.15626](https://arxiv.org/pdf/2306.15626) |
| LeanAgent | miniF2F-test (Lean 4) | 38.1% Pass@1 (93/244) vs ReProver 34.0% (83/244) | [arXiv:2410.06209](https://arxiv.org/pdf/2410.06209) |

Supporting infrastructure: **Lean Copilot** runs LLM inference natively inside
Lean 4, so the model is a tactic rather than an external
process ([arXiv:2404.12534](https://arxiv.org/html/2404.12534v2)). **LeanDojo**
itself is the data-extraction substrate — 98,734 theorems from 3,384 Lean
files ([leandojo.org](https://leandojo.org/leandojo.html)). **LLMLean** and
**LeanAgent** extend to lifelong/continual learning over evolving repos.

**Movement 2023→2026.** The stepwise-search-with-retrieval paradigm went from
SOTA (26.5% miniF2F) to *obsolete* in about two years. It was not beaten by a
better tactic generator; it was bypassed. Nothing in the current top ten uses
best-first tactic search as its primary engine. This is the single most
important trend line in the section, and it is a cautionary tale about
building infrastructure tightly coupled to one search paradigm.

**miniCTX** is the benchmark that still matters from this lineage, because it
tests the thing miniF2F does not: proving theorems that depend on *context not
seen in training* — definitions, lemmas, file structure from live projects
(PrimeNumberTheorem, PFR, Math2001, recent Mathlib), 200 theorems
([arXiv:2408.03350](https://arxiv.org/pdf/2408.03350),
[cmu-l3.github.io/minictx](https://cmu-l3.github.io/minictx/)). File-tuned
models (33.61%) beat state-tactic models (32.79%), and the gap widens with
richer context. miniCTX is the honest benchmark: it is *not* saturated, and it
measures the real-world case where the library is unfamiliar. Note the direct
implication — performance on unfamiliar context is what a *new* ecosystem
looks like to a model. That number being ~33% rather than ~3% is a data point
for §6.

## 2. The big systems: which architecture won

### AlphaProof / AlphaGeometry — RL + autoformalization at scale

AlphaProof is AlphaZero-shaped: an RL agent that learns to find formal proofs,
trained on millions of auto-formalized problems translated into Lean 4. With
AlphaGeometry it solved 4/6 IMO 2024 problems — silver-medal
equivalent — including Problem 6, solved by only 5 of 609 human contestants
([DeepMind](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/);
Nature, ["Olympiad-level formal mathematical reasoning with reinforcement
learning"](https://www.nature.com/articles/s41586-025-09833-y)). Key mechanism:
**Test-Time RL** — generating and learning from millions of *problem-specific*
variants at inference time
([julian.ac analysis](https://www.julian.ac/blog/2025/11/13/alphaproof-paper/)).

The lesson usually mis-drawn from AlphaProof is "RL won." The lesson actually
supported is **test-time compute against a verifier won**. AlphaProof's headline
results come from spending enormous inference-time search against Lean's
checker. The verifier is the reward function. That reframes the whole stack:
the checker is not a downstream gate, it is the training signal and the search
oracle, and its *throughput* is the binding constraint.

### The open whole-proof generators

| System | miniF2F-test | PutnamBench | Source |
|---|---|---|---|
| DeepSeek-Prover-V2-671B | 90.6% | 47 solved (Pass@1024) | [HF model card](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B) |
| Kimina-Prover (72B) | 92.2% (best config) | — | [arXiv:2504.11354](https://arxiv.org/pdf/2504.11354) |
| Goedel-Prover-V2-32B | 88.0% Pass@32 standard; **90.4% self-correction** | 86 solved (Pass@192, self-correction); 43 (Pass@32 standard) | [HF model card](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B), [arXiv:2508.03613](https://arxiv.org/pdf/2508.03613) |
| Goedel-Prover-V2-8B | 84.6% Pass@32 | — | [HF model card](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B) |
| Goedel-Prover-V1 | frontier open-source at release | — | [arXiv:2502.07640](https://arxiv.org/pdf/2502.07640) |
| Seed-Prover (ByteDance) | SOTA at release; lemma-style deep/broad reasoning | Seed-Prover 1.5: 581 solved | [arXiv:2507.23726](https://arxiv.org/pdf/2507.23726), [PutnamBench LB](https://trishullab.github.io/PutnamBench/) |
| Pythagoras-Prover-32B | 93.03% @ pass@2048 | — | [arXiv:2606.12594](https://arxiv.org/pdf/2606.12594) |

Two facts worth dwelling on. First, **Goedel-Prover-V2-8B matches
DeepSeek-Prover-V2-671B at ~1/100th the size**
([blog.goedel-prover.com](https://blog.goedel-prover.com/)). Parameter count is
not the active ingredient. Second, **self-correction is worth ~2.4 points on
miniF2F and doubles PutnamBench yield** (43→57 at Pass@32,
[HF](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B)). Self-correction
is just "compile, read the error, try again." The gains credited by Goedel-V2
are scaffolded data synthesis + verifier-guided self-correction
([arXiv:2508.03613](https://arxiv.org/pdf/2508.03613)); Seed-Prover credits
iterative refinement + broad search + intermediate lemmas + Lean verifier
feedback ([arXiv:2507.23726](https://arxiv.org/pdf/2507.23726)).

Every one of those credited mechanisms is **a loop around the checker**.

### The 2026 result that settles the architecture question

**AxProverBase — "A Minimal Agent for Automated Theorem Proving"**
([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)):

- **miniF2F: 98.0% pass@1**
- **PutnamBench: 54.7% pass@1** (Claude Opus 4.5, 32k thinking tokens, 50 iterations)
- FATE-M 66.0%, FATE-H 24.0%, LeanCat 59.0%

Architecture: a ReAct proposer, a compiler + reviewer agent, and a memory
module ("lab notebook"). That is all. **A general model with plain scaffolding
outperforms DeepSeek-Prover-V2 and Goedel-Prover-V2 — the specialized,
fine-tuned, RL-trained provers — on most benchmarks.**

The ablation is the punchline. Ranked by impact:

1. **Iterative refinement** — "the largest performance gain out of any other element"
2. **Memory management** — significant
3. **Tools** (LeanSearch premise retrieval, web search) — **"marginal"**

Premise search — the thing the entire ReProver/hammer line optimizes — was
*marginal*. The compile-fix loop was everything.

**Aleph** (Logical Intelligence) then took PutnamBench to **668/672 = 99.4%**
on 2026-06-26, and in the process found and corrected ~15 flawed formal
statements (~2% of the benchmark)
([logicalintelligence.com](https://logicalintelligence.com/blog/aleph-solves-putnambench)).
Architecture: "a recursive and interactive state management system with **highly
parallel Lean verification calls**" — an agentic orchestration layer over
planning/proving/refining, currently paired with GPT-5.2, coordinating separate
calls to a variety of reasoning models. Not a fine-tuned prover. Not RL. An
orchestrator whose stated core competency is *parallel verifier throughput*.
Compare the fine-tuned specialists on the same board: Goedel-Prover-V2 86,
DeepSeek-Prover-V2 47 ([PutnamBench LB](https://trishullab.github.io/PutnamBench/)).

**Verdict on "which architecture won":** whole-proof generation lost. Stepwise
neural search lost. RL is a component, not an architecture. **What won is an
agent loop with memory, iterating against a fast, parallel, machine-readable
verifier.** The model is a commodity input; the *verification substrate* is the
differentiator. Aleph's own description of its edge is not a model claim — it is
a systems claim about parallel verification calls.

### Benchmark integrity — read before trusting any number above

**miniF2F is broken and saturated.** "miniF2F-Lean Revisited"
([arXiv:2511.03108](https://arxiv.org/html/2511.03108v1)):

- **More than half** of miniF2F problems have mismatches between informal and formal statements.
- **16 problems across test and validation have no solution in their current form.**
- The authors corrected **over 300** of the 488 Lean statements.
- Reported autoformalization accuracy is "largely inflated" because it is graded by LLMs, not humans.

At 98.0% pass@1 (AxProverBase) against a benchmark where >50% of statements are
mis-formalized and 16 are unprovable, miniF2F has stopped measuring proving
ability. PutnamBench at 99.4% is in the same terminal condition — Aleph had to
*fix the benchmark* to finish it. **Competition math is done as a research
driver.** miniCTX (~33%), FATE-H (24.0%), and real verification workloads are
where the remaining signal is.

## 3. Hammers: how much real proof effort do they actually close?

This section is the most decision-relevant for axeyum, because a hammer is
exactly "call an automated prover from an ITP and reconstruct the proof."

**Sledgehammer (Isabelle)** — the mature reference point:

- PISA benchmark: **38.3%** proof rate ([Magnushammer, arXiv:2303.04488](https://arxiv.org/html/2303.04488))
- miniF2F: **9.9% valid / 10.4% test**; with heuristics **18.0% / 20.9%** ([Draft-Sketch-Prove, arXiv:2210.12283](https://arxiv.org/pdf/2210.12283))
- Magnushammer (transformer premise selection) lifts PISA to **59.5%** ([arXiv:2303.04488](https://arxiv.org/html/2303.04488))

**CoqHammer**: reproved **44.5%** of the Coq standard library
([QED at Large, arXiv:2003.06458](https://arxiv.org/pdf/2003.06458)).

**LeanHammer** — premise selection + Aesop + lean-auto + Duper, the first
domain-general Lean hammer ([arXiv:2506.07477](https://arxiv.org/html/2506.07477v1)):

- **33.3%** of Mathlib-test theorems proved (large model, cumulative mode); **37.3%** accumulated across model sizes
- With **ground-truth premises the ceiling is only 43.0%** — the system already reaches 73.5–79.4% of its own oracle ceiling
- Premise retrieval: **72.7% recall@32** vs MePo's 42.1%
- **21.7%** of theorems cannot be translated to TH0 for external solvers at all; a further **43.6%** translate but Zipperposition cannot prove them
- Honest self-assessment: "LeanHammer is good at filling in small gaps in proofs" — nearly all solved theorems used only 1–2 lines of human proof

**Read this carefully, because it cuts against the obvious axeyum pitch.**
Premise selection is *already near its ceiling*: retrieval is at 72.7% recall@32
and perfect premises would buy only 43.0% vs the achieved 37.3%. **Better
premise selection is worth at most ~6 points.** The bottleneck is elsewhere —
**21.7% untranslatable + 43.6% translated-but-unproven**. That second number is
the one with axeyum's name on it: two-thirds of the residual is *the external
prover not being strong enough on goals it was successfully handed*.

And yet: AxProverBase found premise-search tools "marginal"
([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)). Both things are true.
Hammers close small gaps mechanically; agents close large gaps by iterating.
Hammers are ~35% *of small gaps*, not ~35% of proof effort. **Hammers are a
productivity tool inside a proof, not a proof strategy** — and an agent that can
retry 50 times partially substitutes for them.

**lean-smt** ([arXiv:2505.15796](https://arxiv.org/html/2505.15796v1),
[CAV 2025](https://hanielbarbosa.com/papers/2025cav.pdf)) is the closest
existing thing to axeyum's shape: preprocess the Lean goal, emit an SMT query to
cvc5, take back a Cooperating Proof Calculus (CPC) proof, replay it as a Lean
proof. Its measured numbers are the most important in this note:

- Reconstruction is fast for most problems: **98% under 1s**
- But on SMT-LIB: **cvc5+lean-smt verified 14,099 complete proofs (71% of produced proofs)** vs **cvc5+Ethos 18,018 (98%)**
- Stated causes: **"Lean is not as fast at proof checking as Coq"**, and **"lack of specialized support for arrays in Lean's kernel"**
- Currently ~200 proof rules; extending coverage and lean-auto/HOL integration is future work

**A 27-point reconstruction gap between checking a cvc5 proof in Lean (71%) and
checking it in a dedicated checker (98%)** is a real, measured, unsolved
engineering hole — and it is a *checker throughput and kernel-support* problem,
not a solver problem. Hold that thought for §7.

## 4. Autoformalization

**Statement-level NL→formal is the load-bearing case, and the reported numbers
are not real.** From miniF2F-Lean Revisited
([arXiv:2511.03108](https://arxiv.org/html/2511.03108v1)):

- Best autoformalizer on miniF2F: **~97% reported** — *LLM-graded*
- Human expert verification of the same Herald outputs: **62.7%–69.7%**
- **Kimina-Autoformalizer: ~40% of statements fail syntax validation outright**; survivors "exhibit subtle misalignments with the original queries"
- End-to-end (autoformalize + prove + check the proof against the *original informal* statement): **34.8%**, down from 97% and 70.8% measured individually

That 97% → 66% → 34.8% cascade is the most important set of numbers in this
note after §2's. **Autoformalization is the weakest link in the entire stack and
it is systematically over-reported because it is graded by the same class of
model that produces it.** Any pipeline that autoformalizes and then proves is
sound-looking and wrong ~2/3 of the time at the statement level.

Better methodology exists: **BEq+** declares two formal statements equivalent
only when *bidirectional proof search succeeds in both directions*
([arXiv:2511.03108](https://arxiv.org/html/2511.03108v1)) — i.e. the fix for
"LLM says it's a faithful formalization" is *to prove it*, which is a load on
the solver. **StepFun-Formalizer** ([arXiv:2508.04440](https://arxiv.org/html/2508.04440v2))
and **Autoformalizer with Tool Feedback** ([arXiv:2510.06857](https://arxiv.org/html/2510.06857))
both attack this by putting the compiler in the loop; "Characterizing
Paraphrase-Induced Failures in Lean 4 Autoformalization"
([arXiv:2604.23135](https://arxiv.org/html/2604.23135)) shows the failures are
not random but triggered by surface rewording — a robustness problem, not a
capability problem.

AlphaProof, notably, made autoformalization work *at scale* by not caring about
per-statement fidelity: millions of auto-formalized problems as RL training
substrate, where noise averages out
([Nature](https://www.nature.com/articles/s41586-025-09833-y)). That works for
training. It does not work when a user asks you to prove *their* theorem.

**Formal→NL explanation** is the healthier direction (it degrades gracefully —
a bad explanation misleads, it does not silently prove the wrong thing). APRIL
pairs compiler diagnostics with *natural-language diagnoses* as an explicit
training target ([arXiv:2602.02990](https://huggingface.co/papers/2602.02990)),
which is the useful framing: explanation as a first-class output of the error
path.

## 5. Agentic proving: what the loop looks like, and what a prover must expose

The universal workflow in 2026 is **write proof → compile → read errors → fix →
repeat** ([arXiv:2603.20405](https://arxiv.org/pdf/2603.20405)). Everything else
is detail.

Concrete infrastructure now in place:

- **lean-lsp-mcp** ([github.com/oOo0oOo/lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)):
  MCP methods map **one-to-one to internal Lean LSP commands**, with uniform
  naming, **standardized JSON returns**, error recovery, **message batching, and
  concurrent call handling** ([emergentmind](https://www.emergentmind.com/topics/lean-lsp-mcp)).
  It underpins Numina-Lean-Agent ([arXiv:2601.14027](https://arxiv.org/pdf/2601.14027)),
  LeanExplore, and Numina-Lean-MCP.
- **Rocq-MCP** — same pattern for Rocq ([arXiv:2603.20405](https://arxiv.org/pdf/2603.20405)).
- **APRIL / proof repair**: 260,000 supervised tuples pairing generated failures
  with compiler diagnostics and aligned repair + explanation targets
  ([arXiv:2602.02990](https://huggingface.co/papers/2602.02990)) — proof repair
  from compiler feedback is now a *trained skill*, not an emergent one.
- **Proof-Refactor**: a four-phase agentic refactoring framework built on
  **Claude Code + lean-lsp-mcp** ([arXiv:2606.03743](https://arxiv.org/pdf/2606.03743)).
- **LAMP**: Lean-based agentic framework with MCP and proof repair ([arXiv:2606.28841](https://arxiv.org/html/2606.28841v1)).
- **Draft-Sketch-Prove** remains the durable decomposition pattern ([arXiv:2210.12283](https://arxiv.org/pdf/2210.12283)); Seed-Prover's lemma-style reasoning is its descendant.
- **LongCat-Flash-Prover**: agentic tool-integrated RL — the loop itself becomes the RL environment ([arXiv:2603.21065](https://arxiv.org/pdf/2603.21065)).

### What a prover must expose to be good for an agent

Derived from the evidence above, in rough order of measured importance:

1. **Fast feedback.** Iterative refinement is the top-ranked gain
   ([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)) and self-correction
   is worth 43→57 on PutnamBench ([HF](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B)).
   Latency per iteration *is* the capability ceiling: iterations/hour × yield-per-iteration.
2. **Parallelism.** Aleph's stated core competency is "highly parallel Lean
   verification calls" ([logicalintelligence.com](https://logicalintelligence.com/blog/aleph-solves-putnambench));
   lean-lsp-mcp explicitly supports concurrent call handling. Agents fan out;
   a serial prover throttles the whole loop.
3. **Machine-readable goal state and deterministic, localized errors.**
   Standardized JSON returns, one-to-one command mapping. An error that says
   *which* subterm failed and *why*, identically on every run, is a training
   signal (APRIL's 260k tuples exist because Lean's diagnostics are
   structured enough to learn from). Nondeterministic or global errors are
   worse than useless — they poison the memory module.
4. **Incrementality + no global mutable state.** Both follow from (2): you
   cannot fan out over a prover with a global environment, and you cannot
   iterate cheaply if every attempt re-checks the world. This is a *design-time*
   property; it cannot be retrofitted.
5. **Search/premise API** — genuinely **lower priority than the field assumes**.
   Tools were "marginal" ([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1))
   and premise selection is within ~6 points of its oracle ceiling
   ([arXiv:2506.07477](https://arxiv.org/html/2506.07477v1)). Expose it; do not
   build the product around it.
6. **Explanations on the error path** ([arXiv:2602.02990](https://huggingface.co/papers/2602.02990)).

Note that items 1–4 are *systems* properties, not logic properties. The agentic
turn has revalued the field's inputs: cleverness in search is depreciating,
throughput and interface discipline are appreciating.

## 6. The counter-thesis: does Mathlib + the Lean corpus make a new prover pointless?

**Stated fairly, at full strength:** Every serious result in §2 is in Lean 4.
The overwhelming majority of LLM prover research targets Lean rather than
Isabelle or Rocq ([survey](https://www.emergentmind.com/topics/llm-based-theorem-provers)).
Mathlib is >1M lines (some sources say 2M) of community-maintained mathematics
with an extensive network of definitions, lemmas, and automation
([arXiv:2509.06493](https://arxiv.org/pdf/2509.06493),
[Lean FAQ](https://lean-lang.org/faq/)). Models have memorized Lean syntax,
Mathlib naming conventions, and idiomatic tactic usage. Tooling (LeanDojo,
lean-lsp-mcp, Lean Copilot, LeanSearch) is Lean-first. A new prover starts with
zero library, zero corpus, zero tooling, and zero model familiarity — and the
gap compounds, because each new Lean result generates more Lean training data.
This is a textbook network effect, and network effects do not yield to better
engineering. On this account, building prover infrastructure outside Lean in
2026 is building a better fax machine.

**This is a serious argument and it is substantially correct about
research-grade mathematics.** For proving theorems *about Mathlib's subject
matter, in Mathlib's idiom, against Mathlib's 1M lines of accumulated
definitions*, the network effect is real and probably decisive. axeyum will not
out-Mathlib Mathlib, ever, and any plan premised on doing so should be killed
on sight. miniCTX's ~33% ([cmu-l3.github.io/minictx](https://cmu-l3.github.io/minictx/))
shows models struggle even with *unfamiliar Lean context* — an unfamiliar
*system* is strictly harder.

**Now the evidence against — which is stronger than expected, and specific.**

**(a) The decisive experiment has been run, and library scale lost.**
miniF2F-Dafny ([arXiv:2512.10187](https://arxiv.org/html/2512.10187)) ports
miniF2F to Dafny — a system with an SMT backend, a *tiny* library, and *far*
less LLM training exposure than Lean. The foundation is **283 lines of
axiomatized definitions and 938 lines of lemmas, versus Mathlib's ~2 million
lines**. Results:

- **Dafny empty-proof baseline (i.e. pure SMT, no proof at all): 95/244 = 38.9% test, 43.4% validation**
- **Lean's `grind`, its most powerful automation tactic: 79/244 = 32.4%**
- **Claude Opus 4.6 on Dafny: 62.7% cumulative pass@4**
- Complementarity: 67 problems solved by both, **28 only by Dafny**, 12 only by grind
- Dafny-only wins concentrate in **algebra and number theory** — "SMT solvers excel at arithmetic-heavy problems"

A system with **0.06% of Mathlib's library size** beats Lean's flagship
automation on the same benchmark, with an *empty proof*. The paper's own
conclusion: extensive libraries are **not decisive** for baseline performance;
"SMT automation's domain-specific strengths appear more influential than library
scale for this problem class." The stated bottleneck is **verification
brittleness** ("minor variations in assertion order or calc organization cause
verification failure") and language-specific idioms — *not* missing library, and
*not* missing training data.

**(b) Cross-ecosystem parity, with a shared bottleneck that is not corpus.**
Cross-system evaluations report **proving performance is comparable across
Dafny, Verus, and Lean, and the primary bottleneck is shared: the absence of
auxiliary lemmas and annotations needed to guide automated proving**
([arXiv:2512.10187](https://arxiv.org/html/2512.10187), and see
[HotOS 2025](https://users.cs.duke.edu/~mlentz/papers/llmverif_hotos2025.pdf)).
If the corpus network effect were decisive, performance would track corpus size.
It does not. The bottleneck is *hint synthesis*, which is a reasoning task the
model does from the goal state and the error message — inputs a new system can
supply on day one.

**(c) Frontier models transfer to unfamiliar systems via tooling alone.**
Claude Opus 4.6 + Rocq-MCP does Putnam 2025 in **Rocq** with no Rocq-specific
training regime ([arXiv:2603.20405](https://arxiv.org/pdf/2603.20405)). The
paper's finding is exactly on point: success "hinges on the MCP integration
enabling tight feedback loops," and **"proof assistant choice matters less than
the quality of LLM-tooling integration."** The moat, if any, is the *feedback
interface* — which is buildable — not the corpus, which is not.

**(d) The corpus advantage is being commoditized by the agent loop.** The
mechanism by which Lean familiarity helps is: the model writes syntactically
valid, idiomatic Lean on the first try. But the winning architecture *does not
need first-try correctness* — it needs 50 cheap tries with good errors
([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)). Iterative refinement
was the top-ranked gain and premise tools were marginal. An agent that can
compile-fix its way through unfamiliar syntax has converted a *knowledge* moat
into a *latency* cost. That is precisely the trade a fast prover wins.

**(e) The corpus is smaller than the network-effect story implies.** Mathlib is
~110k theorems ([arXiv:2509.06493](https://arxiv.org/pdf/2509.06493)) — tiny
next to NL pretraining corpora. Lean familiarity is real but it is thin, which
is why frontier models can pick up Rocq from an MCP server.

**(f) Fine-tuning on the corpus is losing to general models anyway.** The
systems that maximally exploit Lean-specific training data — DeepSeek-Prover-V2,
Goedel-Prover-V2, Kimina-Prover — are now *beaten* by a general model with a
compile loop ([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)) and
crushed by an orchestrator on PutnamBench (Aleph 668 vs Goedel 86 vs DeepSeek
47; [PutnamBench LB](https://trishullab.github.io/PutnamBench/),
[logicalintelligence.com](https://logicalintelligence.com/blog/aleph-solves-putnambench)).
If Lean-corpus fine-tuning were the moat, the Lean-corpus fine-tunes would be
winning. They are not.

**Honest synthesis.** The counter-thesis is **true for one thing and false for
another, and the boundary is sharp**:

- **True:** building a *new proof assistant / new surface language / rival
  mathematical library* is dead on arrival. Mathlib's network effect is real,
  compounding, and unbeatable by engineering. Anyone proposing that should stop.
- **False:** building the *automation a prover calls into* is not corpus-gated
  at all. The Dafny result (§6a) is the proof: an SMT backend with a 1,200-line
  library beats Lean's best tactic on shared problems, and the SMT-shaped wins
  are exactly in arithmetic-heavy algebra and number theory — axeyum's fragment.
  The residual in LeanHammer is **43.6% translated-but-unproven**
  ([arXiv:2506.07477](https://arxiv.org/html/2506.07477v1)) — solver strength,
  not corpus. The residual in lean-smt is **71% vs 98% reconstruction**
  ([arXiv:2505.15796](https://arxiv.org/html/2505.15796v1)) — checker
  throughput and kernel array support, not corpus.

The counter-thesis kills a track axeyum should not have been on. It does not
touch the one the evidence points to. But note the survivorship condition
honestly: this only holds if axeyum is *complementary infrastructure Lean calls
into*, not a competitor for the same users. The moment the pitch becomes "use
axeyum instead of Lean," the counter-thesis wins outright.

## 7. What this implies for axeyum

**1. Do not build a prover that competes with Lean. Build the thing Lean's
agents are bottlenecked on.** §6 is decisive on the boundary. The
network-effect argument annihilates a rival proof assistant and says almost
nothing about a solver/checker backend. axeyum's actual assets — a strong SMT
solver, an in-tree Rust Lean-kernel port, and proof certificates — are *not* on
the wrong side of that line. A "prover layer" framed as a rival front-end
should be killed. Framed as backend automation + verification throughput, the
counter-thesis does not reach it.

**2. The single best-evidenced opportunity is the lean-smt reconstruction gap.**
cvc5+lean-smt verifies **71%** of produced proofs; cvc5+Ethos verifies **98%**
([arXiv:2505.15796](https://arxiv.org/html/2505.15796v1)). The named causes are
"Lean is not as fast at proof checking as Coq" and **"lack of specialized
support for arrays in Lean's kernel."** axeyum has a Rust Lean-kernel port
(fast checking) and an array-eliminating rewrite path already shipped
(`eliminate_arrays`, QF_ABV→QF_BV, ADR-0010). That is an uncomfortably precise
match between a measured 27-point industry gap and existing in-tree capability.
This is the highest-value, lowest-speculation target in this note.

**3. Optimize for iterations/second, not cleverness.** The measured ranking is
unambiguous: iterative refinement ≫ memory ≫ tools
([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)); self-correction
doubles PutnamBench yield ([HF](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-32B));
Aleph's stated edge is *parallel verification calls*
([logicalintelligence.com](https://logicalintelligence.com/blog/aleph-solves-putnambench)).
For axeyum this means the agent-facing metrics are **p50/p99 latency to a
verdict, queries/second under fan-out, and incremental re-check cost** — not
PAR-2 on a corpus. The existing `IncrementalBvSolver` (push/pop/assume,
ADR-0009) and `IncrementalCnf` are the right primitives; the roadmap should
start *measuring them as agent-loop metrics*.

**4. axeyum's hard rules are, by luck or taste, already the agent-fitness
checklist.** Compare §5's list against CLAUDE.md: determinism as a public API
promise (stable iteration order, explicit seeds, explicit resource limits, no
hash-map iteration order in output) → item 3. Lifetime-free `Copy` term
handles, no FFI leakage, no global mutable state → item 4. Incremental lowering
+ warm solver → items 1 and 4. Pure-Rust, no C/C++ in the default build →
trivially parallel and embeddable, item 2. `unknown` as a first-class result,
never an error → an agent can act on `unknown`; an exception kills the loop.
**These were not chosen for agents and they are exactly what agents need.** The
work is to *expose* them: structured, machine-readable, localized failure
output is the gap, not the underlying design.

**5. Proof certificates are the differentiated bet, and they get more valuable
as agents get better, not less.** §4 is the argument: autoformalization is
97% claimed → 66% human-verified → **34.8% end-to-end**
([arXiv:2511.03108](https://arxiv.org/html/2511.03108v1)), and the field's own
remedy (BEq+) is *bidirectional proof search* — i.e. checking claims by proving
them. As agents generate more formal artifacts of unverified provenance, the
value of independent, cheap, self-checking evidence rises monotonically.
axeyum's identity — **"untrusted fast search, trusted small checking"** — is
precisely the shape of that need. The DRAT checker (ADR-0011) and
proof-producing CDCL (ADR-0012) are the seed; the Lean-kernel port is the
bridge from "SAT evidence" to "evidence a proof assistant accepts."

**6. Deprioritize premise selection.** It is within ~6 points of its oracle
ceiling (37.3% achieved vs 43.0% with ground-truth premises,
[arXiv:2506.07477](https://arxiv.org/html/2506.07477v1)) and agents rate premise
tools "marginal" ([arXiv:2602.24273](https://arxiv.org/html/2602.24273v1)).
Expose a search API because it is cheap and item 5 on the list; do not make it
a track.

**7. Benchmark against the honest targets.** miniF2F (>50% mis-formalized, 16
unprovable, saturated at 98–99%) and PutnamBench (99.4%) are dead as research
drivers ([arXiv:2511.03108](https://arxiv.org/html/2511.03108v1),
[logicalintelligence.com](https://logicalintelligence.com/blog/aleph-solves-putnambench)).
If axeyum measures itself on competition math it will measure noise. The live
targets are **miniCTX** (~33%, unfamiliar context,
[cmu-l3.github.io/minictx](https://cmu-l3.github.io/minictx/)), **SMT-LIB
reconstruction rate** (the 71%→98% gap), and **auto-active verification
workloads** (Dafny/Verus/DafnyBench), where the bottleneck is "auxiliary lemmas
and annotations" ([arXiv:2512.10187](https://arxiv.org/html/2512.10187)) and
where axeyum's existing Track 1 Z3 head-to-head methodology already applies.

**8. The thing that would falsify all of this.** If Lean's kernel gets fast,
gets native array support, and Lean-native automation (`grind`, lean-auto+Duper)
closes the SMT gap, then the §6a and §7.2 openings close and the counter-thesis
extends to cover axeyum's fragment too. `grind` at 32.4% vs Dafny's SMT at 38.9%
is a *6.5-point* gap, not a chasm, and it is Lean's to close. **This should be
monitored as an explicit kill criterion for the prover track**, reviewed against
Lean releases — not assumed away. The honest position is that axeyum's opening
is real, measured, and *contingent*.

---

### Summary of the load-bearing numbers

| Claim | Number | Source |
|---|---|---|
| General agent beats fine-tuned provers | miniF2F 98.0% pass@1, PutnamBench 54.7% pass@1 | [arXiv:2602.24273](https://arxiv.org/html/2602.24273v1) |
| Orchestrator saturates PutnamBench | 668/672 (99.4%), ~15 statements corrected | [logicalintelligence.com](https://logicalintelligence.com/blog/aleph-solves-putnambench) |
| Iterative refinement > tools | refinement = largest gain; tools "marginal" | [arXiv:2602.24273](https://arxiv.org/html/2602.24273v1) |
| miniF2F is broken | >50% mismatched; 16 unprovable; 300+ corrected | [arXiv:2511.03108](https://arxiv.org/html/2511.03108v1) |
| Autoformalization cascade | 97% → 66% human → 34.8% end-to-end | [arXiv:2511.03108](https://arxiv.org/html/2511.03108v1) |
| Library scale is not decisive | Dafny 38.9% (1.2k lines) vs Lean grind 32.4% (2M lines) | [arXiv:2512.10187](https://arxiv.org/html/2512.10187) |
| Premise selection near ceiling | 37.3% achieved vs 43.0% oracle | [arXiv:2506.07477](https://arxiv.org/html/2506.07477v1) |
| Hammer residual is solver strength | 21.7% untranslatable + 43.6% translated-unproven | [arXiv:2506.07477](https://arxiv.org/html/2506.07477v1) |
| Reconstruction gap | lean-smt 71% vs Ethos 98%; Lean kernel slow, no array support | [arXiv:2505.15796](https://arxiv.org/html/2505.15796v1) |
| Tooling > ecosystem | Opus 4.6 + Rocq-MCP: "choice matters less than LLM-tooling integration" | [arXiv:2603.20405](https://arxiv.org/pdf/2603.20405) |
