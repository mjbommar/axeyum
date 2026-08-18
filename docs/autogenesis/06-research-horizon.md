# Research horizon

## Scope and method

This note relates the Autogenesis programme to current primary research and
official proof-system documentation available on 2026-08-18. It extracts
mechanisms and limitations; benchmark numbers across different systems and
populations are not treated as directly comparable.

Axeyum should learn aggressively from these systems without copying their
authority model. Its distinctive opportunity is the combination of
heterogeneous search, independently checked evidence, explicit trust accounting,
a native kernel/library, and a dependency-aware knowledge ledger.

## Current frontier patterns

### Verified environments make large-scale search useful

[AlphaProof](https://www.nature.com/articles/s41586-025-09833-y) models Lean
proof construction as reinforcement learning inside a formally verified
environment. It combines human proof data, large-scale auto-formalized problem
generation, search, and problem-specific test-time training. The lesson for
Axeyum is not “train a giant model first.” It is that a strict verifier makes
otherwise risky exploration usable as learning signal.

Autogenesis implication:

- build the episode and acceptance environment before learned search;
- retain verifier observations at every intermediate plan state; and
- keep auto-formalization outside the truth boundary.

### Decomposition is a central intelligence primitive

[DeepSeek-Prover-V2](https://arxiv.org/abs/2504.21801) uses recursive subgoal
decomposition to construct training data and improve Lean proof generation.
[LeanTree](https://arxiv.org/abs/2507.14722) similarly argues for white-box,
factorized proof states that support parallel search, reuse, and richer feedback.

Autogenesis implication:

- the proof-plan IR and explicit obligation graph are higher leverage than a
  larger monolithic `solve` call;
- plan state should be serializable and independently inspectable; and
- the scheduler should learn over subgoals and representations, not only whole
  theorem outcomes.

### Premise retrieval is part of proving, not a convenience feature

[LeanDojo/ReProver](https://arxiv.org/abs/2306.15626) records proof states,
tactics, and fully identified premises, then uses retrieval to select relevant
library facts. Its novel-premise split also shows why random train/test splits
can overstate generalization.

Autogenesis implication:

- kernel-derived dependencies and fact/concept links should become retrieval
  features;
- exact theorem identity and scope must survive retrieval;
- dependency-component and novel-premise held-out splits are mandatory; and
- retrieval failure should be a structured decline distinct from inability to
  prove with the correct premises.

### Self-play can create a curriculum, but generated volume is dangerous

[STP](https://arxiv.org/abs/2502.00212) couples conjecturing and proving so the
conjecturer targets statements near the prover's changing frontier. This is a
plausible way around sparse successful-proof data.

Autogenesis implication:

- conjecturer/prover co-evolution belongs after the authored closure loop;
- generated candidates need typing, falsification, deduplication, utility, and
  novelty gates;
- all generated denominators and compute must be retained; and
- curriculum difficulty should be measured by verified outcomes rather than a
  model's self-score.

### Lifelong learning requires stability, not merely new successes

[LeanAgent](https://arxiv.org/abs/2410.06209) frames theorem proving across
evolving repositories as lifelong learning and measures stability and backward
transfer rather than only performance on the newest domain.

Autogenesis implication:

- longitudinal replay sets must start before learned policies;
- every policy update must re-evaluate earlier domains;
- the knowledge base and the search policy need independent versioning; and
- forgetting is a reported outcome, not hidden by aggregate growth.

### Evolutionary discovery works when evaluators are strong

[AlphaEvolve](https://arxiv.org/abs/2506.13131) combines LLM-generated program
changes, an evolutionary archive, and automated evaluators to discover and
optimize algorithms. Its applicability depends on executable objective
functions and evaluator quality.

Autogenesis implication:

- algorithm and self-improvement search belongs behind immutable correctness,
  assurance, and resource evaluators;
- parentage, mutations, rejects, and selection policy are evidence;
- performance improvements must not weaken semantic correctness; and
- evaluator modification must be outside the proposing agent's authority.

### Proof formats must expose incompleteness honestly

cvc5's official
[Cooperating Proof Calculus documentation](https://cvc5.github.io/docs/cvc5-1.3.1/proofs/output_cpc.html)
describes CPC proofs checked by Ethos/Eunoia and distinguishes a fully specified
proof from one containing trust steps.

Autogenesis implication:

- evidence bundles must preserve trust steps and assurance classes;
- “proof produced” is not one binary state;
- checker outcomes need typed completeness status; and
- learning must not optimize by replacing expensive checked reasoning with
  cheaper trust steps.

## Where Axeyum is behind

Compared with current formal theorem-proving agents, Axeyum lacks:

- a large, clean state-action-outcome episode corpus;
- a programmatic white-box proof environment above individual solver routes;
- learned premise retrieval and proof-state policy;
- recursive subgoal-decomposition training;
- large-scale self-play conjecture curricula;
- model/tool evaluation infrastructure; and
- published autonomous theorem-proving benchmarks.

These are substantial gaps. The current pure-Rust kernel and solver breadth do
not compensate for them automatically.

## Where Axeyum can be different

Most current learned provers operate inside one proof assistant and optimize
proof success. Axeyum can pursue a broader verified-reasoning environment:

- SMT, SAT, CAS, rewriting, induction, enumeration, and library proof in one
  typed plan;
- route-specific evidence checked independently of the proposer;
- explicit models, counterexamples, unknowns, and operational failures;
- knowledge dependencies and assurance stored as first-class data;
- capability investment selected by downstream unlock value;
- multiple epistemic classes beyond pure theoremhood; and
- eventual application to programs, protocols, policies, and empirical models.

The differentiator is not that Axeyum will have an LLM. It is that every learned
or generated proposal enters an evidence-aware, heterogeneous, replayable
knowledge-growth system.

## Over-the-horizon research questions

### Representation acquisition

Can the system learn that a goal becomes tractable after changing coordinates,
introducing an invariant, choosing a quotient, inventing an auxiliary function,
or moving between algebraic and combinatorial views? This is likely more
important than tactic prediction for genuinely difficult reasoning.

Near-term preservation requirement: proof plans must name transformations and
their semantic justification, not store only final tactic text.

### Definition and abstraction synthesis

Theorem accumulation eventually plateaus if the vocabulary is fixed. A mature
system must propose definitions that compress proof plans and expose reusable
structure.

Near-term preservation requirement: keep definitions, propositions, procedures,
and evidence distinct, and derive dependency effects for all of them.

### Meta-reasoning about proof economics

The system should reason about whether to prove a lemma, enumerate a finite
domain, strengthen a solver, change a representation, or accept a bounded
answer. That is planning under cost and assurance constraints, not ordinary
theorem search.

Near-term preservation requirement: episodes must record costs and alternate
attempts, including failures.

### Cross-kernel and cross-system disagreement

Multiple independent kernels and checkers can turn disagreement into a localized
research object rather than a binary release failure.

Near-term preservation requirement: artifact identity and semantics must not be
tied to one kernel's in-memory representation.

### Scientific knowledge revision

Mathematical knowledge is monotone under fixed axioms; empirical knowledge is
not. Domain-general Autogenesis will need versioned observations, model
comparison, defeasible conclusions, and retraction without corrupting formal
dependencies.

Near-term preservation requirement: do not force empirical claims into theorem
status or assume the final knowledge graph is monotone.

### Cooperative verified agents

Specialized planners could exchange conjectures, subgoals, counterexamples, and
proof artifacts. Communication should be proof-carrying where possible and
epistemically typed elsewhere.

Near-term preservation requirement: content-addressed episodes and plans must be
self-contained enough for independent workers and clean replay.

### Mechanized planner metatheory

Some proof-plan typing, substitution, composition, and context rules may
eventually be formalized within the kernel or another proof assistant. Full
verification of learned search is neither necessary nor plausible; verification
of the plan semantics may be.

Near-term preservation requirement: keep the plan language small, versioned,
and semantically explicit.

## Research watchlist

Refresh this note before Phases 3, 5, and 6. Watch at least:

- formal proof agents with public code, data, and verifier interaction traces;
- subgoal decomposition and white-box proof-state search;
- premise retrieval under novel-premise or repository-transfer splits;
- self-play conjecturing and curriculum generation;
- proof-producing SMT and independent proof checkers;
- evaluator-guided algorithm discovery and reward-hacking defenses;
- cross-system autoformalization evaluation; and
- formal methods for agent plans and tool-use traces.

Do not copy leaderboard percentages into Axeyum planning without matching
population, budget, verifier, sampling, and contamination conditions.
