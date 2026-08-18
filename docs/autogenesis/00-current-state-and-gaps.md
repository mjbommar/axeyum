# Current state and gaps

## Snapshot boundary

This assessment was refreshed through exact pushed feature checkpoint
`5ac434ef9` on 2026-08-18. It uses live code, root `PLAN.md`, generated reports,
and recent Git history rather than treating older roadmap prose as current.
Numerical claims are snapshot claims and must be regenerated before an
implementation phase relies on them.

Useful live commands are:

```sh
just flywheel
just next
python3 scripts/check-fact-dag.py
python3 scripts/gen-proof-gap-matrix.py --check
python3 scripts/gen-plan.py --check
```

## What already exists

Axeyum is not starting from an agent mock-up. Most data-plane components of the
cycle already exist:

| Layer | Current asset | Current assurance |
|---|---|---|
| Formal problem | Typed term IR, queries, SMT-LIB parser, fact `formal.statement` | Typed and validated; surface support remains uneven |
| Selection | `fact-frontier.py`, dependency readiness, unlock view, gate-coupling warning | Human and content-addressed JSON views; exact authoritative operation matching selects one live fact and refuses every unregistered candidate |
| Search | Pure-Rust SAT/BV, arithmetic, quantifier, string, FP, CAS, and specialized routes | Broad, uneven; `unknown` is first-class |
| Strategy | Solver strategy combinators and route dispatch | Route-local; not a general proof planner |
| SAT checking | Original-model replay and multiple clausal proof routes | Strong for supported routes |
| Theory evidence | Alethe, Farkas, CAS and specialized certificates | Route-dependent; gaps remain explicit |
| Kernel | Independent Rust Lean-core checker and theorem reconstruction | Substantial selected profile; not full Lean |
| Dependencies | `Kernel::theorem_dependencies` derives proof-term dependencies | Landed and mutation-guarded |
| Knowledge ledger | One JSON object per proposition, status, evidence, footprint, dependencies | Schema-validated and checker-aware |
| Closure | `close-fact.py` executes checker commands before changing status | Fail-closed, but caller assembles evidence manually |
| Observability | `just flywheel`, proof-gap matrix, capability/support/trust matrices | Rich but distributed across several artifacts |

The current live flywheel snapshot reports 110 facts: 95 proved, 3 refuted, 2
computed, 7 open, and 3 conjectured. Only 33 facts declare dependencies, only 30
have dependents, 63 are isolated, and maximum depth is 6. The broad retained
proof-gap population reports 259 of 327 baseline UNSAT instances satisfying all
recorded dominance conditions. These are bounded populations, not universal
soundness or general solving-power claims.

## What recent history establishes

Recent work demonstrates several properties that Autogenesis can build on:

- incorrect induction dispatch can be found by adversarial front-door tests;
- producer-claimed certification can be rejected by independent fresh-arena
  checking;
- proof dependencies can be derived rather than transcribed;
- checker coverage and mutation survival matter more than exit code;
- Lean reasoning can be distinguished from structural attestation;
- unsupported or resource-exhausted paths can decline without a wrong verdict;
- architectural refactors can be rejected by measured dependency effects; and
- a fact status transition can be made conditional on executing its evidence.

The history also shows why autonomy cannot be placed directly on top of current
scripts: multiple same-day claims were true only in a weaker sense than their
headline implied. The loop needs typed intermediate contracts, not a shell
pipeline that assumes each preceding tool meant what the next tool needs.

## The missing control plane

The following objects do not yet exist as first-class, versioned contracts:

### Reasoning episode

There is no single artifact joining:

- selected goal and exact input identity;
- visible library and dependency snapshot;
- proposed plans and selection rationale;
- budgets, seeds, and tool versions;
- route attempts and intermediate obligations;
- structured decline causes;
- evidence and reconstruction outputs;
- checker and kernel observations;
- proposed ledger delta; and
- descendants unlocked by admission.

The information exists piecemeal in logs, result notes, solver structures, and
Git history. That makes it unsuitable for deterministic replay, systematic
learning, or causal evaluation.

### General proof-plan IR

Axeyum has route strategies, evidence proof steps, solver traces, and kernel
terms, but no typed orchestration language for operations such as:

- introduce a variable or assumption;
- split a conjunction, case, or induction;
- retrieve and apply a theorem;
- instantiate a quantified fact;
- rewrite under a checked equality;
- normalize into a supported fragment;
- dispatch an obligation to a solver or CAS;
- reconstruct a checked subproof; and
- compose all subproofs into one kernel term.

Without this layer, complex reasoning remains either monolithic solver dispatch
or handwritten kernel-term construction. One narrow registered QF_NIA operation
now exercises the typed authoritative path end to end; it is a route instance,
not yet the general orchestration language described above.

### Autonomous closure transaction

`close-fact.py` is intentionally the last manual link. It executes supplied
checker commands, but it does not itself:

- dispatch the fact;
- construct evidence rows from typed solver results;
- ensure result/fact identity across reparsing;
- derive the proof route and footprint;
- stage the transition as a portable proposal;
- retry dependents; or
- prove that a clean environment reproduces a multi-fact acquisition.

### Capability-learning substrate

No persistent corpus records both successful and failed attempts in a form
suitable for route selection, premise retrieval, decomposition learning, or
budget allocation. Git commits are not a training dataset, and benchmark rows
do not capture the reasoning state that preceded a result.

## Top-down gap: vision to product state

| Desired future state | Current state | Missing bridge |
|---|---|---|
| One autonomous verified theorem | Autogenesis-1 selected, proved, admitted, recovered, and byte-identically reproduced two linked facts | Generalize beyond exact registered bootstrap operations |
| Compounding theorem sequence | One exact Nat chain passed; the ledger still has few useful open dependency chains | Dense held-out nursery and generic scheduler/retry policy |
| Heterogeneous proof planning | Route-specific dispatch and reconstruction | Typed proof-plan IR and obligation semantics |
| Experience-driven improvement | Logs and Git history | Replayable episode corpus and immutable evaluation splits |
| Useful conjecture generation | Mostly authored fact set | Typed candidate lifecycle, falsification, utility and novelty filters |
| Domain-general knowledge growth | Several consumers, no shared acquisition loop | Domain adapter contract and epistemic type system |
| Safe recursive improvement | Humans change code and gates | Sandboxed proposal/evaluation protocol with immutable acceptance |

## Bottom-up gap: present components to the next seam

| Existing component | Immediate engineering gap | Why it blocks the loop |
|---|---|---|
| `fact-frontier.py` | General multi-step orchestration beyond the bootstrap chain | Autogenesis-1 retained two byte-identical B-then-A authoritative runs; dispatch remains exact to this preregistered chain |
| Fact schema | Candidate/attempt identity is absent by design | Attempts and knowledge need separate schemas |
| Solver `Evidence` | No route-neutral portable result envelope for closure | The closer cannot derive ledger evidence safely |
| Reconstruction | No generic obligation-composition interface | Multi-step plans cannot become one kernel proof |
| Kernel dependency inventory | Mapping from kernel constants back to fact IDs is partial | Newly admitted facts cannot always derive ledger edges |
| `close-fact.py` | Shell commands in caller-authored rows | Command text is too weak as a typed trust boundary |
| Fact DAG | 63/110 isolated overall; 52 authored internal kernel-subgraph edges narrow to 23 direct proof-derived edges across 10 consequents | One primary is operationally qualified; 14 named kernel facts remain outside dependency-inventory coverage and no fallback is measured |
| Capability matrices | Primarily capability reporting | Declines are not converted into ranked reusable work |
| Benchmark corpora | Measure solver verdicts | Do not measure autonomous acquisition or human intervention |
| Plan generation | Syntactic consistency only | Semantically stale next actions can still pass |

## Gaps by future phase

### Phase 0: bind reality

Gap: existing state is authoritative only when a human reconciles several
reports. Some generated plan statements can be semantically stale while the
generation check passes. Required bridge: one checked Autogenesis baseline with
exact input identities and cross-artifact invariants.

### Phase 1: close one loop

Gap: each step exists, but composition is manual and evidence input is
caller-authored. Required bridge: a deterministic, typed orchestration command
that emits a proposal and a separate replay command that authorizes closure.

### Phase 2: demonstrate compounding

Gap: the kernel subgraph is connected enough for a bootstrap replay, but every
kernel fact is already settled. Required bridge: a counterfactual knowledge
snapshot that withholds ledger entries *and proof retrieval*, followed by a
dense, non-trivial nursery for sustained evaluation with known dependencies,
mutations, route expectations, budgets, and held-out chains.

### Phase 3: plan proofs

Gap: solver strategies do not express proof decomposition across engines.
Required bridge: proof-plan semantics whose steps create typed obligations and
whose execution can be reconstructed into the kernel.

### Phase 4: acquire capabilities

Gap: failure causes are mostly prose or backend-specific enums. Required bridge:
a cross-route decline taxonomy plus a planner that ranks the smallest reusable
capability acquisition by expected unlocked value.

### Phase 5: learn search, not truth

Gap: there is no stable state/action/outcome dataset and no contamination-safe
evaluation. Required bridge: episode extraction, frozen splits, deterministic
baselines, and a policy interface outside the trusted path.

### Phase 6: discover

Gap: the ledger assumes a proposition worth recording is already known.
Required bridge: candidate conjecture lifecycle, type/formalization checks,
cheap refutation, deduplication, utility estimates, and external novelty review.

### Phase 7: become domain-general

Gap: consumers invoke reasoning but do not all produce the same durable
knowledge objects. Required bridge: domain adapters separating formal truth,
bounded computation, empirical evidence, policy assumptions, and provenance.

### Phase 8: govern recursive improvement

Gap: the system cannot safely distinguish an improvement to search from a
change that weakens evaluation or acceptance. Required bridge: immutable
evaluators, privilege separation, trust budgets, held-out regressions, and human
authorization for trusted-surface changes.

## Strategic conclusion

The next bottleneck is not raw solver breadth. It is the absence of a typed,
replayable control plane connecting already-real components. The programme must
therefore begin by composing and measuring the current system, then allow
failures from that composition to pull bottom-up capability work.
