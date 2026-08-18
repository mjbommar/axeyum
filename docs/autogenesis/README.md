# Axeyum Autogenesis

## Purpose

This programme turns Axeyum from a collection of increasingly capable,
evidence-aware reasoning components into a system whose **verified reasoning
capability compounds automatically**.

The target is not merely a better solver, a larger theorem library, or an agent
that emits plausible proofs. It is:

> **A self-extending verified reasoning system: untrusted search may propose
> goals, decompositions, representations, tactics, algorithms, and even changes
> to its own search policy; only independently checkable evidence becomes
> durable knowledge.**

The trusted core stays small and stable while the untrusted intelligence around
it becomes broader, more adaptive, and more ambitious.

## Authority and scope

This directory is a durable long-horizon programme, not a second live task
tracker. Root [`PLAN.md`](../../PLAN.md) remains the sole authority for current
status and the next authorized increment. Each implementation phase in this
programme must enter the live queue through an owned file in
[`docs/plan/status/`](../plan/status/README.md), and consequential public or
trust-boundary decisions still require an ADR.

The existing [research roadmap](../research/08-planning/roadmap.md),
[foundational DAG](../research/08-planning/foundational-dag.md), and hard rules
remain in force. Autogenesis changes the criterion by which work is selected;
it does not waive foundation gates or authorize speculative implementation.

## Redefined goal

Axeyum succeeds when it can repeatedly perform this cycle:

```text
domain and checked knowledge
          |
          v
select or formulate a valuable claim
          |
          v
propose proof plans and representations       untrusted
          |
          v
search across solver / CAS / rewriting / library / induction
          |
          v
produce explicit evidence and a kernel term
          |
          v
independently replay, check, and admit         trusted boundary
          |
          v
record dependencies, assumptions, and provenance
          |
          v
measure what this result unlocked
          |
          +------> improve selection and search, then repeat
```

The unit of progress is a **verified capability gain**: a result that makes a
new useful class of problems reachable, cheaper, more assured, or more
automatic. A theorem counts when it unlocks descendants or teaches a reusable
method; a certified procedure may count more than a hundred isolated theorems.

The programme's primary objective is:

```text
verified capability gain
------------------------
human intervention * compute * trusted-base growth
```

No single scalar can carry the assurance claim. The operational dashboard must
also show the full conversion funnel from eligible goal to independently
replayed ledger transition.

## Programme outcome

The first decisive result is **Autogenesis-1**:

> From a fixed kernel, initial library, fact DAG, configuration, and resource
> budget, Axeyum autonomously selects and proves a reusable fact, admits it with
> checked evidence, observes that it unlocks another fact, then selects and
> proves that descendant. A clean-room replay reproduces the two-step acquisition
> sequence with no human-written or repaired proof and no unaccounted assumption.

This is deliberately stronger than “one automatic theorem.” It demonstrates
compounding, not automation theatre.

## Programme map

| Document | Question answered |
|---|---|
| [Current state and gaps](00-current-state-and-gaps.md) | What exists now, and what is genuinely absent? |
| [Target architecture](01-target-architecture.md) | What objects, boundaries, and feedback loops must exist? |
| [Phased roadmap](02-phased-roadmap.md) | What phases and concrete tasks get from here to the horizon? |
| [Workstreams and sequencing](03-workstreams-and-sequencing.md) | How do bottom-up and top-down work compose without starving each other? |
| [Metrics and evaluation](04-metrics-and-evaluation.md) | How is real capability gain distinguished from activity and self-report? |
| [Trust, safety, and governance](05-trust-safety-and-governance.md) | What remains immutable as autonomy increases? |
| [Research horizon](06-research-horizon.md) | What do current external systems teach, and what lies beyond them? |
| [First 90 days](07-first-90-days.md) | What is the first bounded execution programme? |
| [Backward foundation](08-backward-foundation.md) | What must be true immediately before Autogenesis-1, and which assumptions already fail? |
| [Authoritative B result](09-authoritative-b-admission-result.md) | Did a real B admission durably unlock A, and what remains uncredited? |
| [Autogenesis-1 result](10-autogenesis-1-result.md) | Did two clean authoritative B-then-A runs satisfy the fixed-budget, assurance, and reproducibility gates? |
| [Nursery foundation result](11-nursery-foundation-result.md) | Can the next evaluation population be split without dependency, family, proof-shape, mutation, or longitudinal leakage? |

The first executable counterfactual primitive is
[`create-autogenesis-snapshot.py`](../../scripts/create-autogenesis-snapshot.py).
It derives a content-addressed B -> A overlay without editing committed facts;
[`theorem_knowledge_audit`](../../crates/axeyum-lean-kernel/examples/theorem_knowledge_audit.rs)
then rejects required/forbidden dependency violations over the full transitive
kernel closure.
[`create-autogenesis-proposer-catalog.py`](../../scripts/create-autogenesis-proposer-catalog.py)
projects that snapshot to names and canonical types only, and the Python
proposer runner supplies the verified catalog through an OS sandbox with no
checkout, retained proof bodies, inherited environment, or network.
[`check-autogenesis-apply-search.sh`](../../scripts/check-autogenesis-apply-search.sh)
then composes two catalog-only searches: a target-independent structural-plan
grammar produces fresh B, and the identical A target receives no proof before B
but a fresh, B-dependent proof afterward under the same budget. The chain is
now bound to an internal typed B evidence handoff and a replay-derived,
zero-ledger-write episode transition. A checked accepted-transition event is
now required to construct the post-B catalog, so the snapshot alone cannot
unlock A. The exact-commit retained bundle at `42dad8ffa` also reproduces
through the separate read-only replay command.
The next boundary now has a typed, read-only fact-transaction proposal: its
positive test is explicitly counterfactual, while mismatched evidence for a
real open fact rejects. No authoritative ledger write is claimed; its durable
admission event is fixture-scoped.
ADR-0468's applicant now commits that proposal only in a temporary fact root,
with compare-and-swap and roll-forward recovery tested at all three durable
boundaries. Production write authority rejects this fixture path.
The durable fixture event now derives a content-addressed readiness delta, and
that delta is mandatory input to the post-B catalog. It authorizes exactly A
from the ledger's B-to-A edge. The authoritative fact frontier now has a
content-addressed JSON form with deterministic rationale. At exact pushed
checkpoint `5c38bf95d`, it selects exactly
`F:no-integer-square-is-minus-one`: the only open fact matching an
authoritative typed operation. Every unregistered candidate remains refused,
so broad fragment reachability cannot silently become dispatch authority.

The reviewed [`operations.json`](../../artifacts/autogenesis/operations.json)
names both the fixture-only Nat producer/checker and the first authoritative
QF_NIA certificate operation. The latter is source-bound, narrow, and carries
a non-empty SMT trust footprint rather than impersonating a kernel theorem.
Selection, typed execution, admission, and recovery are therefore real. The
executor binds a clean commit, frontier, registry, fact, source bytes, budget,
and independently rechecked result; the transaction adapter derives the
complete fact delta and replay checker without caller-authored metadata. The
first production compare-and-swap intentionally stopped after durable intent,
left the fact unchanged, then recovered to a durable event. Its event-triggered
frontier delta honestly records `newly_ready: []`.

At exact pushed commit `f8651ec98`, a second isolated clean worktree reconstructed
the historical open row and freshly repeated selection, certified execution,
transaction preparation, the same intent fault, recovery, settled-fact replay,
and readiness derivation. The complete external bundle at
`/nas3/data/axeyum/autogenesis/replays/f8651ec98/` has replay digest
`7dc1ad8dc336ac0ea295a3a0b912f89f415787c0b78c61c54624a791f1800e4b`.
This closes clean authoritative **leaf** reproduction. The selected fact unlocks
no descendant, so it still receives no Autogenesis-1 compounding credit.

Chain authority is now narrower and stronger. The kernel subgraph contains 52
authored `depends_on` edges, but only 23 are confirmed as direct dependencies by
the checked proof terms; the content-addressed catalog refuses to equate those
sets. The existing `F:nat-zero-add -> F:nat-mul-one` two-search experiment
replayed at exact commit `a90255a92` and qualifies the primary chain: same A
target, pre-B budget exhausted with no proof, B produced axiom-free, durable
fixture event, then A proved using the episode-local B. Qualified catalog
`95e8c8d401441b98793259d79f95cda485493b81c996c08f0d1df998285c925b`
selects it for engineering while explicitly granting no authoritative-write
authority. The next bridge is therefore operation authority for B and A, not
more chain prose.

B's first production-capable route is deliberately exact rather than
generic: `authoritative-kernel-nat-zero-add-induction-v1` reconstructs the
selected statement in a fresh kernel, accepts plan 2 of 2, and requires both an
empty axiom footprint and no retained-answer dependencies. The retained
[authoritative B admission](09-authoritative-b-admission-result.md) then
crash-recovered one real write and derived A as newly ready. The live ledger was
untouched. A's exact episode-local apply operation is now implemented: it
verifies B's execution-to-readiness trigger chain, reconstructs
an episode-local B candidate, and applies only that candidate. It also creates a
deterministic detached post-B state commit without touching the branch or index.

**Autogenesis-1 passed at exact source commit `cf998788b`.** Two isolated runs
used the same fixed budgets (`B=2`, pre-B `A=1`, post-B `A=1`). Before B, A
exhausted that budget without a proof. The authoritative frontier then selected,
proved, crash-recovered, and recorded B; B's durable event made exactly A newly
ready; and the frontier selected, proved through the episode-local B,
crash-recovered, and recorded A. Both kernel footprints and retained-answer
dependency lists were empty. The two runs had identical semantic identities and
all 56 retained artifact bytes matched. The small committed
[result index](../../artifacts/autogenesis/autogenesis-1-result.json) binds the
external receipts; the detailed audit is in the
[Autogenesis-1 result](10-autogenesis-1-result.md).

The first post-result increment is a deliberately red nursery baseline. ADR-0478
reserves the successful chain as a longitudinal regression, separates authored
split dependencies from proof-derived admission authority, and prohibits
dependency components, theorem families, proof shapes, or mutations from
crossing evaluation partitions. The executable
[`nursery-v1.json`](../../artifacts/autogenesis/nursery-v1.json) currently has
zero evaluation facts and nine named readiness blockers. That finding is the
point: the existing ledger cannot be relabelled into a credible held-out Phase 3
population. See the [nursery foundation result](11-nursery-foundation-result.md).

## Phase summary

| Phase | Future state | Decisive exit |
|---|---|---|
| 0. Bind reality | Current claims and interfaces are machine-readable and non-contradictory | One generated baseline names every existing seam and refuses stale plan/fact state |
| 1. Close one loop | A deterministic orchestrator performs one evidence-backed fact transition | Clean replay of one autonomous closure; no learning or conjecturing |
| 2. Demonstrate compounding | A counterfactual knowledge snapshot and scheduler produce a two-fact unlock chain; a dense nursery follows for sustained evaluation | Autogenesis-1 passes from a clean checkout |
| 3. Plan proofs | A typed proof-plan IR composes heterogeneous checked substeps | One goal solved by a multi-route plan that no monolithic route can solve |
| 4. Acquire capabilities | Structured declines drive reusable lemma, route, and representation work | Measured capability acquisition raises held-out autonomous yield |
| 5. Learn search, not truth | Search policy improves from replayable reasoning episodes | Learned policy beats deterministic baselines without changing acceptance |
| 6. Discover | The system proposes and filters useful new conjectures and algorithms | Novel candidates survive independent proof/refutation and novelty review |
| 7. Become domain-general | Domain adapters produce typed, epistemically classified knowledge | Two non-mathematical domains complete the same checked loop |
| 8. Govern recursive improvement | The system proposes bounded improvements to its own untrusted machinery | Improvements pass immutable evaluation, regression, and trust-budget gates |

Phases are capability gates, not dates. Work may begin on a later phase's
research or fixtures early, but no later phase may receive product credit before
its prerequisites pass.

## Strategic rules

1. **Composition before breadth.** Prefer closing an existing seam over adding
   another isolated capability.
2. **Demand pulls mechanisms.** Solver and reconstruction work should normally
   be selected by structured declines from valuable, dependency-ready goals.
3. **Learning proposes; formal machinery disposes.** Learned systems never
   decide truth, evidence validity, axiom freedom, or publication.
4. **Failures are products.** A typed decline with a minimal blocker and replay
   is valuable training and planning data; a timeout string is not.
5. **The ledger records knowledge, episodes record attempts.** Do not overload
   the fact schema with search traces or treat every attempted conjecture as a
   fact.
6. **Novelty is a separate judgment.** Kernel acceptance establishes formal
   consequence, not importance, originality, correct formalization, or truth of
   empirical premises.
7. **Scale follows demonstrated pull.** Sharding, caching, distributed search,
   and learned policies are justified by observed bottlenecks in the closed
   loop, not projected theorem counts.
8. **Over-the-horizon pressure is explicit.** Every phase must preserve typed
   binders, extensible evidence, deterministic replay, domain separation, and a
   path to richer proof calculi.

## Relationship to existing programmes

Autogenesis does not replace the A1-A11 solver programme or the existing proof,
Lean, CAS, verified-systems, and frontend tracks. It supplies their selection
function:

```text
autonomous attempt
      |
      v
structured blocker --+--> solver/theory task
                     +--> reconstruction/checker task
                     +--> library lemma task
                     +--> representation task
                     +--> resource/observability task
                     +--> domain/formalization task
      |
      v
repair the smallest reusable blocker
      |
      v
retry the original attempt and measure unlocked descendants
```

The complete-solver and Lean horizons remain valuable. They become capability
reservoirs serving a measurable knowledge-growth loop rather than independent
feature-count races.

## Definition of done

The programme is not complete because a model generates a proof, because a
solver returns `unsat`, because Lean reads a generated module, or because a
dashboard reports growth. It is complete only when Axeyum can sustain bounded,
reproducible capability acquisition across domains while:

- every durable formal result is independently checkable;
- every assumption and trust step is explicit;
- every policy improvement is evaluated against immutable held-out populations;
- regressions and failed experiments remain visible;
- the trusted base grows only through deliberate, reviewed decisions; and
- human intervention per verified capability gain declines over time.
