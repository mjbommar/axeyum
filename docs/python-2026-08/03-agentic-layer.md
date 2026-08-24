# 03 — The agentic layer: an autonomous, replayable frontier loop over the Python API

Status: plan, 2026-08-24. Measured basis:
[`studies/agentic-framework-comparison.md`](studies/agentic-framework-comparison.md).
Depends on plans 01 and 02. Nothing here has admission authority; that is the
whole design, and [`docs/autogenesis/05-trust-safety-and-governance.md`](../autogenesis/05-trust-safety-and-governance.md)
is the authority matrix this plan makes executable.

## What this plan delivers

An `[agent]` extra on the one Python package (`pydantic-ai-slim[anthropic]`,
`pydantic-graph`, exact-pinned) providing:

1. a **typed tool catalog** over `axeyum.*` in three tiers — R (read), P
   (propose), C (check) — where every C tool is a deferred tool that ends the
   run and waits for a trusted process;
2. an **episode artifact** (`artifacts/ontology/agent-episode.schema.json`),
   canonical JSON + SHA-256, with a stdlib-only checker
   `scripts/check-agent-episode.py` whose exit status depends on the finding;
3. the **frontier loop** as a `pydantic-graph` state machine: deterministic
   `Select` → *Gather* → *Plan* → deterministic `Gate` → `Dispatch` → `Check`
   → `StageTransaction` | *Classify* → `WriteEpisode`;
4. a **strategy vocabulary** the `Plan` node must resolve against — the
   tactic catalog extracted from the producers — so a plan names tactics, not
   prose, and every episode is a labelled datapoint for a named strategy.

## Why the architecture is already here

`autogenesis-induction-proposer.py` emits a hashed plan bundle;
`autogenesis_induction_plan_check` consumes it bound to `--bundle-sha256` and
`--expect proved|no-proof`, so its exit status depends on what it found. The
LLM **replaces the enumerator and nothing else changes**. Four structural
locks already exist: `EXECUTION_DRIVERS` is a closed allowlist,
`apply-autogenesis-fact-transaction.py` is the only ledger writer, the ledger
directory can be mounted read-only, and
`check-autogenesis-holdout-isolation.py` string-walks every artifact.

What plan 02 changes: the tools call `axeyum.kernel.Kernel.prelude("nat")`
and get typed objects. No stdout parsing, no pinned-format contract tests, and
typed `Decline` objects instead of prose — which is what makes the obstruction
graph (Autogenesis F3) derivable rather than hand-authored.

## Tool tiers

| tier | examples | pydantic-ai mechanism | may write |
|---|---|---|---|
| R | `frontier_select` (drops held-out rows **before** the model sees a list), `fact_get`, `fact_neighbourhood`, `kernel_theorems`, `operation_registry`, `overlay_query`, `concept_lookup`, `technique_lookup`, `cas_simplify`, `smt_solve` (bounded), `web_fetch` (snapshotted + hashed; guarded, below) | plain tools; hidden from nodes that do not need them via `FilteredToolset` | only the episode's `snapshots/` |
| P | `propose_strategy -> StrategyProposal`, `propose_lemma`, `propose_overlay_link` | `output_type`; every result carries `assurance="proposed"` enforced by a field validator | `episodes/<id>/proposals/` |
| C | `bounded_induction`, `plan_check`, `certificate.check()`, `outcome.replay()` | `requires_approval=True` → `DeferredToolRequests`; a supervisor resumes with `DeferredToolResults` | nothing; results are receipts |

`StrategyProposal` fields: `fact_id`, `tactic_ids` (must resolve in the tactic
catalog), `producer_id` (must resolve in `operations.json` or the catalog),
`why`, `expected_decline_class`, **`sibling_fact_ids: list[str] =
Field(min_length=3)`** or the explicit `NoGeneralRoute` variant. The last is
doc 228's "dispatch table, not producer" finding made a schema constraint.

## The episode artifact

Spine copied from the statement-adapter manifests and from
`execute-autogenesis-operation.py`'s receipt fields so an episode diffs against
a receipt:

```
schema_version, kind: "axeyum-agent-episode", episode_id, git_commit
selection:  frontier_sha256, frontier_path, fact_id, fact_sha256, partition, eligibility_reason
policy:     model_id (provider-prefixed), settings, prompt_hashes{}, toolset_sha256,
            agent_code_sha256, library_versions{}
budgets:    wall_seconds, request_limit, tool_calls_limit, token limits, cost_limit_usd
transcript: messages_sha256, messages_path, tool_calls[]{ordinal, tool, args_sha256,
            result_sha256, assurance, duration_ms, exit_status}
web_snapshots[]{url, fetched_at, sha256, bytes, path}
proposals[]{path, sha256, kind, assurance:"proposed"}
outcome:    verdict ∈ proved|declined|error|budget-exhausted, decline_class,
            checker_command, checker_exit_status, checker_output_sha256,
            axiom_footprint[], ledger_writes (MUST be 0), search_invocations,
            target_theorem_submissions
observed:   facts_unlocked[], operations_widened[], overlay_links_proposed[]
```

`check-agent-episode.py` fails when: `git_commit` is not an ancestor of HEAD;
`frontier_sha256` does not re-derive via `fact-frontier.py --verify`; any
snapshot digest mismatches; `ledger_writes != 0`; `partition == "held-out"` or
any held-out id appears anywhere; `verdict == "proved"` with nonzero checker
status; any proposal digest mismatches; `tool_calls` is empty. Registered in
`scripts/tests/mutation_controls.py`; each guard kills exactly one test.

**Replayable, not reproducible.** `replay --from-transcript` runs the graph
with `models.ALLOW_MODEL_REQUESTS = False` and a `FunctionModel` returning the
recorded responses; every deterministic node must re-derive bit-identically.
Divergence is a finding.

## Slices

### A1 — episode schema and fail-closed checker (no agent yet)
Schema, two hand fixtures (`proved`, `declined`), checker, mutation controls.
*This is built first because it is what makes everything after it safe.*

### A1 findings that A2 must honour (measured 2026-08-24)

1. **Frontier re-derivation does not survive a live ledger.** `fact-frontier.py
   --verify` recomputes from `artifacts/facts/`, so a committed per-episode
   frontier goes stale the moment any lane adds a fact. An episode therefore
   records `selection.ledger_sha256` (from the frontier's `ledger` block) and
   the checker compares the frontier file's self-digest; `--verify` is an
   explicit freshness mode, not the default gate.
2. **`selection.ready_fact_ids` is not the eligible set** — it includes
   held-out rows. `frontier_select` filters by **partition** before the model
   sees a list, and drops `longitudinal` (2 rows) explicitly, since the
   episode enum admits only `train | development`.
3. **Multiple checkers per episode.** Schema v1 has one `checker_command`;
   v2 adds `checker_runs[]{command, exit_status, output_sha256}`. A2 stays on
   v1 (it dispatches nothing); A4 introduces v2 beside it.
4. **`proved` requires a checked tool call.** Rule 11: `verdict == "proved"`
   only if some `tool_calls[].assurance == "checked"` — the C tier is the
   only route to it.
5. **`decline_class` becomes an enum** seeded from the AG4.1 taxonomy
   (`docs/autogenesis/02-phased-roadmap.md`) in A5.
6. Gates run the checker without `--require-ancestor` (CI clones are
   shallow); the ancestor rule is opt-in and warns by default.

### A2 — package extra, six R tools, four-node graph, ten episodes
`[project.optional-dependencies] agent = [...]`; tools `frontier_select`,
`fact_get`, `fact_neighbourhood`, `kernel_theorems`, `operation_registry`,
`overlay_query` over `axeyum.knowledge` / `axeyum.kernel`; graph `Select` →
*Gather* → *Plan* → `WriteEpisode`; dispatches nothing. Ten committed episodes
over the 104 open, dependency-ready, non-held-out facts (measured 2026-08-24;
`fact-frontier.py` itself currently returns
`refused-no-admissible-candidate`, the baseline this loop exists to move).
Exit: checker green on ten, red on ten corrupt fixtures; **at least one
episode honestly emits `NoGeneralRoute`**.

### A2 result (measured 2026-08-24, live)

Ten episodes on `anthropic:claude-sonnet-4-5` with
`UsageLimits(cost_limit=0.50, request_limit=8, tool_calls_limit=12)` over
ten distinct eligible facts (9 nursery families, 5 train / 5 development):
**$1.635 total, mean $0.163**; 8 `declined`, 2 `budget-exhausted`; 96 tool
calls, all tier R; all 12 documents pass `check-agent-episode.py`; every
episode replays with model requests disabled. **8 of 8 completed plans
emitted `NoGeneralRoute`; zero emitted a `StrategyProposal`.** Not forced:
with the three-sibling rule in force, the model never claimed a general
route over the nine-tactic catalog. That is the baseline A4 and A7 must
move, and it is the first agent output in this repository whose failure
mode is a typed value rather than an absent success.

Facts A4 inherits from A2:

- Sidecars are `*.json.snapshot`, because the checker walks a directory
  with `rglob("*.json")` and treats every match as an episode. Only episode
  documents carry a bare `.json` under `artifacts/episodes/`.
- The committed `frontier.json.snapshot` is a census of the whole open
  ledger and therefore contains held-out ids — the same category as
  `nursery-v1.json`, which the isolation gate exempts. The episode
  documents, transcripts and proposals carry zero held-out ids (grepped
  with a positive control). `check-autogenesis-holdout-isolation.py` does
  not scan `artifacts/episodes/`; extending it, with the census snapshot
  exempted by name, is A4 work.
- Schema v1 `selection` cannot carry `ledger_sha256`
  (`additionalProperties: false`); v2 adds it beside `checker_runs[]`.
- Anthropic rejects a request carrying both `temperature` and `top_p`;
  only `temperature` is sent and `top_p` is recorded as the provider default.
- `TOOL_TIERS` is the single source of `tool_calls[].assurance` and the
  projection raises on an undeclared tool; `episode.A2_VERDICTS` refuses
  `proved`; `test_agent_graph.py` asserts the `Gate`/`Dispatch`/`Check`
  nodes are absent — A4 deletes that assertion deliberately.

### A3 — tactic catalog v1
`artifacts/autogenesis/tactic-catalog-v1.json` + schema + validator: the eight
tactics already described in `bounded_induction_support/mod.rs`'s module doc
(refl closure, bounded structural induction, IH-congruence rewrite,
residual-lemma splice, absurd elimination, case-split elimination,
split-congruence site generalization, absorbing-argument chaining), each with
a structural precondition, residual shape, budget, and measured reach
(accepted / declined goals). Census counts **distinct goal shapes matched**,
never targets. `Plan.tactic_ids` resolves here.

### A4 — C tools behind approval; first autonomous proof
`bounded_induction` and `modeq_family` as deferred tools (`plan_check` was not
built: the two producers are what the Python binding exposes, and a third tool
that shelled out to a cargo example would have been the only thing in the tier
whose result was not a typed object); `Gate` → `Dispatch` → `Supervise` →
`Check` → `StageTransaction`; supervisor approves by policy, never by model;
`StageTransaction` calls `prepare-autogenesis-fact-transaction.py` only. Exit:
one fact moved toward `proved` by a plan the model chose and the kernel
checked, with a committed, replayable episode.

### A4 result (measured 2026-08-24, live)

**The loop closed.** Six eligible facts on `anthropic:claude-sonnet-4-5` with
`UsageLimits(cost_limit=1.00, request_limit=10, tool_calls_limit=16)`:
**$1.551 total, mean $0.259**; **2 `proved`, 4 `declined`** (3 `gate-refused`
from an honest `NoGeneralRoute`, 1 `retrieval-miss` from the tool itself).

The two are `F:ml430-nat-modeq-refl-d870c8f5` (`proof_sha256` `1c0507f1…`) and
`F:ml430-nat-modeq-symm-0a3d4d18` (`c3c8334e…`): the model chose
`T:modeq-equivalence-combinators` / `close_terminal`, named three eligible
siblings, a deterministic gate passed the plan, a deterministic supervisor
approved the deferred call, the producer searched, a kernel admitted, and a
**second kernel** re-derived the same term with an empty measured
`axiom_footprint`. Neither digest appears in any committed manifest — these are
results the ledger does not have, not reproductions. `ledger_writes` is 0 in
every episode and the ledger is byte-unchanged.

What the exit criterion says and what was achieved differ in one place, and it
matters. The facts moved *toward* `proved`, not into it: `StageTransaction`
runs the read-only proposal writer and it exits **1** for every A4 target,
because a transaction is derivable only from a registered authoritative
operation plus an execution receipt, and **no registered operation covers the
`Nat.ModEq` family** — which is exactly where
[`docs/autogenesis/250-natural-modeq-capability-selection.md`](../autogenesis/250-natural-modeq-capability-selection.md)
deliberately stops. So `via_multi_target` has not moved. The nonzero exit is
recorded in `checker_runs[]` rather than swallowed, because it is the finding
the human ledger-writing step needs.

Four findings A5 and A7 inherit:

1. **A2's `NoGeneralRoute` baseline was partly a retrieval artifact.**
   `frontier_select` capped a page at 60 rows against 98 eligible facts, while
   the generality rule asks for three siblings *from ids the tools showed you*.
   The first live A4 episode declined `Nat.ModEq` reflexivity naming only the
   two ModEq facts its page contained, with symmetry and transitivity eligible,
   unseen, and closable by the same producer in milliseconds. `MAX_ROWS` is now
   120; the same fact, model and prompt then closed. A capability census (A7)
   run against a truncated page would have measured the page.
2. **`retrieval-miss` is the dominant real obstruction, not a proof failure.**
   Of 98 eligible facts, exactly **3** have a frozen, proof-free statement
   export a producer can import — `Nat.ModEq` refl, symm and trans, from the
   development adapters. The other 95 have none, so no producer in this loop
   can attack them at all. The bottleneck between here and volume is the Lean
   export step on s5, not the producers.
3. **The generality rule produced a measured false negative.** All three
   exportable facts close, axiom-free, in milliseconds (`propose_modeq_family`,
   verified directly). The model routed two of them and emitted
   `NoGeneralRoute` for transitivity — after seeing the whole eligible page.
   The rule is a filter on the model's *confidence that a route generalizes*,
   not on whether it does, and the gap between those two is now measurable: it
   is 1 of 3 here. A7's census answers it properly by running every tactic
   precondition against every open fact without a model in the loop.
4. **An operation registry entry is still the gate to admission.** The loop can
   now manufacture kernel-checked, axiom-free proofs of open facts faster than
   the registry can be widened to accept them, which inverts the constraint doc
   228 described.

### A5 — obstruction graph from typed declines
*Classify* node maps `Decline` objects to the AG4.1 taxonomy; proposals of
`blocked-by` overlay links; a generated dashboard answering "which capability
removes the largest measured cluster?"

### A5 result (measured 2026-08-24)

The census, from `scripts/gen-obstruction-graph.py`:

```text
OBSTRUCTIONS|entities=12|links=28|facts_blocked=19|from_episodes=16|
from_decline_records=11|largest_cluster=O:tactic-precondition-unmatched-b14d25ec:6
```

F3's funnel over the sixteen episodes: **goal 16 -> adapter 2 -> producer 2 ->
reconstruction 2 -> checker 0 -> obstruction 14.** Three episodes dispatched a
tier-C producer and one of those three came back `retrieval-miss`, so `adapter`
is 2 and not 3. `checker` is the registry/transaction stage and it is **0** --
both proofs were kernel-checked with an empty axiom footprint and neither had a
registered operation to land in, which is A4's finding 4 now visible as a stage
rather than as prose.

The ranked answer to F3's question has two halves and both matter:

* **By capability:** `K:proposed-tactic-precondition-mobility-census` -- named
  for 3 clusters covering **10 of 19 blocked facts**, and it does not exist. It
  is slice A7: run every tactic precondition against every open fact with no
  model in the loop. A4's finding 3 already measured why -- the three-sibling
  rule filters the model's *confidence* that a route generalizes, not whether it
  does, and the gap was 1 in 3 on the exportable ModEq facts.
* **By single cluster:** `O:tactic-precondition-unmatched-b14d25ec`, 6 facts,
  removed by `K:bounded-structural-induction` -- which **already exists and is
  `active` in the overlay**. That is a scheduling finding, not an engineering
  one: the capability is built and has not been pointed at the population. The
  cluster's own decline record names what would close it, in its own words.

Two findings A7 inherits:

1. **`no-general-route` and `gate-refused` are one obstruction, not two.** A4's
   gate refuses a `NoGeneralRoute` plan, so the identical model behaviour that
   A2 recorded as `no-general-route` A4 records as `gate-refused`. The
   classifier reads the *proposal variant* as the first blocker and lets the
   decline class join the known set; keying on `decline_class` alone would split
   one cluster in two and blame the mathematics for a change in our own graph.
2. **A single decline record can declare a larger population than six episodes
   assemble.** The top cluster rests on one record's `generalization.sibling_fact_ids`
   (7 rows, 6 after the must-decline filter) while the runner-up was built one
   episode at a time. The dashboard prints the evidence count beside every
   cluster for exactly this reason, and A7's census is what would settle which
   of the two is the better estimate.

*Classify* is **deterministic**, though plan 03's node list draws it in italics.
Its inputs are already typed values, a model call would put the cluster keys
outside the replay guarantee, and the same mapping has to re-derive in
standard-library code under `scripts/`. Rationale and the agreement test:
[`06-obstruction-graph.md`](06-obstruction-graph.md). No field was added to
episode schema v2.

### A6 — guarded web and Python tools
`web_fetch` restricted to arXiv / Semantic Scholar metadata and the pinned
`math-education` sibling; disabled entirely when the target's **family**
contains a held-out member; a sandboxed `python_exec` (smolagents'
`LocalPythonExecutor` pattern, `MemoryMax` + `MemorySwapMax`). Open web search
requires its own ADR.

### A7 — mobility census and evaluation
Run every tactic precondition against every open fact without running a
producer; publish matched / zero-match; the zero-match clusters are the
capability backlog. Draw every Nth episode from the must-decline population
(9 rows, `check-autogenesis-must-decline-population.py`).

### A7 result (measured 2026-08-24)

Full write-up: [`07-mobility-census.md`](07-mobility-census.md). Artifact:
`artifacts/autogenesis/mobility-census-v1.json`; dashboard:
[`docs/plan/generated/mobility-census.md`](../plan/generated/mobility-census.md).

```
MOBILITY|open=191|evaluable=4|unevaluable=187|tactics=9|matched_pairs=2|zero_match_facts=2|clusters=2|held_out_excluded=57
```

**The census answers finding 3 and the answer is that finding 2 dominates it.**
Nine tactic preconditions were evaluated over 191 open facts with no model and
no producer, three-valued (`matched | unmatched(reason) | unevaluable(reason)`).
**187 of the 191 have no frozen statement export, so they were never looked at
at all** — A4 measured 3 of 98 on one page; over the whole ledger it is 4 of
191, and all four are the same `Nat.ModEq` adapter run. A two-valued census
would have published those 187 as zero-match and made the capability backlog
187 entries of fiction. The 57 held-out rows are counted and never named;
`check-autogenesis-holdout-isolation.py` is `PASS` at `references=0` over 1022
files.

The three ranked zero-match clusters are therefore only two, both of size 1,
both `development`, and the ranking is not the finding:

| rank | size | why every tactic declined |
|---|---|---|
| 1 | 1 | `F:ml430-nat-modeq-comm-24b71e7a` — `goal-head-is-not-eq-shaped`, `goal-does-not-unfold-to-an-eq-shaped-head`, `no-hypothesis-binder-to-classify` (the goal is an `Iff`; no tactic's precondition admits one) |
| 2 | 1 | `F:ml430-nat-modeq-refl-d870c8f5` — `goal-head-is-not-eq-shaped`, `no-equation-shaped-hypothesis`, `no-hypothesis-binder-to-classify` (reflexivity has no hypothesis; every combinator precondition demands one) |

The reach cross-check re-evaluates the catalog's own `accepted_goals`:
`REACH|rows=21|evaluable=16|disagreements=7|initial_goal_disagreements=4`. Three
are rows citing a `succ`-case sub-goal (a population mismatch, not a defect);
**four are real** and are reported rather than repaired, because the catalog is
another lane's file: `T:residual-lemma-splice` on both ascFactorial facts, and
`T:modeq-equivalence-combinators` on `int-modeq-refl` (no hypothesis) and
`int-modeq-comm` (an `Iff`). The last is the same shape as zero-match cluster 1
seen from the other side: a tactic titled "eq-**iff** combinators" whose
precondition admits only `Eq`.

Must-decline sampling: `MUST_DECLINE|rows=9|evaluable=0|unevaluable=9|suspect=0`.
None of the nine has an export, so **`suspect = 0` is "not looked at", not
"clean"** — the command exits **2** in that state, distinct from 1 (a real
suspect) and 0 (evaluated and clean).

Facts A5 inherits:

- **The largest measured cluster is not a tactic gap.** Any "which capability
  removes the largest cluster?" dashboard must rank the export pipeline first,
  or it is ranking the wrong axis. Nine exports for the must-decline rows are
  the cheapest item on it: they turn a negative control that currently cannot
  fail into one that can.
- **`unevaluable` is an obstruction class, not an error.** It maps to
  `retrieval-miss`, and this census sizes it at two orders of magnitude above
  everything else.
- The checker is `scripts/check-mobility-census.py` (standard library only, 39
  mutation-verified guards, each killing exactly one test); `just check` and
  `scripts/check.sh` validate the committed file and never regenerate it.

## Exit criteria for the plan

- ≥ 1 fact proved autonomously end to end with a replayable episode (A4).
- `multi_target_operations` or `via_multi_target` in the provenance ledger
  moved by an agent-chosen route.
- Every episode passes `check-agent-episode.py`; every guard has a mutation
  control.
- Zero held-out references in any episode (`check-autogenesis-holdout-isolation.py`).
- Cost per episode recorded in the artifact and summarized in a generated
  dashboard; budget exhaustion is a verdict, not an error.

## Non-goals

DSPy-style prompt optimization (later, once episodes exist in volume — the
kernel is a non-gameable metric, which is rare and worth waiting for); open web
search; any change to fact readiness or admission; MCP transport (local
subprocess/in-process tools do not need it).
