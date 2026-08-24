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
`bounded_induction`, `plan_check` as deferred tools; `Plan` emits the existing
bundle JSON with `bundle_sha256`; supervisor approves by policy (never by
model); `StageTransaction` calls `prepare-autogenesis-fact-transaction.py`
only. Exit: one fact moved `open → proved` by a plan the model chose and the
kernel checked, with a committed episode, and the ledger's
`via_multi_target` counter moved.

### A5 — obstruction graph from typed declines
*Classify* node maps `Decline` objects to the AG4.1 taxonomy; proposals of
`blocked-by` overlay links; a generated dashboard answering "which capability
removes the largest measured cluster?"

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
