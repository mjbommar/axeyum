# An agentic frontier-expansion framework for Axeyum

Design study. Repo at `0874b9e4fc6c738eb776fa94bf39799c58481b7b`, branch
`codex/autogenesis-knowledge-f1`, 2026-08-24.

**Method note.** Anything I label *measured* I ran myself, foreground, bounded,
on this host. Anything labelled *from docs* carries the URL it was read on.
Where I could not verify a claim, I say so. No repo file was modified and no
cargo command was run.

---

## The one-paragraph answer

Use **pydantic-ai v2** (`pydantic-ai-slim`) for the agent and tool layer, in a
separate `uv`-managed package that the repository's gates do not import. Do not
let it write anything. Axeyum already contains the exact architecture this
problem needs — a **proposer → hashed typed bundle → fresh-process checker →
receipt → transaction** pipeline in which the proposer is deterministic,
disposable, and structurally powerless — and the correct move is not to build an
agent loop beside it but to make the LLM a *drop-in replacement for the proposer
only*, emitting the same bundle JSON that `autogenesis-induction-proposer.py`
emits today. The trust boundary then needs no new enforcement: it is already a
process boundary with a content-addressed interface, and
`validate-autogenesis-operations.py`'s closed `EXECUTION_DRIVERS` allowlist means
the agent cannot even name a new executable. The genuinely new engineering is
not the agent. It is the **episode artifact**, which does not exist yet, and a
checker for it whose exit status depends on what the episode found.

---

## A. Framework evaluation

### Measured on this host

`uv` 0.11.1, system Python 3.14.4, no `pydantic` and no `pydantic_ai` installed.
Current PyPI releases (`https://pypi.org/pypi/<name>/json`):

| package | version | `requires_python` | uploaded |
|---|---|---|---|
| `pydantic-ai` / `-slim` / `pydantic-graph` / `pydantic-evals` | **2.33.0** | `>=3.10` | 2026-08-21 |
| `langgraph` | 1.2.11 | `>=3.10` | 2026-08-11 |
| `openai-agents` | 0.22.0 | `>=3.10` | 2026-08-19 |
| `smolagents` | 1.26.0 | `>=3.10` | 2026-05-29 |
| `claude-agent-sdk` | 0.2.144 | `>=3.10` | 2026-08-21 |
| `dspy` | 3.3.1 | `<3.15,>=3.10` | 2026-08-21 |

Dependency closures resolved on Python 3.14 (`uv pip compile --python-version
3.14`): `pydantic-ai` **99 packages**; `pydantic-ai-slim[anthropic,mcp]`
**65**; `langgraph` **35**; `openai-agents` **38**. All resolve cleanly. The
slim closure pulls `pydantic-graph==2.33.0`, `mcp==1.29.0`, `anthropic==1.0.0`,
`httpx2==2.12.0`, `opentelemetry-api`, and `logfire-api` (the no-op shim, not the
SaaS client).

**Two facts that invalidate stale knowledge**, both from
`https://pydantic.dev/docs/ai/project/changelog/`: pydantic-ai is on **v2**
(2.0.0 shipped 2026-06-23), and `https://ai.pydantic.dev/` now 301-redirects to
`https://pydantic.dev/docs/ai/overview/`. Anything an LLM remembers about the v1
API is substantially wrong.

### The unstated repository constraint

I checked every import across the 640 scripts in `scripts/`:
`hashlib` 520, `pathlib` 510, `json` 485, `sys` 446, `typing` 315, `argparse`
194. There is **no `pyproject.toml`, no `requirements.txt`, and no third-party
import anywhere in `scripts/`**. Every gate in `just check` runs on the standard
library. That invariant is real even though nothing writes it down, and it
decides the packaging: *the agent must be optional and out-of-tree from the
gate's point of view.* If any checker ever imports `pydantic`, a fresh-machine
`./scripts/check.sh` starts requiring a network install and the repository loses
the property that its trusted checking runs anywhere. So:
`tools/frontier-agent/pyproject.toml`, `uv`-managed, never imported from
`scripts/`. Artifacts cross between them as JSON on disk — already how every
producer/checker pair here communicates.

The other reading of that table: `hashlib` in 520 of 640 scripts. Content
addressing is this repository's native idiom, and the episode artifact (§D) must
be canonical-JSON + SHA-256, not a framework-native checkpoint.

### The adjudication

Criteria, in the order they matter here: (1) typed tool I/O with validation
feedback; (2) the run serializes to a committable artifact; (3) provider-agnostic
with pinnable model ids; (4) a proposal-then-gate primitive; (5) the loop is a
state machine we own.

**pydantic-ai v2** wins on 1, 3 and 4, and — importantly — *loses* on 5 in a way
that turns out to be an advantage.

- Tool schemas are derived from type hints; `griffe` parses docstrings for
  parameter descriptions and `require_parameter_descriptions=True` enforces them;
  `args_validator=` runs business-logic validation before execution and may raise
  `ModelRetry` (retry with correction, consumes budget) or the v2-only
  `ToolFailed` (terminal, does not consume budget)
  (`https://pydantic.dev/docs/ai/tools-toolsets/tools-advanced/`).
- **Deferred tools are the proposal-then-gate primitive, first class.**
  `@agent.tool_plain(requires_approval=True)`, or raise `ApprovalRequired` /
  `CallDeferred` conditionally; the run then *ends* with output
  `DeferredToolRequests`, and resumes via
  `agent.run_sync(..., message_history=..., deferred_tool_results=DeferredToolResults(...))`
  where an approval is `True` or `ToolDenied('reason')`
  (`https://pydantic.dev/docs/ai/tools-toolsets/deferred-tools/`). That is
  exactly "the untrusted proposer stops, a trusted process decides, the run
  continues" — and both halves are typed Pydantic objects, so the pause point is
  a committable artifact rather than a checkpointer row.
- Model ids **must** carry a provider prefix in v2; bare names raise. Pinning is
  enforced by the library rather than by our discipline. `openai:` now means the
  Responses API and `openai-chat:` the Chat Completions API — a rename worth
  knowing before writing config.
- `UsageLimits` carries `input_tokens_limit`, `output_tokens_limit`,
  `request_limit`, `tool_calls_limit`, and `cost_limit=Decimal(...)`, raising
  `UsageLimitExceeded`; tools read the remaining budget from `ctx.usage_limits`.
  Budgets are a library feature, not something we bolt on.
- `models.ALLOW_MODEL_REQUESTS = False` plus `TestModel` / `FunctionModel`
  (`https://pydantic.dev/docs/ai/guides/testing/`) gives a hard global guard
  against accidental live calls. This is the mechanism that makes an episode
  *replay* deterministic (§D), and it is the honest answer to determinism —
  `ModelSettings.seed` exists but the docs themselves hedge that even
  `temperature=0.0` is not fully deterministic
  (`https://pydantic.dev/docs/ai/api/pydantic-ai/settings/`).

**The one finding that changes the design:** `pydantic_graph.persistence` is
**removed in v2** with no equivalent — `FullStatePersistence`, `FileStatePersistence`
and `iter_from_persistence` are v1-only. The first-party replacement,
`StepPersistence`, lives in the separately-versioned `pydantic-ai-harness`
(**0.24.0**, pre-1.0) (`https://pydantic.dev/docs/ai/harness/step-persistence/`).
Graphs in v2 are therefore *not* resumable out of the box.

That sounds like a disqualification and is not, because **we do not want
framework-owned persistence.** A LangGraph SQLite checkpoint or a Harness
`SqliteStepStore` row is not a referee-auditable artifact: it is not
content-addressed, not diffable, not stdlib-checkable, and not something
`scripts/check-agent-episode.py` can validate without installing the framework
that wrote it. The episode is ours. The removal simply deletes a tempting wrong
answer. Use `pydantic-graph`'s `BaseNode` (or the new v2 `GraphBuilder` API,
`https://pydantic.dev/docs/ai/graph/builder/`) for control flow only, and treat
`result.all_messages()` + `ModelMessagesTypeAdapter` as the serialization route.

The alternatives, honestly:

- **LangGraph 1.2.11** is the strongest competitor and the only one whose
  persistence and human-in-the-loop story is genuinely battle-tested
  (`interrupt()` + `Command(resume=...)`, `get_state_history()`, forking via
  `update_state`). Its own docs state the limit we care about: *"Replay
  re-executes nodes — it doesn't just read from cache. LLM calls, API requests,
  and interrupts fire again and may return different results"*
  (`https://docs.langchain.com/oss/python/langgraph/use-time-travel`), and
  resume "restarts the entire node from the beginning." So replay-from-artifact
  is engineered, not inherited — the same amount of work as with pydantic-ai.
  Meanwhile state is a `TypedDict` by default with runtime validation opt-in and
  documented as slower, tool typing is a LangChain convention layered on top, and
  it drags `langchain-core` 1.x. Defensible if the team already runs it; worse
  typing for a repository whose entire discipline is typed contracts.
- **OpenAI Agents SDK 0.22.0** has arguably the best tool typing (Pydantic
  `Field` constraints propagated into the JSON Schema, validated before
  execution) and a genuinely excellent gate primitive: `result.to_state()` →
  `state.to_json()`, `RunState.from_json(...)` **in a different process**,
  `state.approve(...)`/`state.reject(...)`, resume with `Runner.run(agent,
  state)` (`https://openai.github.io/openai-agents-python/human_in_the_loop/`).
  Against it: non-OpenAI models go through adapters the docs themselves call
  *"beta"*, structured-output reliability degrades off-OpenAI, tracing exports to
  OpenAI's backend unless disabled, and there is no graph layer.
- **smolagents 1.26.0** — its `replay()` only *prints* a log; there is no
  checkpointing, no resumable state, no interrupt. Tools are a dict of type-name
  strings, not Pydantic models. Nine months, three releases. **But its sandboxing
  is the best of the five** — `LocalPythonExecutor`'s AST allowlist,
  `executor_type` ∈ `local|blaxel|e2b|modal|docker`, a Pyodide/Deno
  `WasmExecutor`, and the refreshingly blunt doc line that *"no local python
  sandbox can ever be completely secure"*
  (`https://huggingface.co/docs/smolagents/en/tutorials/secure_code_execution`).
  Borrow the executor for the Python tool family; do not adopt the agent.
- **claude-agent-sdk 0.2.144** — `can_use_tool` is a real interposition point,
  and `resume_session_at=<message-uuid>` plus `fork_session` is per-message time
  travel. Three disqualifiers for a pipeline spine: it is Claude-only by design;
  PyPI metadata says MIT while the README says use is governed by Anthropic's
  Commercial Terms (a discrepancy worth flagging to whoever owns licensing); and
  it shells out to a bundled CLI versioned independently of the Python package,
  at 8 releases in 9 days. Also a trap: `can_use_tool` fires *only when
  permission evaluation falls through to a prompt* — a permissive
  `permission_mode` or an `allowed_tools` entry silently bypasses your gate.
  Excellent for the interactive lane; wrong for the audited one.
- **DSPy 3.3.1** is not a competitor. It optimizes prompts against a metric, and
  this repository has the rarest thing DSPy needs: a **non-gameable automatic
  metric** — "the kernel accepted it, axiom footprint empty." Adopt it later,
  once episodes exist in volume. Optimizing before you can measure is doc 228's
  failure one level up. Note the `<3.15` pin.

**Recommendation: `pydantic-ai-slim[anthropic]==2.33.0` + `pydantic-graph`,
exact-pinned**, with `pydantic-evals` for offline scoring. Exact pins matter
concretely: 2.33.0 exists *because* `anthropic` 1.0.0 landed on 2026-08-20 and
broke unpinned installs, and `pydantic-ai-slim` now depends on `httpx2`, not
`httpx` — a custom `http_client` for `AnthropicProvider` must be an
`httpx2.AsyncClient`. Skip `[mcp]` for now: the Axeyum tools are local
subprocesses and MCP adds a protocol hop for nothing.

---

## B. Tool surface design

The critical local finding: **almost nothing in this repository emits JSON.**
Measured: exactly one Rust example (`explain_corpus`) accepts `--json`, and 10 of
640 Python scripts do. The Rust examples emit TSV or a pipe-delimited
`KEY|field=value|…` line. So every Axeyum tool needs a thin parsing adapter, and
every adapter needs a **pinned-format contract test** — these formats are
unversioned and would drift silently, which is precisely the class of failure
this repository keeps rediscovering.

### Family 3 — Axeyum engines (prebuilt binaries, no cargo lock)

84 entries under `target/release/examples/`. Measured contracts:

| binary | invocation | output (measured) |
|---|---|---|
| `smtcomp_cli` | `<file.smt2> [--timeout-ms N]` | one line `unsat`/`sat`/`unknown`, exit 0. The only sanctioned front door |
| `theorem_axiom_footprint` | no args | `nat: 139 theorems, 139 axiom-free, footprint min=0 mean=0.0 max=0, …` per prelude |
| `nat_theorem_inventory` | no args | TSV `name \t deps \t canonical-type` |
| `prelude_theorem_inventory` | no args | TSV `prelude \t name \t footprint \t …` |
| `theorem_dependency_inventory` | `NAME` | TSV `name \t comma,deps`; **errors on no match** |
| `theorem_knowledge_audit` | `ROOT [--same-type-as N] [--require N] [--deny N] [--expect-axiom-free]` | `KNOWLEDGE_AUDIT_*|…` |
| `autogenesis_induction_plan_check` | `--plans <json> --candidate <n> --budget N --expect proved\|no-proof [--evidence-output P]` | `AUTOGENESIS_INDUCTION_*|…`, nonzero on error |
| `bounded_induction_operation` | `<export.ndjson> <target-definition>` | `BOUNDED_INDUCTION_OK\|target=…\|goal_sha256=…\|proof_sha256=…\|binders_used=…\|axioms=…\|ledger_writes=0`, then `GOAL\|…` and `PROOF\|…` |
| `cas_tour` | no args | human prose with `[CERTIFIED]` markers |

Two with teeth. `theorem_dependency_inventory` fails on a name that does not
match, with the message *"Asking for a theorem and finding none is a failure, not
an empty answer"* — the adapter must propagate that as an error, never as an
empty list. And `cas_tour` is a demo, not an interface: the CAS tool must wait
for a purpose-built example with a machine contract, or the agent is reading
English.

### Family 3b — scripts

`fact-frontier.py --json` is the best tool in the catalog. It already returns the
typed selection surface the loop needs — per fact: `band`, `dependency_ready`,
`epistemic_status`, `external_status`, `fact_sha256`, `fragment`, `route_class`,
`registered_operation_ids`, `would_unlock`, `missing_dependencies`, plus a
`capabilities.decidable_fragments` list — and it has a `--verify` mode, so an
episode can pin the frontier it selected from and prove later it was that one.

Also: `validate-facts.py` (census + `NOVEL --` lines, nonzero on error);
`validate-autogenesis-knowledge.py` → `AUTOGENESIS_KNOWLEDGE_OK|entities=2|links=24|relations=7|sources=2`;
`check-autogenesis-holdout-isolation.py`;
`gen-production-provenance-ledger.py --check` →
`PRODUCTION_PROVENANCE|settled=152|via_multi_target=7|via_capsule=21|no_operation=124|multi_target_operations=2|operations=26`;
`prepare-autogenesis-fact-transaction.py --fact F --output P` (read-only
proposal); `execute-autogenesis-operation.py --frontier F --output P` (receipt
binding commit, frontier, registry, fact, input bytes, rechecked evidence);
`apply-autogenesis-fact-transaction.py --transaction T --journal-dir D` (the only
ledger writer).

### Family 4 — knowledge-graph tools (custom, read-only)

Measured shapes: **350 facts** (191 open, 150 proved, 2 computed, 4 refuted, 3
conjectured), 86 carrying `concept_refs`; **26 operations** (25 authoritative, 1
counterfactual-fixture-only), of which **2** name more than one fact; the overlay
at 2 entities / 24 links / 7 relations; the nursery at 216 entries (78 train, 79
development, 57 held-out, 2 longitudinal); the sibling `../math-education/graph/`
present at exactly the pinned revision `ce3e2a52…`, 1567 concept files and 42
technique files as YAML-front-matter markdown.

Tools, all pure reads: `frontier_select(band, limit) -> FrontierPage` (joins the
nursery partition and **drops every held-out row before the model sees it**);
`fact_get`; `fact_neighbourhood`; `kernel_theorems(prelude, glob)` — the premise
retrieval corpus, roadmap AG3.7; `overlay_query(relation, endpoint)` returning
links with their `assurance` intact; `concept_lookup` / `technique_lookup`
(refusing unless `git rev-parse HEAD` in the sibling equals the pin);
`operation_registry()` with `applicability.fact_ids` intact, so the model can
*see* that 24 of 26 name exactly one fact.

### Families 1 and 2 — web and Python

`web_search(query, provider) -> [SearchHit]` and `web_fetch(url) ->
FetchedDocument{url, fetched_at, sha256, bytes, content_type, snapshot_path}`.
Every fetch is snapshotted into the episode directory and hashed; nothing the
model reads is unrecorded. Prefer arXiv and Semantic Scholar APIs to general
search: structured metadata, far less injection surface.

`python_exec(code, timeout_s) -> ExecResult`, sandboxed, no network, no writes
outside a scratch dir, memory-capped. Apply this repository's own lesson from
`scripts/cargo-serialized.sh`: `MemoryMax` without `MemorySwapMax` is decoration
— it swaps instead of dying, and takes the host with it. sympy cross-checking a
claimed identity numerically before anything is dispatched is the point of this
tool, not general computation.

---

## C. The trust boundary in code

**It already exists, and it is a process boundary, not a convention.**
`autogenesis-induction-proposer.py`'s own docstring states the contract: *"The
proposer does not parse proof bodies or decide whether a plan is valid. It
enumerates the same bounded structural plans for every target binder. A fresh
kernel process validates the binder sort, executes the plan, and decides whether
the resulting term has the registered target type."*

It emits:

```json
{"schema_version":1,"kind":"axeyum-autogenesis-induction-proposals",
 "catalog_sha256":"…","phase":"…","target":{…},
 "policy":"binder-order-then-structural-step",
 "plans":[{"rank":1,"operation":"induct-nat","target_binder":0,
           "base":"definitional-reflexivity",
           "step":"exact-induction-hypothesis"}],
 "bundle_sha256":"…"}
```

and `autogenesis_induction_plan_check` consumes it with `--plans --candidate
--budget --expect proved|no-proof --bundle-sha256 --catalog-sha256`. The checker
is bound to the exact bundle hash **and to an expected outcome**, so its exit
status depends on what it found. That is this repository's answer to its own
"checkers that cannot fail" problem, already implemented in the right place.

**So the LLM replaces the enumerator and nothing else changes.** Same bundle
shape, same hash discipline, a `proposer` field naming the model instead of the
grammar.

### Three tiers, mapped onto the governance doc's existing authority matrix

`docs/autogenesis/05-trust-safety-and-governance.md` already has the matrix
("Select an open eligible fact: autonomous yes"; "Change kernel or checker rule:
no autonomous authority"). The tiers are that table made executable, and
pydantic-ai has a primitive for each.

**Tier R (read).** Everything in §B. No side effects. Bounded by
`UsageLimits.tool_calls_limit`.

**Tier P (propose).** Writes only into
`artifacts/episodes/<episode-id>/proposals/`. Every Tier-P return type carries
`assurance` drawn from the overlay's own enum — `formal-derived |
independently-checked | registry-derived | mechanically-observed | human-reviewed
| heuristic | proposed` — and an LLM-authored proposal may **only** be
constructed with `assurance="proposed"`. Make that a Pydantic field validator,
not a convention: a `ProposedArtifact` whose `assurance` is anything else fails
construction, in the same library the tool schema came from.

**Tier C (check).** Deterministic subprocesses, no model in the loop. Declare
every Tier-C tool `requires_approval=True` so it raises `ApprovalRequired` and
ends the run with `DeferredToolRequests`; a supervising process outside the agent
decides and resumes with `DeferredToolResults`. In week one, deny everything —
the mechanism is then demonstrated before it is trusted.

Compose the tiers with toolset wrappers rather than prompt discipline:
`FilteredToolset` / `.prepared()` / a `PrepareTools` capability can hide Tier-P
and Tier-C entirely on a Gather-only node, so the tools are not merely
unauthorized but *absent from the schema the model sees*.

### The four structural locks

1. **No write tool touches `artifacts/facts/`.** Run the agent process with the
   ledger read-only at the OS level. That converts a policy into a
   `PermissionError`.
2. **`EXECUTION_DRIVERS` is a closed allowlist** of nine strings in
   `validate-autogenesis-operations.py`. An operation naming anything else is
   rejected, so the agent cannot register a route to code it wrote. Adding a
   driver is a human diff to a gated file.
3. **`apply-autogenesis-fact-transaction.py` is the only writer**, and it
   consumes files the agent produced earlier. The agent process does not need the
   ability to invoke it at all in the first increment.
4. **Held-out filtering happens at the tool, not in the prompt.**
   `check-autogenesis-holdout-isolation.py` already fails if *any artifact
   references* a held-out fact id, via a generic string walk — including, by
   construction, an episode file. An agent that so much as writes a held-out id
   into its transcript reddens the gate. Loud, immediate, before any spend.

---

## D. Reproducibility and evidence: the episode artifact

`episode` is already an entity kind in
`artifacts/ontology/autogenesis-knowledge-overlay.schema.json`, and **nothing
owns it** — there is no episode schema. That gap is the highest-value thing to
build here, independent of framework choice.

The model to copy is the statement-adapter manifest, e.g.
`mathlib-modeq-family-refl-statement-adapter-v1.json`, which already binds
`toolchain` (lean version + githash + mathlib commit + lean4export commit),
`external_artifact` (path + sha256 + bytes + records), `independent_import`
(goal_sha256, direct_dependencies, admitted_declarations, axioms), and
`reproduction` (export command, check command). An episode gets that spine:

```
schema_version, kind: "axeyum-agent-episode", episode_id, git_commit
selection:  frontier_sha256, frontier_path, fact_id, fact_sha256,
            partition (train|development; never held-out), eligibility_reason
policy:     model_id (provider-prefixed, exact), temperature, top_p, max_tokens,
            seed|null, prompt_hashes{}, toolset_sha256, agent_code_sha256,
            library_versions{pydantic-ai, pydantic-graph, anthropic, httpx2}
budgets:    wall_seconds, request_limit, tool_calls_limit,
            input_tokens_limit, output_tokens_limit, cost_limit_usd
transcript: messages_sha256, messages_path,
            tool_calls[]{ordinal, tool, args_sha256, result_sha256,
                         assurance, duration_ms, exit_status}
web_snapshots[]{url, fetched_at, sha256, bytes, path}
proposals[]{path, sha256, kind, assurance:"proposed"}
outcome:    verdict ∈ proved|declined|error|budget-exhausted,
            decline_class (AG4.1 taxonomy)|null, checker_command,
            checker_exit_status, checker_output_sha256, axiom_footprint[],
            ledger_writes (MUST be 0), search_invocations,
            target_theorem_submissions
observed:   facts_unlocked[], operations_widened[], overlay_links_proposed[]
```

Four of those field names are lifted verbatim from
`execute-autogenesis-operation.py`'s receipt builder, which already tracks
`ledger_writes`, `retained_answer_dependencies`, `search_invocations` and
`target_theorem_submissions`. Reusing them is deliberate: an episode should be
diffable against a receipt.

**Mapping pydantic-ai onto it.** `result.all_messages()` returns
`ModelRequest`/`ModelResponse` objects; `ModelMessagesTypeAdapter` is the
documented serialization route
(`https://pydantic.dev/docs/ai/core-concepts/message-history/`). Serialize,
hash, commit — that is `transcript.messages_*`. Tool calls appear inside that
same list as `ToolCallPart`/`ToolReturnPart`, so `tool_calls[]` is a *projection*
of the transcript rather than a parallel log that can silently disagree with it.
`output_type` gives the run a typed terminal value; make that value the
`outcome` block, so the agent cannot finish without producing one. And
`capture_run_messages()` in v2 captures interrupted runs with
`state='interrupted'`, which is how a `budget-exhausted` episode still gets a
transcript.

**The checker.** `scripts/check-agent-episode.py`, stdlib-only, exit status
dependent on the finding. It must fail when: `git_commit` is not an ancestor of
HEAD; `frontier_sha256` does not re-derive via `fact-frontier.py --verify`; any
`web_snapshots[].sha256` mismatches the file on disk; `ledger_writes != 0`;
`partition == "held-out"` or any held-out id appears anywhere in the document;
`outcome.verdict == "proved"` while `checker_exit_status != 0`; any
`proposals[]` digest mismatches its file; or `tool_calls` is empty — a run that
called nothing must not read as a clean decline. Register it in
`scripts/tests/mutation_controls.py`, delete each guard, require **exactly one**
test to die. Use that harness rather than a hand loop: it copies to a scratch
tree (so it does not break sibling lanes' builds) and runs `py_compile` (so the
`__pycache__` staleness trap cannot fabricate a `KILLED`).

**On determinism, stated honestly.** Governance invariant 7 already says
"Determinism governs acceptance and replay even when proposal generation is
stochastic." So the claim is not *reproducible* — LLM sampling is not, and
pydantic-ai's own docs hedge that even `temperature=0.0` is not fully
deterministic. The claim is **replayable**: given the committed transcript, every
checker verdict re-derives bit-identically, because the checkers are
deterministic subprocesses over content-addressed inputs. Build
`replay --from-transcript` immediately after the schema: run the graph with
`models.ALLOW_MODEL_REQUESTS = False` and a `FunctionModel` that returns the
recorded responses in order. If a replay diverges, that is a finding — and it is
the property no framework in §A gives you for free.

---

## E. The loop

A `pydantic-graph` state machine. Deterministic nodes **bold**, LLM nodes *italic*.

```
  **Select**  frontier --json → join nursery → drop held-out → rank
      ▼         (deterministic: the model never sees an unfiltered list)
  *Gather*    Tier R only: fact_get, neighbourhood, kernel_theorems,
      ▼         overlay_query, concept/technique, web (guarded, §F)
  *Plan*      typed output StrategyProposal{producer_id, capability_id,
      ▼         plan[], why, expected_decline_class, sibling_fact_ids[≥3]}
  **Gate**    refuse if producer_id ∉ registry, any sibling held-out,
      ▼         budget exhausted, or plan shape unknown
  **Dispatch** bounded_induction_operation / plan_check / smtcomp_cli,
      ▼         fresh process, hard timeout
  **Check**   independent re-derivation; axiom footprint; exit status decides
      ├─ proved  → **StageTransaction** (prepare-…, never apply-…) → **WriteEpisode**
      └─ declined → *Classify* (AG4.1 taxonomy) → **UpdateObstructions**
                    (proposals only) → **WriteEpisode** → **Select**
```

Three LLM nodes only: Gather (retrieval), Plan (strategy), Classify (decline
taxonomy). Selection is deterministic on purpose — it is where holdout
contamination and neighbourhood-chasing both enter. Budgets live on `Gate` and
on `UsageLimits`; `budget-exhausted` is a first-class verdict, distinct from
`declined` and from `error`, per governance invariant 1.

### Addressing "dispatch table, not producer"

Doc 228's finding — 24 operations, 23 facts covered, 0 naming more than one fact,
0 of 144 ready facts covered — is a property of what the loop *optimizes*, and
per-episode success cannot detect it. **My measurement today: 104 facts are open,
dependency-ready and not held-out; 0 of them are covered by any registered
operation.** The registry is at 26 operations with 2 multi-target;
`gen-production-provenance-ledger.py --check` reports `via_multi_target=7` of
`settled=152`.

Three structural answers:

1. **`StrategyProposal.sibling_fact_ids: list[str] = Field(min_length=3)`.**
   Before proposing anything, the model must name three other frontier facts it
   believes the same route reaches. That is doc 228's item 2 turned into a
   Pydantic constraint enforced by the tool schema. If it cannot, the honest
   output is a `NoGeneralRoute` decline — itself a finding, and obstruction-graph
   material (doc 243 F3).
2. **Score the episode on generality, not the target.** The metric is how many
   named siblings the same producer closes when dispatched immediately after the
   first success. Target-only success scores 1/4, not 1/1.
3. **Gate the loop on the ledger's own counters** — `multi_target_operations` and
   `via_multi_target` — not on episode count. A run that moves neither is
   activity, and the dashboard should say so.

And the gap the retrospective names as still open: evaluate the loop on the
**must-decline population**. `check-autogenesis-must-decline-population.py`
reports `must_decline=9|ground_truth_verified=9|violations=0`. Draw every Nth
episode from it. A producer that never declines is the checker-that-cannot-fail
one arrow upstream, and nine rows is enough to catch it.

---

## F. Risks and prior art

### Prior art, one clause each on what to borrow

- **Goedel-Architect** (arXiv 2606.06468, 2026-06-04) — agentic Lean 4 framework
  built on *blueprint generation and refinement*, where a blueprint is "a
  dependency graph of definitions and lemmas that builds up to the main theorem";
  open lemma nodes are closed in parallel and failed lemmas drive refinement of
  the global blueprint. **This is the most relevant paper in the list**: it is
  our concept DAG plus our fact ledger, published, with the failure path made
  explicit. *Borrow: the dependency graph as the unit of planning and repair,
  and parallel closure of independent lemma nodes.*
- **"A Minimal Agent for Automated Theorem Proving"** (arXiv 2602.24273, ICML
  2026) — a deliberately minimal baseline (iterative refinement + library search
  + context management) reporting competitive results at a fraction of the cost.
  *Borrow: build this first as the control condition; a repository this worried
  about gates that cannot fail should want a cheap baseline that must be beaten.*
- **Seed-Prover / Seed-Prover 1.5** (arXiv 2507.23726; 2512.17260) — RL that
  accumulates experience across the run; miniF2F is now saturated and the live
  frontier is graduate/PhD. *Borrow: the accumulated-lemma bank — solved subgoals
  become retrievable assets, which is what the fact ledger is for.*
- **LeanDojo / ReProver** (arXiv 2306.15626) — retrieval-augmented tactic
  generation over a mined corpus. *Borrow: premise retrieval as a separately
  evaluated component — roadmap AG3.7, and the highest-leverage LLM use here.*
- **LeanAgent** (arXiv 2410.06209) — lifelong learning across 23 repos with a
  curriculum ordered by proof complexity; 162 previously unproved theorems, with
  backward-transfer measured. *Borrow: curriculum ordering by measured
  difficulty, plus explicit non-forgetting metrics.*
- **Goedel-Prover-V2** (arXiv 2508.03613) — verifier-guided self-correction; an
  8B model beating a 671B at pass@32. *Borrow: compiler-error-in-the-loop repair,
  and the size lesson — a small model in a tight verifier loop beats a large one
  shooting blind.*
- **DeepSeek-Prover-V2** (arXiv 2504.21801) — RL for recursive subgoal
  decomposition. *Borrow: decomposition as a recorded artifact, not implicit
  reasoning.*
- **Draft-Sketch-Prove** (ICLR 2023) — informal draft → formal sketch →
  gap-filling by automation. *Borrow: our `Plan` node is the sketch, and the
  sketch is the thing that should be typed.*
- **Lean-STaR** (arXiv 2407.10040) — interleaved rationale and tactic. *Borrow:
  keep rationale in the episode as classifier input; never let it into an
  evidence field.*
- **Lean Copilot** (arXiv 2404.12534) — LLM suggestion inside the ITP. *Borrow:
  suggestion-not-authority as the interaction default.*
- **miniF2F / PutnamBench** — *borrow nothing, and that is the point;* see
  contamination below. Note also that essentially every headline number in this
  field comes from the system's own paper at wildly differing inference budgets;
  pass@1 and pass@8192 are not comparable, and only Goedel-Architect and the
  PutnamBench leaderboard report cost at all. Ask what budget produced a number
  before believing a ranking.

### Risks

**Holdout contamination via web search — the one that will actually happen.**
The nursery preregisters 216 propositions and the split key is
`<family>:<statement-shape>`; doc 228 records one held-out registration spending
19 of 76 rows. Web search makes this far worse, because every Mathlib proof is
one query away and the model need not be *told* the target to retrieve its
neighbourhood. Mitigations, strongest first:

1. **`frontier_select` drops held-out rows before the model sees them** — the
   only mitigation that is structural rather than behavioural.
2. **Web tools disabled entirely on any episode whose target's *family* contains
   a held-out member.** Family, not fact: the partition unit is the family, so
   fact-level filtering leaks by construction.
3. **Every fetch snapshotted and hashed**, with `check-agent-episode.py` grepping
   snapshots for held-out statement text and ids. Late, but worth having.
4. **Prefer a curated corpus to open search.** For the first increment, point the
   "web" family at arXiv/Semantic Scholar metadata and the pinned
   `math-education` sibling only. Open search widens the authorization surface
   and should arrive with its own ADR, as the governance doc requires.

**Prompt injection.** Fetched pages are untrusted text the model reads as
instructions. Wrap every fetched document in a delimiter block with an explicit
"retrieved data" preamble; never let a Tier-R result flow into a Tier-P argument
except through a typed field. But the real defense is tier separation: an
injected instruction cannot write to the ledger because *no tool the agent has
can write to the ledger*.

**Cost.** Bound it in the artifact, not a runbook: `cost_limit=Decimal(...)` on
`UsageLimits` maps to `budgets.cost_limit_usd`, and `budget-exhausted` is a
verdict. Gather dominates; cache on `(tool, args_sha256)` since Tier-R tools are
pure. Note pydantic-ai has *prompt* caching (`CachePoint`) but no response cache
— the memo table is ours to build.

**Determinism versus the repository's promise.** Addressed in §D: replayable,
not reproducible, and the schema must say which. The failure mode to avoid is a
dashboard row that reads as reproducible because everything else here is.

**The measurement trap.** Before believing any number the loop reports, ask what
the command would print if it were broken. An episode with zero tool calls; a
checker that exits 0 on completion; `grep -q` in a pipeline; `$?` after a pipe —
all four have produced confident wrong answers in this repository recently, and
all four are reachable from an agent harness written quickly.

---

## G. Recommended first increment (one week, bounded)

**Goal: one replayable episode artifact, produced by a real LLM proposer over
real Axeyum tools, validated by a fail-closed stdlib checker — that proves
nothing.** Deliberately: the first increment must not touch the ledger, so the
trust boundary is demonstrated before it is loaded.

1. **`artifacts/ontology/agent-episode.schema.json`** (§D). No agent yet. Two
   hand-authored fixtures: one `proved`, one `declined`.
2. **`scripts/check-agent-episode.py`**, stdlib-only, with the eight failure
   conditions in §D. Register in `scripts/tests/mutation_controls.py`; delete
   each guard, require exactly one test to die. *This is the deliverable that
   makes the rest safe, and it must exist first.*
3. **`tools/frontier-agent/`** — `uv` project,
   `pydantic-ai-slim[anthropic]==2.33.0`, `pydantic-graph==2.33.0`, exact pins,
   `requires-python >=3.12`. Nothing under `scripts/` imports it.
4. **Six Tier-R tools only**: `frontier_select` (with the held-out drop),
   `fact_get`, `fact_neighbourhood`, `kernel_theorems`, `operation_registry`,
   `overlay_query` — each with a contract test pinning the exact stdout format
   of the binary or script it wraps. **No web, no `python_exec`, no Tier-P, no
   Tier-C.**
5. **A four-node graph**: `Select` (deterministic) → *Gather* → *Plan*
   (`StrategyProposal` output type, `sibling_fact_ids` `min_length=3`) →
   `WriteEpisode`. It dispatches nothing.
6. **Run against the 104 eligible facts; commit ten episodes.** Then run the
   checker over all ten in CI.

Exit criteria, each independently checkable:

- `check-agent-episode.py` exits 0 on the ten committed episodes and **nonzero**
  on ten hand-made corrupt fixtures, one per guard.
- Every episode has `ledger_writes: 0` and
  `outcome.verdict ∈ {declined, budget-exhausted}` — nothing proved, by
  construction.
- `check-autogenesis-holdout-isolation.py` still passes with the episodes
  committed, proving its generic string walk sees them and the filter held.
- `fact-frontier.py --verify <episode.selection.frontier_path>` re-derives for
  every episode.
- `replay --from-transcript` reproduces every episode's `outcome` block with
  `ALLOW_MODEL_REQUESTS = False`.
- At least one episode's `sibling_fact_ids` names three facts a human reviewer
  agrees share a route — **and at least one episode honestly emits
  `NoGeneralRoute`**. If all ten claim generality, the constraint is being
  satisfied by confabulation and the metric is already broken.

Week two is the short step: add the two Tier-C tools
(`autogenesis_induction_plan_check`, `bounded_induction_operation`) behind
`requires_approval=True`, turn the `Plan` output into the existing bundle JSON
with its `bundle_sha256`, and let the checker decide. At that point the LLM has
replaced the enumerator in a pipeline that was built for exactly this
substitution — and the first autonomously proposed, kernel-checked, axiom-free
theorem is one dispatch away.
