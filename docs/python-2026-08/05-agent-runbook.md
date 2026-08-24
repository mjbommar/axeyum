# 05 — Agent runbook: running, replaying, and reading an episode

Slices A2 and A4 of [`03-agentic-layer.md`](03-agentic-layer.md). Measured
2026-08-24 against commit `5e289fe8cfccab7ba6b230a73cacedf6a485a187`.

**Since A4 this loop dispatches — and still cannot admit anything.** The whole
of the change is a tool the model may *ask* to run: both tier-C tools are
declared `requires_approval=True`, so a call ends the run with a
`DeferredToolRequests` output and a deterministic supervisor decides. What the
loop produces is still an *episode*: a record of what a model was allowed to
look at, what it proposed, what a producer returned, and what a **second,
independent kernel** says about that. Admission stays where it was
([`docs/autogenesis/05-trust-safety-and-governance.md`](../autogenesis/05-trust-safety-and-governance.md)):
`apply-autogenesis-fact-transaction.py` is the one ledger writer and it is not
reachable from this package.

Sections below marked **(v1)** describe the A2 four-node path, which still runs
and still replays; `--schema-version 1` selects it.

## Install

```sh
uv sync --dev --extra agent      # pydantic-ai-slim[anthropic], pydantic-graph, pydantic-evals
uv run maturin develop           # the axeyum extension the tools read the kernel through
```

The pins are exact (`==2.33.0`), not ranges: 2.33.0 exists *because*
`anthropic` 1.0.0 landed on 2026-08-20 and broke unpinned installs, and
`pydantic-ai-slim` depends on `httpx2`, not `httpx`. The extra is an **extra**
and not a dependency group because nothing under `scripts/` may import it —
every gate in `just check` runs on the standard library, and a checker that
imported `pydantic` would make a fresh-machine `./scripts/check.sh` require a
network install. `python/tests/test_agent_extra.py` gates both properties and
runs without the extra installed.

## Run

```sh
# offline: no provider is reached, and the episode says so (model_id test:offline)
uv run python -m axeyum.agent run --fact F:ml430-nat-fastfib-eq-cde11774 --offline \
  --out artifacts/episodes/$(date +%F)

# live
export ANTHROPIC_API_KEY=...
uv run python -m axeyum.agent run --next --n 10 \
  --model anthropic:claude-sonnet-4-5 --budget-usd 0.50 \
  --request-limit 8 --tool-calls-limit 12 \
  --out artifacts/episodes/$(date +%F)
```

Model ids **must** carry a provider prefix; pydantic-ai v2 rejects a bare name,
which is pinning enforced by the library rather than by our discipline. In a
lane snapshot (`git archive`, no `.git`) pass `--git-commit <40-hex>`: the
writer refuses to invent one, because a wrong `git_commit` makes the ancestor
rule pass against the wrong history.

`--next` draws from the **eligible** population: open, dependency-ready, and
preregistered `train` or `development` in the nursery. Held-out and
longitudinal rows are dropped inside `frontier_select`, before the model sees a
list — the filter is in the tool, never in the prompt. Measured 2026-08-24: 98
eligible, from 143 dependency-ready (34 held-out, 11 not preregistered).

## Replay

```sh
uv run python -m axeyum.agent replay \
  --from-transcript artifacts/episodes/2026-08-24/episode-a2-ml430-int-gcd-div-5e01872f.json
```

Sets `pydantic_ai.models.ALLOW_MODEL_REQUESTS = False` and feeds the recorded
responses back through a `FunctionModel`, so a replay that accidentally reached
a provider raises instead of quietly costing money. It then compares the
`selection` and `outcome` blocks and **exits nonzero when they differ**;
`selection.frontier_path` is compared by basename because a replay writes into
a scratch directory. Tool-call digests are reported but do not gate the exit
status: the tools read a live ledger, so a fact added by another lane can
legitimately change a result hash.

Replay is *replayable, not reproducible*. `ModelSettings.seed` exists and the
provider docs hedge that even `temperature=0.0` is not deterministic, so the
promise is the narrower checkable one: the deterministic nodes re-derive.

## Where episodes go, and how they are named

```
artifacts/episodes/2026-08-24/
  episode-a2-<fact slug>.json          <- the episode; the ONLY *.json here
  frontier.json.snapshot               <- the frontier every selection was pinned to
  <fact slug>/messages.json.snapshot   <- the serialized message list
  <fact slug>/proposals/proposal-0.json.snapshot
```

**Only episode documents carry a bare `.json` extension.** This is mechanical,
not stylistic: `check-agent-episode.py` walks a directory argument with
`rglob("*.json")` and checks every match *as an episode*, so a transcript
committed as `messages.json` beside its episode would be read as a malformed
episode and redden the gate. Sidecars therefore end in `.json.snapshot`. The A1
fixtures do not hit this because their sidecars are deliberately uncommitted.

`selection.frontier_path` points at a **committed** frontier, so
`frontier-digest` and `frontier-reverify` both bite (A1 finding 1). One census
is shared by every episode of a run.

### The frontier census names held-out ids, and that is not a breach

`frontier.json.snapshot` is `fact-frontier.py --json`: a census of the whole
open ledger, which `--verify` re-derives entry for entry. It therefore
enumerates all 57 held-out fact ids, exactly as
`artifacts/autogenesis/nursery-v1.json` does — and
`check-autogenesis-holdout-isolation.py` exempts that file for the same reason,
as a `POPULATION_FILE`. A filtered census would fail the very rule that makes
it evidence.

What must be zero, and is: the ten **episode documents**, the ten
**transcripts** and the ten **proposals** contain no held-out id at all
(measured 2026-08-24, against a positive control that finds all 57 in the
nursery). Three independent mechanisms hold that line — the partition filter
inside `frontier_select`, a write-time byte walk in
`episode.assert_no_held_out` that refuses to write, and the checker's own
generic string walk over the episode document.

Note that `check-autogenesis-holdout-isolation.py` scans
`artifacts/autogenesis/*.json` and `artifacts/facts`, **not**
`artifacts/episodes`. It is not the gate that protects episodes; the walk
inside `check-agent-episode.py` is, and it imports the held-out set from the
isolation script rather than re-deriving it so the two cannot drift.

## What the checker enforces

```sh
python3 scripts/check-agent-episode.py artifacts/episodes
python3 scripts/check-agent-episode.py artifacts/episodes --require-ancestor   # full checkout
```

The last line is `EPISODES|checked=N|ok=K|failed=M`. **Read the count, not just
the status**: `checked=0` exits nonzero on purpose, because a check that
checked nothing is not a pass. Twelve rules, each with a mutation control:
schema, git-commit-ancestor (opt-in), frontier-digest, frontier-reverify,
web-snapshot-digest, ledger-writes-must-be-zero, held-out-reference,
proved-requires-zero-checker-status, proved-requires-checker-command,
proposal-digest, empty-transcript, unknown-fact-id.

Three of those are the load-bearing ones for A2:

- `ledger_writes` must be `0`. An episode has no admission authority, and the
  writer refuses to build a document claiming otherwise.
- `verdict == "proved"` requires a checker that exited 0 **and** a named
  command. A2 can write only `declined` and `budget-exhausted`; the writer
  raises on anything else, because `proved` needs a `checked` tool call and the
  C tier does not exist yet.
- a held-out id **anywhere** in the document is a failure, found by a generic
  recursive string walk rather than a field-specific guard.

## Reading a run

```
AGENT_EPISODE|path=…|fact=…|verdict=declined|decline_class=no-general-route|route=none
             |requests=6|tool_calls=8|input_tokens=34818|output_tokens=1299
             |cost_usd=0.123939|cost_limit_enforced=true
```

`cost_limit_enforced=false` means genai-prices had no pricing for the model, so
`UsageLimits.cost_limit` could not fire — pydantic-ai emits a
`CostNotFoundWarning` and the run continues on its request, tool-call and token
limits. It is printed because a budget that cannot fire is decoration, and a
harness that hid the difference would be the "checker that cannot fail" defect
moved into the accounting. (`TestModel` is always unpriced; measured
2026-08-24, `anthropic:claude-sonnet-4-5` is priced.)

`route=none` is `NoGeneralRoute` — the model saying it cannot name three other
eligible facts this route would reach. That is a **result**, not a failure: it
is the datapoint slice A5 builds the obstruction graph from, and a schema that
forced a three-sibling claim where none exists would poison exactly that
measurement.

## Budgets

`UsageLimits(cost_limit, request_limit, tool_calls_limit, input_tokens_limit,
output_tokens_limit)` plus a wall-clock deadline checked between nodes. Budget
exhaustion is a **verdict**, not an error: the episode is written and says
`budget-exhausted`, because "the loop ran out of money" and "the loop crashed"
are different findings.

Measured 2026-08-24 over ten live episodes at `request_limit=8`,
`tool_calls_limit=12`: eight completed and two exhausted, at a mean of
$0.163 and a total of $1.635.

## A4: dispatch, approval, and the second kernel

### The nine nodes

```
Select -> Gather -> Plan -> Gate -> Dispatch -> Supervise -> Check -> StageTransaction -> WriteEpisode
```

Five of the nine run **no model**, and they are the five that could do damage:
`Select` (what to work on), `Gate` (may this plan be dispatched), `Supervise`
(is this call approved), `Check` (did the proof re-derive), `WriteEpisode`
(what is written down). `Gather`, `Plan` and `Dispatch` are the model, and only
`Dispatch` is even *shown* a tier-C tool.

`Supervise` holding no model is the load-bearing property, not a stylistic one:
an LLM deciding whether an LLM's plan may run is not a gate, it is the same
actor twice. `test_agent_graph.py` asserts it by inspecting the node's source
and the signature of `supervisor_decision`, because a docstring saying so would
survive the change that broke it.

Every node can short-circuit to `WriteEpisode`. A run that was gated, denied,
declined or cut short still produces its artifact.

### The two tier-C tools

```
bounded_induction(fact_id) -> Accepted | Declined | Error
modeq_family(fact_id)      -> Accepted | Declined | Error
```

Each one resolves the fact's frozen, proof-free statement export, **re-hashes
the bytes against the pinned digest**, imports them into a kernel, runs the
producer, and hands the term to `Kernel.add_declaration` — the kernel decides,
not the producer. The `axiom_footprint` on the result is *measured* on the
admitted name. Neither tool raises for a decline: `Declined` carries the
producer's own typed Rust variant, and a decline delivered as an exception
lands in the harness's error path where it reads as a crash.

Resolution has two routes and the order matters. A committed statement-adapter
manifest (`source_fact_id` + `external_artifact`) is authoritative and is tried
first; all nine facts of the two multi-target operations resolve that way.
`artifacts/autogenesis/agent-frozen-export-index-v1.json` is consulted only for
exports that were produced and never registered — today, the four `Nat.ModEq`
development adapters from
[`docs/autogenesis/250-natural-modeq-capability-selection.md`](../autogenesis/250-natural-modeq-capability-selection.md).

A fact with no export at all comes back `retrieval-miss`, an AG4.1 class. That
is a **finding about the pipeline**, not about the mathematics, and the
taxonomy keeps them apart deliberately.

### What the gate and the supervisor refuse

`Gate` (deterministic, pre-dispatch) refuses a `NoGeneralRoute` plan, a
`producer_id` that resolves in the vocabulary but has no tool behind it, a plan
targeting a fact other than the selected one, **any sibling outside train or
development**, less wall budget than one producer call, and a target another
lane settled since selection.

`Supervise` (deterministic, at the approval) approves only when the gate
passed, the tool is the one the gate routed to, the call's `fact_id` is the
selected fact, and the ledger still calls it open. A denial is
`ToolDenied(reason)`, so the model is told why — a denial the model cannot see
is a denial it will make again.

### The independent re-check

`Check` builds a **second kernel** from the same export, re-runs the producer,
re-renders and re-hashes, and only then compares against the digest the tool
reported. It has to work that way: an `ExprId` is an index into the kernel that
interned it, so a term cannot be carried across. Two kernels agreeing is a
different claim from one kernel consulted twice.

It is recorded as a `checker_runs[]` entry whose `command` is a thing you can
run:

```sh
uv run python -m axeyum.agent check \
  --fact F:ml430-nat-modeq-refl-d870c8f5 --producer modeq_family \
  --expect-proof-sha256 1c0507f1ded168f7bea07c8e63e3cf92b27166328eb9468e7ee77ae635abb4f9
```

It exits 0 only when a second kernel re-derives exactly that term with an empty
footprint, and it discriminates: a digest mismatch, an absent export and an
unknown producer route are three distinct nonzero findings. It reads nothing
out of the episode — a checker that took its expected answer from the artifact
it is checking would agree with it by construction.

### Schema v2

`artifacts/ontology/agent-episode-v2.schema.json`, beside v1, adds:

- `selection.ledger_sha256` — v1 could only smuggle it into the free-text
  `eligibility_reason`, and a digest a machine cannot read is a digest nobody
  re-derives;
- `outcome.checker_runs[]{command, exit_status, output_sha256, assurance}` —
  an A4 episode has more than one checker and v1's singular field collapsed
  them;
- `outcome.decline_class` as an **enum**: the nine AG4.1 classes from
  [`docs/autogenesis/02-phased-roadmap.md`](../autogenesis/02-phased-roadmap.md)
  (`unsupported-semantics`, `missing-lemma`, `missing-plan-rule`,
  `missing-certificate`, `representation-explosion`, `resource-exhaustion`,
  `retrieval-miss`, `formalization-mismatch`, `operational-failure`), plus five
  loop-local classes kept deliberately separate (`no-general-route`,
  `gate-refused`, `supervisor-denied`, `budget-exhausted-before-plan`,
  `budget-exhausted-during-plan`). `no-general-route` is a *result*; folding it
  into `missing-plan-rule` would record a mathematical obstruction nobody
  observed and poison the measurement A5 is built from.

v2 **keeps** v1's singular `checker_command` / `checker_exit_status` and
requires them, so every v1 rule still bites on a v2 document. A new schema
version that quietly turned rules off would be the worst way to add one, and
`test_a_v2_document_still_fails_the_v1_ledger_write_rule` (and two siblings)
exist for exactly that.

**Rule 11, `proved-requires-checked-call`**: `verdict == "proved"` requires at
least one `tool_calls[].assurance == "checked"` **and** at least one
`checker_runs[]` with `exit_status == 0`. Both halves are required and neither
implies the other — a `checked` call with no passing checker is a producer
nobody re-validated; a passing checker with no `checked` call is a checker that
ran against nothing this episode did. Enforced twice, in two codebases that
never import each other: at write time in `axeyum.agent.episode`, and in the
stdlib-only gate.

### Held-out isolation now covers the episode tree

`check-autogenesis-holdout-isolation.py` walks `artifacts/episodes/**`, both
`*.json` and `*.json.snapshot`, with `frontier.json.snapshot` exempted **by
name** as a population census (it is `fact-frontier.py --json`, which `--verify`
re-derives entry for entry, so it necessarily names all 57 held-out ids exactly
as `nursery-v1.json` does). Ten episodes were committed on 2026-08-24 while
that tree was unscanned and their cleanliness was measured by hand.

It gained a second guard at the same time: the exact-value walk is right for a
structured artifact, but an episode transcript is **prose**, and a model
writing "I will work on F:…" puts the id inside a value that is not equal to
it. The first version of the episode scan passed such a transcript. Both guards
are mutation-verified with disjoint killed-sets.

### Run it

```sh
export ANTHROPIC_API_KEY=...
uv run python -m axeyum.agent run --fact F:ml430-nat-modeq-refl-d870c8f5 \
  --model anthropic:claude-sonnet-4-5 \
  --budget-usd 1.00 --request-limit 10 --tool-calls-limit 16 \
  --out artifacts/episodes/$(date +%F)-a4 --git-commit <40-hex>

# offline: no provider, no /nas3 needed for a fact with no export
uv run python -m axeyum.agent run --fact F:... --offline --out /tmp/scratch
```

Offline, the `Dispatch` node uses a `FunctionModel` rather than `TestModel`:
`TestModel` invents arguments from the JSON schema, so `fact_id` comes back as
`"a"` and the supervisor correctly denies the call for targeting the wrong
fact. That is a real outcome and a useless demonstration. The approval gate in
front of it is untouched — even a model that asks perfectly cannot run the tool.

### What the ledger-writing step still needs

`StageTransaction` runs `prepare-autogenesis-fact-transaction.py`, the
**read-only** proposal writer, and records its exit status whatever it is.
Measured 2026-08-24 it exits **1** for every A4 target:

```
AUTOGENESIS_FACT_TRANSACTION_ERROR|choose exactly one input mode: --bundle, or --frontier plus --execution
```

That is the useful finding, not a harness bug. A transaction proposal is
derivable only from a *registered authoritative operation* plus an execution
receipt, and no registered operation covers the `Nat.ModEq` family — that is
precisely what
[`250-natural-modeq-capability-selection.md`](../autogenesis/250-natural-modeq-capability-selection.md)
stops short of. So the sequence a human has to authorize is: register an
authoritative operation for the family (with source-bound statement adapters
and independently checked receipts, per that document's construction
constraints), run `execute-autogenesis-operation.py`, then
`prepare-autogenesis-fact-transaction.py --frontier … --execution …`, and only
then `apply-autogenesis-fact-transaction.py`. The episode is evidence for the
first step and has no authority over any of them.

## A2 measurements worth carrying forward

- **98** eligible facts across 9 nursery families; `fact-frontier.py`'s own
  selection still returns `refused-no-admissible-candidate`, which is the
  baseline this loop exists to move.
- Ten live episodes: **8 declined, 2 budget-exhausted; 8 of 8 completed plans
  were `NoGeneralRoute` and zero were `StrategyProposal`.** With the
  three-sibling rule in force, Sonnet 4.5 never claimed a general route over
  this catalog. Whether that is the catalog's reach or the rule's severity is
  an open question and A7's census is what answers it.
- All ten replay with `selection` and `outcome` re-derived and tool-call
  digests matching.

## A4 measurements (2026-08-24, live)

Six eligible facts on `anthropic:claude-sonnet-4-5` with
`UsageLimits(cost_limit=1.00, request_limit=10, tool_calls_limit=16)`:
**$1.551 total, mean $0.259**. Two `proved`, four `declined` — three
`gate-refused` (the model emitted `NoGeneralRoute`) and one `retrieval-miss`
(the model proposed a general route, the gate passed, the supervisor approved,
and the *tool* reported that no frozen export exists for that fact).

| fact | verdict | decline_class | proof_sha256 |
|---|---|---|---|
| `F:ml430-nat-modeq-refl-d870c8f5` | proved | — | `1c0507f1…` |
| `F:ml430-nat-modeq-symm-0a3d4d18` | proved | — | `c3c8334e…` |
| `F:ml430-nat-modeq-trans-ef9d1c46` | declined | gate-refused | — |
| `F:ml430-nat-modeq-one-516d46e8` | declined | retrieval-miss | — |
| `F:ml430-nat-add-modeq-left-e3b1fba9` | declined | gate-refused | — |
| `F:ml430-int-modeq-neg-f649f6c5` | declined | gate-refused | — |

Both proofs are axiom-free and dependency-free, re-derived in a second kernel,
and **neither digest appears in any committed manifest**: these are results the
ledger does not have, not reproductions of ones it does.

### The retrieval blindness A2's baseline was partly measuring

A2 reported 8 of 8 completed plans as `NoGeneralRoute` and called that the
baseline A4 must move. Part of it was not about mathematics. `frontier_select`
capped a page at **60 rows against 98 eligible facts**, and the generality rule
asks the model to name three other eligible facts *from ids the tools showed
you*. A fact whose siblings sat outside the first page could not satisfy that
rule whatever was true of the goal.

Measured directly. The first live A4 episode on `Nat.ModEq` reflexivity emitted
`NoGeneralRoute`, and its `obstruction` named only the two ModEq facts its page
happened to contain — with symmetry and transitivity eligible, unseen, and
provable by the same producer in milliseconds. `MAX_ROWS` is now 120 and the
default page is the whole eligible population; the same fact, same model, same
prompt, came back `general` and closed. That is a retrieval failure that was
being recorded as a mathematical obstruction, which is the one thing the
obstruction graph must not be poisoned by.

The remaining three `NoGeneralRoute`s are not that: each names siblings the
model saw and judged structurally different, which is the datapoint A5 wants.
One of them is nonetheless a **measured false negative**. All three exportable
eligible facts -- `Nat.ModEq` refl, symm and trans -- close axiom-free in
milliseconds; the model routed two and declined transitivity after seeing the
whole eligible page. The three-sibling rule filters on the model's confidence
that a route generalizes, not on whether it does, and the gap between the two
is 1 in 3 here.

### Replay

All six replay with `selection` and `outcome` re-derived, model requests
disabled, and every recorded response consumed. Two report
`tool_calls=differ`, which does not gate the exit status and is expected here
for a specific reason: a tier-C result carries its own `duration_ms`, so the
digest of the tool return legitimately moves between a run and its replay. The
`outcome` block -- including `checker_runs[0].output_sha256`, which the replay
re-derives by building a second kernel again rather than reading it out of the
file -- is byte-identical.

### Reach, measured

Of the 98 eligible facts, **3** resolve to a frozen, proof-free statement
export (`tools.resolve_export`); the other 95 have none, so no producer in this
loop can attack them at all. `retrieval-miss` is therefore the dominant real
obstruction on this frontier, and it is a finding about the Lean export
pipeline on s5, not about the producers.
