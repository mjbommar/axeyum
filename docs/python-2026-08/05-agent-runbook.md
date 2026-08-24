# 05 — Agent runbook: running, replaying, and reading an episode

Slice A2 of [`03-agentic-layer.md`](03-agentic-layer.md). Measured 2026-08-24
against commit `5e289fe8cfccab7ba6b230a73cacedf6a485a187`.

**This loop dispatches nothing.** There is no C-tier tool in it, so it is not
merely unauthorized to admit a theorem — it has no tool that could. What it
produces is an *episode*: a record of what a model was allowed to look at, what
it proposed, and what a trusted checker says about that record. Admission stays
where it was ([`docs/autogenesis/05-trust-safety-and-governance.md`](../autogenesis/05-trust-safety-and-governance.md)).

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
