# 06 — The obstruction graph: typed declines become a scheduling input

Status: landed, 2026-08-24. Slice A5 of
[`03-agentic-layer.md`](03-agentic-layer.md); Autogenesis **F3** in
[`docs/autogenesis/243-knowledge-overlay-and-fill-plan.md`](../autogenesis/243-knowledge-overlay-and-fill-plan.md).

## What landed

| Artifact | Role |
|---|---|
| [`artifacts/ontology/obstruction-graph.schema.json`](../../artifacts/ontology/obstruction-graph.schema.json) | the contract: `O:` entities, `blocked-by` links, an assurance ceiling of `mechanically-observed` |
| [`scripts/gen-obstruction-graph.py`](../../scripts/gen-obstruction-graph.py) | derives `artifacts/autogenesis/obstruction-graph-v1.json`; `--check` fails on a stale artifact |
| [`scripts/validate-obstruction-graph.py`](../../scripts/validate-obstruction-graph.py) | the independent re-validator |
| [`scripts/gen-obstruction-dashboard.py`](../../scripts/gen-obstruction-dashboard.py) | renders [`docs/plan/generated/obstruction-graph.md`](../plan/generated/obstruction-graph.md) |
| [`python/axeyum/agent/classify.py`](../../python/axeyum/agent/classify.py) | the in-graph `Classify` node's mapping |
| [`scripts/tests/test_obstruction_graph.py`](../../scripts/tests/test_obstruction_graph.py) | 36 controls; 26 mutation anchors, each killing exactly one |

Gate: `just obstruction-graph`, and four steps appended to `scripts/check.sh`.

## The two evidence populations, and why they stay distinguishable

* **16 committed agent episodes** under `artifacts/episodes/<date>[-<slice>]/`
  (A2 and A4). Their declines are *typed values*: a discriminated
  `NoGeneralRoute` proposal variant and a v2 `decline_class` enum.
* **11 committed producer decline records** `artifacts/autogenesis/*-decline-v*.json`.
  These predate the loop, carry no episode fields, and have eleven different
  shapes.

`artifacts/episodes/fixtures*/` is deliberately not read: those are
`check-agent-episode.py`'s own control inputs, some of them intentionally
corrupt, and counting an invented decline in a measured census would be the
whole defect this file exists to avoid.

Each blocker records which typed field produced it (`episode-proposal-route`,
`episode-decline-class`, `decline-record-observation`), because a blocker
derived from a producer's own Rust `DeclineReason` variant is a different
quality of evidence from one derived from a proposal the model wrote, and that
distinction is not recoverable from the blocker's kind.

## The finding that shaped the design

**`no-general-route` and `gate-refused` are the same obstruction under two
harnesses.** A2 recorded `no-general-route` when the model declined to claim
three siblings. A4 added a deterministic gate that *refuses* a `NoGeneralRoute`
plan, so the identical situation now records `gate-refused`. A classifier keyed
on `decline_class` alone would split one cluster in two and attribute the split
to the mathematics rather than to a change in our own graph.

So the **first blocker** is read from the earlier observation — the proposal
variant — and the decline class joins the **complete known blocker set**. F3
asks for those two separately; this is why.

## Why `Classify` is deterministic when plan 03 drew it in italics

Plan 03's node list italicizes *Classify* alongside *Gather* and *Plan*, and in
that list italic means "a model runs here". It does not, for three reasons, all
recorded in [`classify.py`](../../python/axeyum/agent/classify.py):

1. **The inputs are already typed.** There is no free text left to read: the
   proposal is a discriminated variant, the decline class is a pinned enum, and
   a `ProducerDeclined.reason_kind` is the producer's own Rust enum variant
   carried across the boundary unflattened.
2. **A model call would put the cluster keys outside the replay guarantee.**
   `replay --from-transcript` requires every deterministic node to re-derive
   bit-identically and treats divergence as a finding.
3. **The same mapping has to run outside the package.** `just check` is
   standard-library only and nothing under `scripts/` may import the `[agent]`
   extra, so the generator re-derives identical clusters from committed bytes.
   `python/tests/test_agent_classify.py` holds the two implementations to
   agreement on every committed episode, so the duplication cannot drift.

`Classify` sits on the **post-plan** decline path: `Gate`, `Dispatch`,
`Supervise` and `Check` all reach `WriteEpisode` through it. `Gather` and `Plan`
still exit straight to `WriteEpisode` when a run is cut short before it has a
plan — there is no typed proposal to read, and routing the v1 path through a
node the ten A2 episodes never ran would change what a v1 replay re-derives.

**No episode field was added.** A classification is a function of
`outcome.decline_class` and the committed `proposals[]`, both already in schema
v2. That was a constraint, not a coincidence: a taxonomy needing a new column
would be a taxonomy the sixteen committed episodes could not be scored against.

## Guards, and why each can fail

The generator exits 1 when: no obstruction was derived; a decline record's shape
matches **no** predicate (a new shape must be classified, never dropped — the
checker-that-cannot-fail defect one arrow upstream); an episode selects a
held-out fact; or any held-out id reaches the rendered bytes.

The validator recomputes rather than reads: every `O:` id is re-derived as
sha256 of its own `cluster_key`, every `evidence[].sha256` is re-hashed from
disk, and every `candidate_capability.exists` is re-measured against the
knowledge overlay. Held-out ids are refused twice more, structurally and as a
substring walk over every string in the document — the walk is the only guard
that sees a held-out id copied verbatim out of a decline record's free-text
diagnostic into a blocker `detail`, which is a path no field-specific check can
see.

The validator's local rules run **even when the JSON Schema check has already
complained**. `jsonschema` is installed on some hosts and not others; a rule
that only executes where the library is absent is a rule nobody measures, and
its mutation control would report `SURVIVED` on a developer box and `killed` in
CI.

The nine preregistered `must-decline-mutations-v1.json` rows are removed from
every population before it is counted: a producer declining a **false**
statement is the trusted layer working, not an obstruction.

## Relationship to `obstruction-projection-v1.json`

Another lane's
[`obstruction-projection-v1.json`](../../artifacts/autogenesis/obstruction-projection-v1.json)
normalizes the top-level `decline` object found in 47 `*-result-v*.json`
records. It is a **disjoint** evidence population — measured 2026-08-24, zero
files appear in both censuses — and it reads no agent episode. It also carries
no fact population, no partition counts, no first-versus-known blocker split, no
funnel and no `blocked-by` links, which is the shape F3 asks for and the reason
this graph exists beside it rather than instead of it. Joining the two is real
F3 work and is **not** done.

## What this is not

An obstruction is evidence that a route did not close a goal. It is never
evidence that the goal is false, and never evidence that the named capability
would in fact close it. The assurance enum tops out at `mechanically-observed`
and the schema cannot express `independently-checked`, `registry-derived`,
`formal-derived` or `human-reviewed` at all. Nothing here admits a fact, relaxes
a checker, or changes an axiom footprint.
