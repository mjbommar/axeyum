# Agent episodes

An **episode** is the record of one run of the agentic frontier loop
(`docs/python-2026-08/03-agentic-layer.md`): what it was allowed to look at,
which model and prompts it ran with, every tool call it made, whatever it
proposed, and what a trusted checker said about the result.

Schema: [`../ontology/agent-episode.schema.json`](../ontology/agent-episode.schema.json).
Checker: [`../../scripts/check-agent-episode.py`](../../scripts/check-agent-episode.py).

## An episode carries no authority

This is the whole point of the artifact, so it is worth stating flatly. An
episode is **evidence about a run**, never evidence about mathematics. Three
mechanisms hold that line, and they are independent of each other:

- `outcome.ledger_writes` is pinned to `0` twice — once by the schema
  (`minimum: 0, maximum: 0`) and once by a named checker rule whose deletion
  kills a test. The only writer to `artifacts/facts/` is
  `apply-autogenesis-fact-transaction.py`, and an episode is not it.
- `proposals[].assurance` is `const: "proposed"`. A P-tier tool cannot emit a
  value that reads as checked.
- `selection.partition` admits `train` and `development` **only**. Held-out is
  not expressible, and a separate rule string-walks the entire document for any
  held-out fact id — computed by importing `held_out_facts` from
  `check-autogenesis-holdout-isolation.py`, so the two gates cannot drift about
  what "held out" means. One held-out row cost 19 of 76 blind propositions on
  2026-08-21; the population is a shared resource with no owner.

`outcome.verdict == "proved"` therefore means "a trusted checker this episode
shelled out to exited 0", not "a fact moved". Moving a fact is a separate,
trusted step (plan 03, slice A4) that reads an episode and does not trust it.

## How to check one

```sh
python3 scripts/check-agent-episode.py artifacts/episodes
python3 scripts/check-agent-episode.py artifacts/episodes --production-only
python3 scripts/check-agent-episode.py artifacts/episodes --require-ancestor
python3 -m unittest scripts.tests.test_check_agent_episode
```

The last line of the output is `EPISODES|checked=N|ok=K|failed=M`, and the exit
status is nonzero when `M > 0` **and when `N == 0`** — a check that checked
nothing is not a pass. Read the count, not the exit status.

The aggregate repository gate uses `--production-only`. It excludes directories
whose names start with `fixtures`, reports the excluded count, and fails if no
real episodes remain. Fixtures exercise the checker; they are never evidence
that the autonomous loop ran.

## Why `--require-ancestor` is opt-in

Plan 03 says `git_commit` must be an ancestor of `HEAD`, and in a full checkout
it is. It is not decidable anywhere else: a CI clone at `fetch-depth: 1` has one
commit and answers "no" to every ancestor query, a `git archive` lane snapshot
has no `.git` at all, and a release tarball has no history. A rule that goes red
in those environments gets switched off, which is strictly worse than a rule
that has to be asked for — so the default prints a `EPISODE_WARN` naming the
same rule, and gates that run in a full checkout pass `--require-ancestor` to
get the hard failure. Within the opt-in the rule is fail-closed: ancestry that
cannot be *determined* is a failure, not a pass.

## The fixtures are illustrative, not evidence

[`fixtures/episode-declined-v1.json`](fixtures/episode-declined-v1.json) and
[`fixtures/episode-proved-v1.json`](fixtures/episode-proved-v1.json) are
hand-authored. They exist to give the checker something to be green on and to
give `scripts/tests/test_check_agent_episode.py` a good document to corrupt one
field at a time. Read them as a worked example of the format:

- No model ran. `policy.model_id` is `anthropic:claude-illustrative-fixture`,
  which is not a model id that resolves anywhere, and the prompt/toolset digests
  are hashes of fixed strings rather than of real prompts.
- Neither fixture claims a fact transition. `observed.facts_unlocked` is empty in
  both, `ledger_writes` is 0 in both, and both name facts that are **open** in
  the ledger. `episode-proved-v1.json` records a checker exiting 0 on a plan
  bundle; it does not record `F:ml430-nat-add-modeq-left-e3b1fba9` becoming
  proved, and nothing in this directory could make that true.
- Both draw from `train` / `development` rows of
  `../autogenesis/nursery-v1.json`. Neither touches a held-out row.
- `selection.frontier_path` and `transcript.messages_path` point at files that
  are **deliberately not committed**, so every run prints
  `EPISODE_WARN|...|rule=frontier-digest`. A real frontier is derived from the
  live fact ledger, so a committed copy would go stale the next time any lane
  adds a fact and would turn this gate red for a reason that has nothing to do
  with episodes. The warn is the honest report: that input was not re-derived.
  Real episodes (slice A2 onward) commit their frontier and their transcript
  beside themselves, and the digest rules then bite.

Because they carry no verdict about the world, corrupting a copy of them in a
temporary directory is the cheapest way to prove each checker rule can fail —
which is what the unittest suite and the `agent-episode` entry in
`../../scripts/tests/mutation_controls.py` do.
