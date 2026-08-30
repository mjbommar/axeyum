# ADR-0885: The L2 phase G5 graph dispatcher composes three read-only layers and is authoritative only where ADR-0865 tested it

Status: accepted
Date: 2026-08-30
Index-summary: L2 phase G5 makes graph selection the ordinary dispatcher by
composing three layers -- curriculum (destination), infrastructure frontier
(capability, ADR-0845), fact-frontier.py via check-dispatchable-frontier.py
(legal target) -- without editing any of them. Authority is scoped to
exactly the (population, queue) pair ADR-0865 measured; a held-out fact can
never be proposed (proven by refusing an override attempt by name); an
override requires an evidence note and is refused without one, leaving a
record in an append-only ledger.

## Context

`docs/plan/graph-directed-library-roadmap-2026-08-30.md` phase G5 asks for
graph selection to become "the ordinary dispatcher": "The curriculum
chooses the destination, the infrastructure frontier chooses the
capability, and `fact-frontier.py` chooses the specific legal target inside
that cluster. A lane can override the ordering only with an evidence note."

ADR-0865 (L2 phase G4) is the evidence this phase must not outrun. It ran
TWO pilots, not three -- the third category (a destination bridge toward
linear algebra, polynomials, or analysis) had zero candidates in the only
joined population and was declared not-yet-evaluable rather than
manufactured. Both run pilots moved their preregistered metric with zero
added trust surface, over exactly one population
(`mathlib-group-defs-v1`), restricted to two queues
(`language-infrastructure`, `proof-producers`). `docs/plan/global/
50-planning-rules.md` independently states that graph rank is advisory
until its authority is complete. A dispatcher that promotes the ranking
beyond what was tested is worse than none, because lanes follow it.

Three artifacts already exist as read-only inputs and are explicitly out of
this phase's edit scope:

- `docs/curriculum/curriculum.toml` -- the curriculum graph (destinations).
- `artifacts/infrastructure-frontier/*.frontier.json` -- the infrastructure
  frontier (ADR-0845; capabilities, one hand-curated row per proposed
  increment, each with a stable content-hash `row_id`).
- `scripts/check-dispatchable-frontier.py` -- the legal-target computation:
  open `ml430` mirrors classified into held-out (blind evaluation
  population, ADR-0542), mutation negative controls, structurally blocked,
  and dispatchable.

## Decision

**Compose, never reimplement.** `scripts/lib/graph_dispatcher.py` reads
`curriculum.toml` and every `*.frontier.json` directly, and invokes
`check-dispatchable-frontier.py --json` as a subprocess for the legal-target
layer -- it never re-derives held-out/mutation/blocked classification, and
never writes to any of the three inputs.

**Three functions, one per layer, each raising on absence rather than
returning a placeholder:**

1. `select_destination(nodes, frontier_docs)` ranks curriculum nodes by how
   many published infrastructure-frontier rows name the node's doc path in
   `destination_paths`. This is the only checkable signal available today:
   every curriculum node is currently `covered` or `lean-horizon` (no
   `planned` rows exist), so ranking by curriculum status alone would
   fabricate priority the data does not support. Raises `DispatcherError`
   if no destination has any supporting row.
2. `select_capability(destination, frontier_docs)` picks the top row for
   that destination across every published population, ordered by the
   roadmap's own priority tiers (`language-infrastructure` >
   `proof-producers` > `theorem-dominators` > `dependency-ready-leaves`),
   tie-broken by `row_id`. Raises if the destination has zero rows.
3. `match_legal_target(capability_row, dispatchable_ids)` is handed ONLY
   the `dispatchable` list `check-dispatchable-frontier.py --json` computed
   -- never held-out, mutation, or blocked. A "linked" match requires an
   EXACT (case-insensitive) match between one of the capability row's
   `subject_declarations` and one dot-separated component of a dispatchable
   fact's own Mathlib identifier (extracted from its title's `"...
   proposition X.Y.Z"` suffix) -- deliberately NOT a fuzzy token-overlap
   heuristic, which would spuriously match on shared stopword-shaped
   fragments (a probe during development confirmed `"left"` inside
   `and_or_distrib_left` would otherwise wrongly link to
   `mul_left_cancel`/`IsLeftCancelMul`). Absent a link, it falls back to
   the lexicographically smallest dispatchable id -- the same "best
   local-ready alternative" pattern ADR-0865's own pilots used when graph
   selection had nothing to offer, always labeled advisory.

**Authority is a function of measured scope, not of confidence.**
`authority_level` (folded into `select_capability` and
`legal_target_authority`) returns `"authoritative"` only for
`population_id == "mathlib-group-defs-v1"` and
`queue in {"language-infrastructure", "proof-producers"}` -- literally
ADR-0865's tested scope -- and `"advisory"` everywhere else, including a
"linked" legal target whose capability is out of scope, and INCLUDING every
"fallback" legal target regardless of the capability's own scope, because a
fallback pick was not actually selected by the capability at all.

**A held-out fact cannot be proposed, structurally and provably.**
`select_legal_target`/`match_legal_target` are typed to receive only the
`dispatchable` list; `check-graph-dispatcher.py`'s `HELD_OUT_NEVER_PROPOSED`
guard independently re-checks the committed recommendation and every
override-ledger entry against a freshly computed held-out/mutation/blocked
set. And the override path was tested directly: attempting
`--override-legal-target` against a real held-out fact id is REFUSED BY
NAME (`"'F:...' is held-out (blind evaluation population, ADR-0542) and
cannot be dispatched, override or not."`), exit 1, with no write to
`overrides.jsonl`.

**An override requires an evidence note, checked at the point of use, not
only audited after.** `scripts/gen-graph-dispatcher.py
--override-legal-target FACT_ID --evidence-note-file PATH` refuses (no
ledger write) if: the fact is held-out/mutation/blocked; the fact is not
in the current dispatchable set; the note file is missing; the note is
under 20 characters; or the note does not name the fact it overrides. On
success it appends one record to `artifacts/graph-dispatcher/
overrides.jsonl` (append-only) carrying the lane (from `AXEYUM_AGENT`), the
default pick that was overridden, and the note verbatim.
`OVERRIDE_LEDGER_COMPLETE` independently re-validates every ledger entry so
a hand-edited entry bypassing the CLI is still caught.

**Two artifact halves get different staleness treatment, on purpose.** The
`destination`/`capability` sections of `recommendation.json` are derived
from frozen inputs (curriculum.toml, infrastructure-frontier snapshots) and
are checked byte-for-byte against a fresh recomputation
(`STALE_DESTINATION_CAPABILITY`). The `legal_target` section is derived
from the mutable fact ledger via `check-dispatchable-frontier.py`, which
changes every time a fact is proved; requiring historical byte-equality
there would fail the gate on ordinary flywheel progress. It is instead
checked STRUCTURALLY (never held-out, row citation valid, authority
correctly scoped) against a fresh run.

**Ten guards, each mutation-verified to be killed by exactly one fixture**
(`scripts/check-graph-dispatcher.py`, kill table in
`scripts/tests/test-graph-dispatcher-mutations.sh`, every guard printed IN
the final table, not merely exercised beside it):

| Guard | What it catches |
|---|---|
| `MISSING_INPUTS` | curriculum.toml or every infrastructure-frontier document is absent/unreadable |
| `NO_DESTINATION` | layer 1 produced no destination |
| `NO_CAPABILITY` | layer 2 produced no capability for that destination |
| `UPSTREAM_GUARD_PROPAGATION` | check-dispatchable-frontier.py itself failed and the composition did not refuse to build on top of it |
| `LEGAL_TARGET_PRESENT` | the dispatchable set was empty but a legal_target was still produced |
| `HELD_OUT_NEVER_PROPOSED` | the recommendation's legal_target, or an override-ledger entry, is held-out/mutation/blocked |
| `AUTHORITY_SCOPE` | "authoritative" appears outside ADR-0865's tested (population, queue) pair, or a fallback legal target is labeled authoritative |
| `ROW_CITATION_VALID` | the cited capability row_id/title/subject_declarations do not match the real frontier artifact |
| `OVERRIDE_LEDGER_COMPLETE` | an override-ledger entry has an empty/short note, a note not naming its target, or no identified lane |
| `ADR_CITATION_PRESENT` | a cited ADR path is missing from the tree, or ADR-0865 is missing from the citation list |

## Evidence

Worked example on the tree at commit time: destination `groups`
(`docs/curriculum/02-structures/groups.md`, 3 supporting rows across 1
servable destination); capability `IF-LANG-4f071ea9a3` (bundled
commutative-magma structure / generic `mul_comm`, population
`mathlib-group-defs-v1`, queue `language-infrastructure`, **authoritative**);
legal target `F:ml430-nat-and-div-two-1a2f7c33` (**fallback, advisory** --
the two populations are largely disjoint, confirming ADR-0845's own
cross-check finding that no direct link exists between them today).

Two consecutive runs of `scripts/gen-graph-dispatcher.py` produce a
byte-identical `recommendation.json`/`dashboard.md` (verified). All ten
guards each kill exactly their own fixture when deleted in a scratch copy
(verified, `scripts/tests/test-graph-dispatcher-mutations.sh`). The held-out
refusal and the four override-rejection paths (missing note file, note too
short, note not naming the target, target not dispatchable) were each
exercised against the real committed data
(`scripts/tests/test-graph-dispatcher.py`) without writing to the real
`overrides.jsonl`.

## What this does not capture

The composition is authoritative for exactly the slice ADR-0865 measured.
Every curriculum destination other than `groups` currently has zero
supporting infrastructure-frontier rows and is invisible to layer 1's
selection (reported as an unserved candidate, never silently dropped). No
published frontier row currently links to any dispatchable `ml430` mirror
by identifier, so every legal target this dispatcher currently proposes is
the advisory fallback, not a graph-authoritative pick -- this is an honest
description of the current data, not a defect in the matcher (a synthetic
fixture in `scripts/tests/test-graph-dispatcher.py` confirms linking works
when an identifier genuinely matches). Category 3 (a destination-bridge
population) remains untested; nothing in this dispatcher claims otherwise.

## Alternatives

**Rank legal targets by fuzzy token overlap against the capability's
subject.** Rejected during development: a probe showed this spuriously
links `IsLeftCancelMul`/`mul_left_cancel` to `and_or_distrib_left` on the
shared token `"left"` -- exactly the bare-name-similarity-as-identity trap
ADR-0835/ADR-0845 already refuse elsewhere in this pipeline. Replaced with
an exact, whole-component identifier match.

**Rank curriculum destinations by `status` (`planned` first).** Rejected:
zero curriculum nodes currently carry `status = "planned"`; this would
either select nothing or require inventing a synthetic prioritization the
committed data does not support.

**Treat a capability row from ANY population/queue as authoritative once a
legal target links to it.** Rejected: this would launder an out-of-scope
capability into an authoritative recommendation via a coincidental
identifier match. `legal_target_authority` explicitly requires BOTH a
genuine link AND the capability itself being in ADR-0865's tested scope.

**Skip the override mechanism's live refusal and only audit after the
fact.** Rejected: an override nobody can safely attempt is an override
nobody will use, and an audit-only design still lets a held-out fact get
proposed before anyone notices. Refusing synchronously, by name, at the
point of the attempt, is strictly stronger and was verified directly.

## Consequences

A lane citing this dispatcher's `recommendation.json` gets, in one place: a
destination with its curriculum path, a capability with its frozen
`row_id` and preregistered metric (description, command, baseline,
expected_change), and a legal target -- each carrying its own authority
label and reason, so a lane cannot mistake an advisory fallback for a
graph-authoritative pick. Extending authority to a new population or queue
requires a new ADR measuring it, mirroring ADR-0865's own method, not an
edit to `PILOTED_POPULATION`/`PILOTED_QUEUES` alone.
