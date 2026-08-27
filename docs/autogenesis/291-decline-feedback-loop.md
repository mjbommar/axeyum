# 291 — Declines become selector input: the contract-decline convention

Date: 2026-08-27
Lane: decline-feedback

## The gap this closes

Doc 290 ran the first contract-driven dispatch end to end:
`producer-contract-int-modeq-family-v1` matched
`F:ml430-int-add-modeq-left-ee732b5b`, the s5 export and import were clean,
and the producer honestly declined (`DeclineReason::TerminalNotClosed`). The
decline is recorded, correctly, as
`artifacts/autogenesis/mathlib-int-add-modeq-left-decline-v1.json`.

Verified on the merged tree before this task touched anything:

```
$ python3 scripts/fact-frontier.py --json | python3 -c "...
selected_fact_id: F:ml430-int-add-modeq-left-ee732b5b
admissible_count: 27
admissible_via_contract_count: 27
```

`fact-frontier.py` still selects the exact fact that was just declined. It
has no way to read the decline artifact at all: `admissible` is computed from
shape-match + route-capability only, so a shape match that will always be
declined counts identically to one that would succeed. Without feedback the
selector loops on this fact forever, and `admissible_count` measures "shape
matched a contract", not "a producer would actually attempt this and might
succeed" -- despite the name.

This doc formalizes the convention that closes the loop, and
`scripts/fact-frontier.py` / `scripts/validate-producer-contract-declines.py`
implement it.

## Survey: what decline artifacts already look like

`artifacts/autogenesis/*decline*.json` currently holds twelve files. Eleven
predate ADR-0602 and record an *implementation-stage* decline (a driver that
fails clippy, a construction that doesn't typecheck yet) -- each has its own
ad hoc shape, no two alike, and none of them name a `contract` or a `fact_id`
at the top level.

Exactly one, `mathlib-int-add-modeq-left-decline-v1.json`, is the new shape:
a **contract-driven decline**, produced by running a producer against a fact
a contract matched. It already carries the fields that matter:

```json
{
  "contract": "artifacts/autogenesis/producer-contracts/int-modeq-family-v1.json",
  "fact_id": "F:ml430-int-add-modeq-left-ee732b5b",
  "producer": {
    "tool": "crates/axeyum-lean-import/examples/modeq_family_operation.rs",
    "result": "declined",
    "decline_reason": "TerminalNotClosed",
    "decline_message": "terminal goal is not an Eq/Iff shape ..."
  }
}
```

That is the convention this doc extends, not a new one invented from
scratch. **A contract-driven decline artifact is any JSON object under
`artifacts/autogenesis/` carrying top-level `contract` and `fact_id` keys
together with `producer.result == "declined"`.** That three-field shape is
exactly what the seed instance has and exactly what distinguishes it,
structurally, from all eleven older decline files (none of which have a
top-level `contract` key at all) -- so the selector can tell the two families
apart without a naming convention or a directory move, and every existing
file keeps working unmodified.

## What the convention adds

One field existed informally (`producer.decline_reason` as a bare identifier)
and one is new:

1. **`contract_sha256` (new, required on every contract-driven decline).**
   The sha256 of the referenced contract's full canonical JSON
   (`hashlib.sha256(json.dumps(contract, sort_keys=True,
   separators=(",",":")).encode()).hexdigest()` -- the exact `digest()`
   already used by `validate-producer-contracts.py` and `fact-frontier.py`),
   captured at the moment the decline was recorded. This is the
   **re-dispatch key** (item 4 below): a decline binds to one exact version
   of the contract's recipe/shape, never to the contract's *name*.

2. **`producer.decline_reason` must be a bare typed identifier, never free
   text.** Pattern: `^[A-Z][A-Za-z0-9]*$` -- exactly the shape of a Rust enum
   variant name (`TerminalNotClosed`, `BinderBudgetExceeded`,
   `UnsupportedRecursorShape`, `RequiredDeclarationUnavailable`, ...; see
   `crates/axeyum-lean-import/src/producers/modeq_family.rs`'s own
   `DeclineReason`). This was already true of the seed instance by
   convention; it is now a validated requirement, because the failure mode
   this whole feature must not open is *make a fact disappear from the queue
   by writing "we tried, no dice" in a `reason` string nothing checks*. A
   free-text reason cannot be told apart from that. Prose detail keeps living
   in `producer.decline_message` (required, non-empty, unconstrained) -- nothing
   forces the message to be terse, only the reason to be typed.

3. **`producer.tool` and `producer.result` are required, unchanged in
   meaning.** `result` must be exactly `"declined"` (this is what lets the
   frontier and the validator both recognize the record as a decline rather
   than, say, a future contract-driven *success* artifact sharing the same
   `contract`/`fact_id` header). `tool` names the exact producer module, so a
   decline's provenance is checkable against real source rather than merely
   asserted -- mirroring the identity requirement CLAUDE.md's trap #3 (the
   `nra_monomial_bound_cert` case) draws out: a checker can only re-derive a
   distinction the artifact actually recorded.

4. **`fact_id` and `contract` must resolve.** `fact_id` must name a real fact
   in `artifacts/facts/`; `contract` must be a path, relative to the
   repository root, to a file that exists under
   `artifacts/autogenesis/producer-contracts/` and parses as a contract with
   an `id`. A decline naming nothing real proves nothing, exactly the
   falsifiability discipline `validate-producer-contracts.py` already applies
   to a contract's own `non_examples`.

Nothing above requires touching the eleven older decline files: they have no
`contract` key, so neither the new validator nor the frontier's decline
reader ever looks at them.

## Re-dispatch: a decline is contract-version-scoped

`fact-frontier.py` computes, for every decline artifact, whether it is
**live**: `contract_sha256 == digest(the referenced contract's CURRENT
on-disk content)`. A decline is live only against the exact contract version
that produced it.

- **Live** declines suppress admission of that `(fact, contract)` pair.
- **Stale** declines (the contract's sha has changed -- its recipe, its
  shape predicate, its route) do **not** suppress anything. The fact is
  automatically eligible again the moment the contract that declined it is
  edited, with no manual list to clear and no `expires` date to maintain.

This is the mechanism ADR-0602's own framing implies but never wired up:
"the shape is dischargeable via `kernel-lane`" is a claim about the
*contract*, and improving the producer the contract's `recipe.reference`
points at is exactly the event that should re-open every fact that contract
previously declined. Bumping `producer-contract-int-modeq-family-v1`'s
`schema_version` or editing its `shape`/`recipe` (a real behavior change --
touching `notes` alone would be a false re-open, so contract authors should
prefer a genuine `-v2` file when only prose changes, matching the existing
`-v1`/`-v2` decline-artifact convention already used elsewhere in this
directory) changes its digest and re-opens `F:ml430-int-add-modeq-left-ee732b5b`
for reattempt without anyone touching the decline artifact.

## Three populations, not two

`fact-frontier.py --json`'s `diagnostics` now distinguishes:

- **`shape_matched_count`** -- ready facts with at least one matched producer
  contract (unchanged meaning; this is what `matched_producer_contract_ids`
  already counted).
- **`declined_count`** -- ready facts where *every* matched contract has a
  live decline against this fact. This population was previously invisible;
  it is the set the old `admissible_count` was silently over-reporting.
- **`admissible_via_contract_count`** -- shape-matched, single contract match,
  route capable, **and not declined** (existing key, meaning now includes the
  decline check). Read as "shape-matched minus declined" for the
  single-match case; a fact matching more than one contract, with only some
  declined, is `ambiguous-producer-contract`, not `admissible`, exactly as
  before this change (declines narrow admission further; they never widen an
  already-ambiguous match into a decision).

Per-contract decline counts: `diagnostics.declined_by_contract`, a
`{contract_id: count}` map over every *live* declined `(fact, contract)`
pair, so a contract with a pile of honest declines is visible in the summary
report rather than only discoverable by grepping the decline artifacts by
hand.

**Declined facts are never silently dropped.** `selection.declined_fact_ids`
lists every ready fact in the `declined_count` population, by id, sorted --
the same treatment doc 288 gives `no_route_ready_fact_ids`: a fact this
system has given up on for now is named, not disappeared.

## Falsifiability: `scripts/validate-producer-contract-declines.py`

The failure mode this whole feature must be designed against, verbatim from
this task's brief: *a decline artifact becomes a cheap way to make the
selector shut up about a fact forever.* Three independent guards, each
capable of failing on a real malformed input:

1. A decline whose `fact_id` does not resolve to a real fact, or whose
   `contract` does not resolve to a real, loadable contract file, is
   rejected -- an invented reference proves nothing (mirrors
   `validate-producer-contracts.py`'s non-example check).
2. A decline whose `decline_reason` is not a bare typed identifier (contains
   spaces, lowercase-first, punctuation, or is empty) is rejected --
   the free-text-reason loophole named above.
3. A decline whose `producer.result` is not exactly `"declined"`, or whose
   `producer.tool` / `producer.decline_message` is missing or empty, is
   rejected -- a decline with no checkable producer identity is
   unfalsifiable by construction.

`scripts/tests/mutation_controls.py` registers `producer-contract-declines`
alongside the existing `producer-contracts` suite; each guard is killed by
exactly one test in
`scripts/tests/test_validate_producer_contract_declines.py`.

## What this slice deliberately does not do

Per the brief: **no refinement of the shape predicates themselves.** A
finer-grained shape that distinguishes "combinator-over-hypotheses" from
"derive-a-new-identity" *at match time* would make declines like this one
rarer, and is real, valuable future work -- but it is a producer-capability
question, not a feedback-loop question, and conflating the two here would
mean neither gets done carefully. This slice's entire job is: when a
producer has already tried and declined, stop presenting that exact
`(fact, contract)` pair as new work, and say so out loud in the report.

## Verification

```
python3 scripts/validate-producer-contract-declines.py
python3 -m unittest scripts.tests.test_validate_producer_contract_declines
python3 -m unittest scripts.tests.test_fact_frontier
python3 scripts/validate-facts.py
python3 scripts/check-autogenesis-holdout-isolation.py
python3 scripts/fact-frontier.py --json
```

The new selection on the current tree (see
`docs/plan/status/decline-feedback.md` for the verbatim `--json` excerpt) is
a different fact: `F:ml430-int-add-modeq-left-ee732b5b` is no longer
admissible via `producer-contract-int-modeq-family-v1`, and selection moves
to the next `Int.ModEq` or `Nat.Coprime` family member with no live decline
against it.
