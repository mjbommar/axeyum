# ADR-0855: Extend the nursery component-split gate across nursery-v1 and nursery-v2-extension

Status: accepted
Date: 2026-08-30
Index-summary: check-autogenesis-nursery.py's declared-dependency component
check only ever read nursery-v1.json; extends it to the UNION of nursery-v1
and nursery-v2-extension, surfacing 3 crossing components (none held-out),
one visible only in the union; also settles ADR-0850's open train/development
question from the existing record (held-out alone is blind by design)

## Context

ADR-0850 added a scoped, self-invalidating exemption mechanism to
`scripts/check-autogenesis-nursery.py`'s declared-dependency component-split
check, after a post-freeze ledger fix (`237c1abdd`, 2026-08-29) surfaced
train/development crossings in `artifacts/autogenesis/nursery-v1.json`.

That check reads exactly one file: `NURSERY = ROOT /
"artifacts/autogenesis/nursery-v1.json"`. `artifacts/autogenesis/
nursery-v2-extension.json` (340 preregistered entries, ADR-0615/ADR-0616)
holds a second evaluation population, drawn later against the same fact
ledger, with its own `partition` field per entry (train/development/
held-out) and the same `family`/`proof_shape`/`source_group`/`depends_on`
shape as v1. Grepping the checker script for `nursery-v2-extension` returns
zero matches: no gate anywhere performs a component check that includes it.

A weakly-connected declared-dependency component does not respect which
manifest file its members happen to be listed in. If a v2 entry depends on a
v1 entry (or vice versa) through a real fact-ledger `depends_on` edge, or two
v2-only entries already form a crossing component on their own, neither case
was checked by anything.

## Diagnosis

Independently measured (script: temporary diagnostic, since folded into
`build_cross_population_report`'s own logic; full detail in
`docs/plan/status/nursery-v2-component-coverage.md`): computing weakly
connected components over `nursery-v1`'s 216 entries UNION
`nursery-v2-extension`'s 340 entries (adjacency from
`artifacts/facts/*.json`'s `depends_on`, restricted to edges where both
endpoints are in the combined selected set — the identical method
`check-autogenesis-nursery.py`'s existing `components()` uses) surfaces
**3** declared-dependency components crossing evaluation partitions
(train/development/held-out):

1. **`4c696b5744bb…`** — 3 members, entirely **within v2**:
   `F:ml430-nat-div-gcd-pos-of-pos-left-dd878a3f` (train),
   `F:ml430-nat-div-gcd-pos-of-pos-right-8d26808c` (train),
   `F:ml430-nat-div-mul-cancel-99799a00` (development).
2. **`510e9696bc85…`** — 206 members, a **v1 union v2 merge**. This is
   ADR-0850's three exempted v1-only components (`de94125d520a`,
   `6959be9c08c2`, `533d01fc3b24`) merged with two v2-internal crossing
   components (previously `aee5f7b663cc`, `11b9f2566178` when v2 is checked
   alone) into one component, via real declared-dependency edges between v1
   and v2 facts across the `int-gcd`/`int-dvd`/`nat-choose`/`nat-coprime`/
   `nat-factorial`/`nat-fib`/`nat-modeq` families. Also touches the two
   longitudinal Autogenesis-1 facts (`F:nat-mul-one`, `F:nat-zero-add`),
   same as ADR-0850 found for the v1-only version of this component.
3. **`55e86f8aed26…`** — 4 members, a **v1 union v2 merge visible ONLY in
   the union** (does not appear as a crossing when either file is checked in
   isolation): `F:ml430-int-modeq-add-left-cancel-062ad5fe` (v1, train)
   plus three v2 development entries (`...-left-cancel-c1adde5a`,
   `...-right-cancel-d7366811`, `...-right-cancel-f74acb64`).

**Held-out involvement: none.** Verified directly against every member of
all 3 components — no member has `partition == "held-out"`. This matches
ADR-0850's precedent exactly: real proof-dependency structure the original
partition draws did not know about, spending nothing held-out-blind.

Independently confirmed the ADR-0850 exemption mechanism's self-invalidating
property already works as designed, with no code change: recomputing
`digest()` for each of nursery-v1's 3 existing `component_split_exemptions`
entries against the **live union graph** shows none of them match anymore —
their named component grew by merging with v2 members. This is exactly the
fail-closed behaviour ADR-0850 specifies, now exercised for real by a second
population landing.

As a diligence pass (not the primary target), family/proof_shape/
source_group leak checks were also run over the union: 0 crossings.

## Decision

Add `build_cross_population_report()` to `check-autogenesis-nursery.py`,
performing the identical weak-component-vs-evaluation-partition check as the
existing `build_report`, over entries drawn from BOTH
`nursery-v1.json` and `nursery-v2-extension.json`, wired into `main()` as an
additional hard gate (both checks must pass for exit 0).

It reuses ADR-0850's exemption mechanism verbatim
(`validate_exemptions`, `describe_leak`, `components`) rather than inventing
a second one: an exemption names the exact closed fact-id set of a UNION
component, and its `component_id` is `digest()` of that same list. The
exemption list lives in a new top-level `cross_population_component_split_
exemptions` key in `nursery-v2-extension.json` — deliberately not
`nursery-v1.json`'s own `component_split_exemptions`, so this lane's change
does not touch the file or the exemption list ADR-0850 owns, and does not
alter `build_report`'s v1-scoped readiness/policy computation (v1's
`evaluation_fact_count` floor and friends govern v1's own 214-entry
evaluation population, not this extension — matching
`nursery-v2-extension.json`'s own `coverage.ceiling_authority` note that its
policy is separate).

`describe_leak` gained an optional `origin_of` parameter (tags each printed
member `[v1]` or `[v2]`) used only by the new check; every existing call
site is unaffected (verified: all 19 pre-existing tests in
`test_check_autogenesis_nursery.py` pass unchanged with no edits).

Added the 3 exemption records after the same independent verification
ADR-0850 performed: every member fact confirmed non-`held-out` by reading
its `partition` directly, and the recorded `component_fact_ids` recomputed
to match the checker's own live digest before being written down (never
transcribed by hand).

## Consequences

- `scripts/check-autogenesis-nursery.py` now checks the union of both
  evaluation populations for component-split and longitudinal-overlap
  leakage; `main()` prints a second `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK`
  line and the script exits 1 if either check fails.
- If any of these 3 exempted components later grows (a new fact, in either
  file, starts depending on one of its members), the exemption stops
  matching automatically and the gate reports the ENLARGED crossing in full,
  unexempted — exercised directly by
  `test_exemption_stops_matching_once_the_cross_population_component_grows`.
- A future v1<->v2 or v2-internal crossing that is not one of these three
  exact digests raises loudly with full detail (component id, every member's
  fact id, partition, and origin file), same as ADR-0850's v1-only gate.
- The train/development "already mostly spent by ordinary work" question
  ADR-0850 left open is unaffected by this change and remains open; this ADR
  does not attempt to settle it.

## Settling ADR-0850's open train/development question

ADR-0850 left open whether train/development facts being "spent" by ordinary
development undermines whatever measurement train and development are for,
since 104 of 120 development and 72 of 78 train v1 entries were already
`proved` against 0 of 16 held-out, and "nothing in ADR-0478 says so
explicitly."

The existing record settles this, and it does not need a new gate — the
enforcement already exists, scoped exactly the way the evidence says it
should be:

- **ADR-0542, directly:** rejecting "delete the 19 rows" as a repair for a
  held-out breach, it says outright — "The rows remain fully usable in
  **development, where looking is allowed**." That is an explicit statement
  that development is not a blind-evaluation population; ordinary,
  non-blind work on it is the intended use, not a violation to repair.
- **`scripts/check-autogenesis-holdout-isolation.py`'s own stated scope**
  (out of this lane's edit scope, read only): its two rules are "No held-out
  fact may be settled in the ledger" and "No artifact may reference a
  held-out fact id" — **train and development appear in neither rule.** The
  gate enumerates held-out ids from BOTH `nursery-v1.json` and
  `nursery-v2-extension.json` (confirmed by reading `held_out_facts()`,
  which already unions both manifests — this specific cross-population gap
  does NOT exist for held-out isolation, only for the component-split check
  this ADR closes) and fails closed if that population is empty, unreadable,
  or contaminated. It never inspects train or development settlement at
  all, by design.
- **Every ADR-0542 amendment moves a family OUT of held-out INTO
  development** ("`natural-gcd` moves to `development`") — never the
  reverse, and never into or out of train. The asymmetry is consistent with
  exactly one direction of concern: held-out's blindness is a spendable,
  non-renewable resource; train/development are not that kind of resource
  at all.

So the invariant is: **held-out alone is the blind evaluation population;
train and development are for ordinary work, and their being settled by
routine proving is expected, not a defect.** This is not a new policy — it
is already fully enforced by `check-autogenesis-holdout-isolation.py`
exactly as written, for both nursery-v1 and nursery-v2-extension. Nothing in
this ADR changes that gate or adds a parallel one, because the record shows
none is missing: a gate restricting train/development settlement would
contradict ADR-0542's explicit design rather than complete it.

## Alternatives

- **Fold the union check into `build_report` directly** (reading both files
  inside the existing function) was rejected: `build_report`'s readiness and
  policy floors are specifically about nursery-v1's own 214-entry evaluation
  population (`policy.evaluation_fact_count` 100..300, `required_evaluation_
  partitions`, etc.), and nursery-v2-extension explicitly documents that this
  policy does not govern it. Mixing the union's component graph into that
  computation risks silently changing v1's own `held_out_components` count
  and other policy-relevant figures the moment v2 entries merge into a v1
  component, for no benefit — the two questions (is v1 alone
  evaluation-ready; does the combined dependency graph leak) are independent.
- **A single merged exemption list, replacing nursery-v1's
  `component_split_exemptions`** was rejected: it would require rewriting
  nursery-v1.json (out of this lane's scope, and unnecessary — ADR-0850's
  exemptions remain valid documentation of what was diagnosed about v1
  alone, even though they no longer suppress anything once the union graph
  is checked instead).
- **Silently regenerating partitions to eliminate the crossings** was
  rejected outright, matching ADR-0850 and the standing ADR-0542 rule: no
  partition changes, no row moves, ever, for either evaluation population.
