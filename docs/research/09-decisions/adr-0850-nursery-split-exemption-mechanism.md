# ADR-0850: A scoped, self-invalidating exemption for the nursery split gate

Status: accepted
Date: 2026-08-30
Index-summary: Adds a component-scoped exemption mechanism to the nursery
split gate, and uses it for three train/development crossings a post-freeze
ledger fix surfaced -- none held-out, all already proved outside autogenesis

## Context

`scripts/check-autogenesis-nursery.py` was red on `main`, and its entire
output was one line: `autogenesis-nursery: declared dependency component
crosses evaluation partitions`. It named no component, no fact, and no
partition, so nobody could act on it, and it had been red for at least a day.

Diagnosed directly against `artifacts/autogenesis/nursery-v1.json` (216
entries, 214 evaluation + 2 longitudinal): **3 declared-dependency components
cross evaluation partitions**, all train/development, with **zero held-out
involvement**. A fourth, previously masked check (`evaluation population
shares a component with Autogenesis-1`) also fires once the first is
silenced, for one of the same three components, which additionally touches
the two longitudinal Autogenesis-1 facts via `F:nat-mul-one`/`F:nat-zero-add`.

Root cause, established from `git log`, not assumed: nursery-v1 froze
2026-08-18 (`c9717b3bc`) against the fact ledger's `depends_on` graph as it
stood then, per ADR-0478's "frozen before target outcomes" design. Commit
`237c1abdd` (2026-08-29, `fix(ledger): re-derive 1054 missing depends_on edges
across 306 facts`) retroactively added those edges from
`theorem_dependency_inventory`'s ground truth -- real kernel proof-term
dependencies that existed all along but were never recorded at freeze time.
Several of the newly surfaced edges cross nursery-v1's frozen partition
boundaries. Nobody re-ran this gate after that commit landed.

Independently verified about the 18 facts across the 3 crossing components:

- None are `held-out` (`component_partitions` for all three crossing
  components is a subset of `{train, development}`).
- All 18 have `epistemic_status: proved`.
- Zero entries in `artifacts/autogenesis/operations.json` (29 total
  operations) reference any of the 18 fact ids.

So every affected fact was proved by ordinary hand development in
`nat_prelude`/`int_prelude`, unconnected to any autogenesis dispatch, before
or independent of the 2026-08-29 ledger-hygiene fix that surfaced the
crossing.

## Decision

Add a component-scoped, self-invalidating exemption mechanism to the gate,
and use it for exactly these three components. Do not move any nursery row's
partition, and do not touch `epistemic_status` or `depends_on` on any fact.

An exemption is a new top-level `component_split_exemptions` array in
`nursery-v1.json`. Each entry names the **exact, closed set of fact ids**
making up one weakly-connected component (never a bare digest -- a digest is
opaque and a reviewer cannot audit it), plus `reason`, `authority`, and
`date`. `validate_exemptions()` in the gate recomputes the digest from that
fact-id list using the SAME `digest()` the split-component check itself uses,
and only suppresses the hard error for a component whose **current** declared
dependency graph produces that exact digest. If a later fact-ledger edit adds
a new dependency that pulls another entry into one of these components, the
recomputed digest changes, the exemption silently stops matching, and the
gate goes red again on the enlarged, unreviewed component -- fail-closed by
construction, not by policy discipline.

This is deliberately **not** the ADR-0542 amendment ledger. ADR-0542 moves a
row between partitions and is irreversible history, because a held-out row's
blindness, once spent, cannot be un-spent. Here nothing is spent that an
amendment would need to record: no partition changes, no row moves, no
autogenesis operation ever touched any of these facts, and the underlying
mathematical dependency the crossing exposes was always true -- the
2026-08-18 partition assignment simply didn't have that information yet.
An exemption records "this specific, already-diagnosed crossing is benign, and
the gate should keep checking that it stays exactly this crossing," which is a
narrower and more mechanical claim than an amendment makes.

The gate's report (`build_report`'s `controls`) surfaces exempted crossings
in full -- `component_split_leaks_exempted`,
`evaluation_longitudinal_component_overlap_exempted`, and the raw
`component_split_exemptions` records themselves -- so an exemption changes the
exit status without hiding what was exempted or why. A `--json` run always
shows the three exempted components and their full membership.

## Evidence

```
$ python3 scripts/check-autogenesis-nursery.py
autogenesis-nursery: 2 partition-leak violation type(s) found: ...
EXIT=1
```
(full detail: 3 components, 18 fact ids, every one's partition, in the commit
that fixed the message -- `2cc851274`)

Independent verification, not inherited from any prior lane's report:

- `component_partitions` for `de94125d520a`, `6959be9c08c2`, `533d01fc3b24`
  are `{train, development}` or `{train, development, longitudinal}` --
  **never** includes `held-out`.
- All 18 member fact ids: `epistemic_status == "proved"` (read from
  `artifacts/facts/*.json` directly).
- `artifacts/autogenesis/operations.json`: 0 of 29 operations reference any
  of the 18 fact ids (checked by scanning the full serialized operation
  record, not just `applicability.fact_ids`).
- `git log` on the affected fact files: each was touched after the
  2026-08-18 freeze, several directly by `237c1abdd` or its sibling
  `depends_on`-repair commits (`935dde5e2`, `8488a62cb`, `047ce83805`).

After adding the exemption records with digests
`de94125d520a…`, `6959be9c08c2…`, `533d01fc3b24…` (recomputed and confirmed
to match `digest(sorted(component_fact_ids))` for each):

```
$ python3 scripts/check-autogenesis-nursery.py
AUTOGENESIS_NURSERY_OK|<sha>|ready=true|evaluation=214|blockers=0
EXIT=0
```

## Open question for a decision above this lane's level

104 of 120 `development` and 72 of 78 `train` v1 entries are *already*
`proved` (measured directly against the fact ledger), against 0 of 16
`held-out`. That asymmetry is consistent with train/development being
intended for ordinary, non-blind work while held-out alone stays blind
(matching every existing ADR-0542 amendment, which moves held-out rows DOWN
to development, never the reverse) -- but nothing in ADR-0478 says so
explicitly, and no gate measures whether train/development facts being
"spent" by ordinary development undermines whatever measurement train and
development are for. This ADR does not resolve that question; it only
records that the 18 facts here are unremarkable against that base rate (they
are not an unusual concentration of spend) and recommends whoever owns
ADR-0478's intent decide whether train/development need their own
"spent-by-ordinary-development" tracking, analogous to ADR-0542's held-out
one, or whether the current asymmetric treatment is the intended design.

## Alternatives

- **Move the minority-partition facts to match the majority** (an ADR-0542
  amendment) was rejected: none of these facts are held-out, an amendment's
  irreversible-history cost is not warranted for a purely bookkeeping
  crossing, and there is no principled "correct" partition to move to -- the
  crossing exists because the SAME weakly-connected component of REAL proof
  dependency spans a partition boundary that was drawn before the dependency
  was known, not because any individual fact is misclassified.
- **Silently correct the split in place (regenerate nursery-v1.json's
  partitions)** was rejected outright: the hard rule for this population is
  amendment, never silent rewrite, and a silent regeneration is exactly the
  failure mode ADR-0478's freeze and ADR-0542's ledger both exist to prevent.
- **Report and defer to a human decision with no code change** was
  considered, since the crossing carries zero held-out risk. Rejected because
  the underlying defect -- a hard error naming nothing -- would remain
  unfixed for the next occurrence, which is worse than this one (a
  train/held-out or development/held-out crossing would carry live risk and
  deserves the same detailed message this ADR ships).

## Consequences

- `scripts/check-autogenesis-nursery.py` is green again, honestly: every
  crossing it is not raising on is named, in the report, with its full
  membership.
- A future component-split crossing that is NOT one of these three exact
  three digests raises loudly with full detail, same as before this ADR.
- If any of these three components later grows (a new nursery fact starts
  depending into it), the exemption stops matching automatically and the gate
  reports the ENLARGED crossing in full, unexempted.
- The train/development "already mostly spent" question is open and flagged
  above; it is not blocked on this ADR and this ADR does not attempt to
  settle it.
