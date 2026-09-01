# The selector selected a held-out fact, and two readers of the partition are blind to it

Date: 2026-09-01
Lane: `flywheel-restart`

## What happened

Lane `flywheel-restart` was dispatched to run the one fact the frontier had
selected. It did not run it. The fact is **held-out blind evaluation
population**, and dispatching it would have spent the whole
`natural-factorization-lcm` family — 10 of the 190 held-out rows in
`nursery-v2-extension.json`.

The dispatch was recommended in three places, none of which is at fault
individually:

- `python3 scripts/fact-frontier.py --json` reported
  `"outcome": "selected"`, `admissible_via_contract_count: 1`, with
  `F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`
  as the sole `admissible_fact_ids` entry;
- [ADR-1510](../09-decisions/adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)'s
  Consequences section: *"The loop has a candidate. Dispatch it."*;
- [the 2026-09-01 contract-decline review](2026-09-01-why-every-contract-dispatch-declined.md)
  §6: *"Dispatch the fact the selector already selected. One lane, existing
  recipe."*

## The partition, from two independent authorities

```
artifacts/autogenesis/nursery-v2-extension.json, entries[260]:
  "fact_id":       "F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce"
  "family":        "natural-factorization-lcm"
  "partition":     "held-out"
  "answer_access": "withheld-during-episode"

artifacts/autogenesis/drawn-population-partition-snapshot-v1.json:
  ["F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce", "held-out"]
```

Its family is held-out in full — 10 of 10 rows — so ADR-0542's split key
(`<family>:<statement-shape>`) means closing this one spends all ten.

The fact's own ledger row says where to look, and says it plainly:

> Preregistered in `artifacts/autogenesis/nursery-v2-extension.json`, which
> carries the partition; **that manifest, not this file, is the split
> authority.**

## Why nothing caught it: one manifest, and one code path

Two separate readers, each correct on the day it was written:

1. **`scripts/fact-frontier.py`'s `held_out_fact_ids()` reads
   `artifacts/autogenesis/nursery-v1.json` literally.**
   `nursery-v2-extension.json` (500 rows, 190 held-out) was preregistered on
   2026-08-29 and did not exist when that function was written. So every
   v2-extension held-out row is invisible to the queue's warning.

2. **That function is called from exactly ONE site, and it is the
   human-rendered queue line.** `grep -n 'held_out_fact_ids'
   scripts/fact-frontier.py` returns two lines: the definition, and one call
   inside the line renderer. The `--json` path — `selection`,
   `admissible_fact_ids`, `diagnostics`, which is what every downstream
   reader and every brief actually consumes — applies **no held-out screen at
   all**. Even a v1 held-out fact would be reported as `admissible` there;
   the warning only ever existed for a human reading `just next`.

The same v1-only literal appears a third time, in this repository's own
control for exactly this hazard:
`scripts/tests/test_validate_producer_contracts.py`'s
`SeedContractHoldoutIsolationTests` — a test whose docstring says "no seed
contract's matched-open set may contain a held-out fact" and which reads one
manifest. It was green throughout.

This is the "a prefix filter is still a literal" failure with the filter being
a *filename*: the authority is the SET of nursery manifests, and three
independent readers each named one member of it.

## Why the contract matched a held-out fact at all

Not a defect in the contract. `producer-contract-nat-coprime-family-v1` was
authored 2026-08-27 and its own `notes` record the check it ran:

> 22 are open, dependency-ready, and sit in `nursery-v1.json` partition
> `development` … **none held-out, checked 2026-08-27.**

True when written. `nursery-v2-extension.json` landed two days later and
preregistered a row this shape happens to match. **A contract cannot be
written to exclude rows that do not exist yet** — which is a second, weaker
argument for ADR-1510 rule 1 than the one the ADR gives: a contract's
population drifts not only because facts get proved, but because the ledger
grows underneath it.

## What this lane changed, and what it deliberately did not

Changed (see ADR-1510 rule 1's implementation):

- `scripts/validate-producer-contracts.py` grew `held_out_fact_ids()` reading
  **every** `artifacts/autogenesis/nursery*.json`, a `live_population()` that
  excludes held-out rows and mutation fixtures, and a guard that rejects any
  contract whose recorded `sizing` population names a held-out fact. Killed
  by exactly one test.
- `SeedContractHoldoutIsolationTests` now reads the glob and **pins** the one
  overlap in `KNOWN_HELD_OUT_SHAPE_MATCHES`, with a control asserting the
  overlap is invisible to a v1-only reader and visible to the glob reader. It
  fails in both directions: a second contamination lengthens the list, a fix
  empties it.

Deliberately **not** changed:

- **`scripts/fact-frontier.py`.** Adding a held-out screen to the `--json`
  selection path changes what the selector means, and the right shape of that
  change (refuse? annotate? a `held_out_fact_ids` band?) is a decision, not a
  patch. It wants its own ADR.

## An accidental side effect, reported as such

After this lane's edits, the frontier reports `admissible_count: 0` and
`outcome: refused-no-admissible-candidate`. **That is not a fix, and it is
mostly not deliberate.** Three things stacked:

1. Adding `sizing` changed each contract's digest, so doc 291's re-dispatch
   rule correctly stopped treating the 27 declines as live. 26 name settled
   facts and are filtered by `band()` anyway; the one live consequence is
   that `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` stopped being suppressed
   by its decline.
2. That fact is named by `scripts/gen-obstruction-producers.py`, so the
   frontier's `gate-coupling-review-required` rule now rejects it instead.
3. The held-out fact is *also* rejected by that rule — because this lane's
   own test file now names its id in the pin above. Fragile: reword the pin
   and the fact becomes `selected` again.

So the held-out fact is out of the admissible set today by a coincidence of
the gate-coupling rule, not by any held-out screen. The defect in §"Why
nothing caught it" is untouched.

## What did not run

- **The dispatch itself.** Not attempted: the target is held-out, and the
  brief's own stop condition applied. No producer, no import, no export, no
  `modeq_family_operation` invocation.
- No Lean, no `lean4export`, no s5 access.
- No cargo build and no Rust test sweep: this lane changed no Rust.
