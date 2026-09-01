# Lane: flywheel-restart

<!-- plan-section: lane-status -->

Status: DONE. The dispatch was REFUSED (the selected fact is held-out); both
ADR-1510 guards landed, mutation-verified, six new guards each killing exactly
one test.

## 1. Dispatch: refused, not run

`F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce` —
the one fact `scripts/fact-frontier.py --json` reported as
`admissible_via_contract` with `outcome: selected` — is **held-out blind
evaluation population**, confirmed from two independent authorities
(`artifacts/autogenesis/nursery-v2-extension.json` entry 260,
`partition: held-out`, `answer_access: withheld-during-episode`; and
`drawn-population-partition-snapshot-v1.json`). Its family
`natural-factorization-lcm` is held-out 10 of 10, so under ADR-0542's split key
closing it would have spent all ten — 10 of the 190 held-out rows in the v2
extension.

Nothing was dispatched. No producer, no import, no export, no Lean.

The reason the selector said otherwise, and the two blind readers behind it,
are written up in
[2026-09-01-the-selector-selected-a-held-out-fact.md](../../research/11-design-review/2026-09-01-the-selector-selected-a-held-out-fact.md).
In one line: `fact-frontier.py`'s `held_out_fact_ids()` names
`nursery-v1.json` literally (the v2 extension landed two days later) **and** is
called from exactly one site — the human-rendered queue line — so the `--json`
selection path applies no held-out screen at all. A third reader, this
repository's own control for the hazard
(`SeedContractHoldoutIsolationTests`), had the same v1-only literal and was
green throughout.

`fact-frontier.py` itself was deliberately NOT changed: putting a held-out
screen on the selection path changes what the selector means and wants its own
ADR.

## 2. ADR-1510's two guards, landed

### Contracts (`scripts/validate-producer-contracts.py`)

`sizing` is now required (`date`, `ledger_sha256`,
`matched_open_ready_count`, plus optional `matched_open_ready_fact_ids`,
`frontier_query`, `note`); `retirement` is the optional lifecycle marker.
`live_population()` is open AND dependency-ready AND not held-out AND not an
outcome-blind mutation fixture — every exclusion is permanent, so counting
them would keep an exhausted contract alive on work nobody may ever do.
`held_out_fact_ids()` reads EVERY `artifacts/autogenesis/nursery*.json`.

What the data said, measured by re-executing each shape predicate:

| contract | live population | outcome |
| --- | --- | --- |
| `producer-contract-int-modeq-family-v1` | **0** | **RETIRED** |
| `producer-contract-nat-coprime-family-v1` | 1 (`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`) | stays live |

So exactly one of the two retires. The naive count would have been 2 for
nat-coprime; one of those two is the held-out fact above, which is why the
exclusion is part of the definition rather than a nicety.

### Declines (`scripts/validate-producer-contract-declines.py`)

A decline whose fact is settled must carry `resolution`; one whose fact is
still open must not; `resolution.closed_by` must resolve to a real path.
26 blocks backfilled (all 26 settled declines; 1 of the 27 is still open and
correctly carries none). `closed_by` is DERIVED — the theorem name from the
fact's own evidence `checker_command`, the module from the `declare_*` /
`d.theorem(p.*` site that admits it: `int_prelude/modeq_family.rs` ×5,
`int_prelude/modeq.rs` ×7, `nat_prelude/primes.rs` ×13,
`nat_prelude/rel_prime.rs` ×1.

`diagnosis_status` is a three-valued vocabulary
(`reproduced` 2 / `attested` 5 / `not-re-executed` 19), **not** a boolean:
only two dispatches have been re-executed since 2026-08-27 and only five carry
a lane attestation, so a boolean here would have recorded "nobody re-checked"
as "still accurate".

### Mutation tables — every new guard kills exactly one test

```
producer-contracts (baseline green, 25 tests)                       exit 0
  a contract may not be SIZED against held-out population   killed 1
  an exhausted contract must be retired                     killed 1
  retirement may not silence a contract with live work      killed 1

producer-contract-declines (baseline green, 33 tests)               exit 0
  a decline against a settled fact must carry a resolution  killed 1
  a decline against an OPEN fact may not carry a resolution killed 1
  resolution.closed_by must name a real path                killed 1
```

Running the table found a regression this lane had introduced and would
otherwise have shipped: `validate_resolution` first used the local names
`missing`/`extra`, duplicating the top-level key guard's anchor, so the
PRE-EXISTING mutation "every required top-level key must be present" reported
`AMBIGUOUS ANCHOR` — an unmeasured mutation, not a result. Renamed; that
mutation is back to `killed 1`. The harness anchors on source TEXT, so a
duplicated `if <name>:` silently converts a registered guard into an
unmeasured one.

## 3. Deliberate side effect

Adding `sizing` changes each contract's digest, so doc 291's re-dispatch rule
correctly stops treating the 27 declines as live. `contract_sha256` was left
UNTOUCHED — editing digests to preserve liveness would defeat the guard that
catches a real capability change. The frontier now reports
`admissible_count: 0` / `refused-no-admissible-candidate`, but that is mostly
coincidence (the gate-coupling rule, not a held-out screen) and is disentangled
in the design-review note.

## 4. Checks run

| check | result |
| --- | --- |
| `python3 scripts/validate-producer-contracts.py` | `contracts=2 retired=1`, exit 0 |
| `python3 scripts/validate-producer-contract-declines.py` | `declines=27 resolved=26`, exit 0 |
| `python3 -m unittest scripts.tests.test_validate_producer_contracts` | 25 tests, OK |
| `python3 -m unittest scripts.tests.test_validate_producer_contract_declines` | 33 tests, OK |
| `python3 -m unittest scripts.tests.test_mutation_controls` | 35 tests, OK |
| `python3 scripts/tests/mutation_controls.py producer-contracts` | exit 0 |
| `python3 scripts/tests/mutation_controls.py producer-contract-declines` | exit 0 |
| `scripts/check-control-registration.sh` | `orphans=0 py_orphans=0`, exit 0 |
| `scripts/tests/test-check-control-registration.sh` | 17 cases, all passed |
| `python3 scripts/validate-facts.py` | 2576 facts, **0 errors**, exit 0 |

Did not run: any cargo build or Rust test sweep (this lane changed no Rust);
any Lean or `lean4export` invocation; the producer dispatch itself.

## Landed changes

| commit | what |
| --- | --- |
| `fce483215` | lane stub |
| `307e5d2e6` | ADR-1510's two guards + the contract sizing/retirement and 26 resolution backfills |
| `71cd59d04` | mutation-control registration for the six new guards + the ambiguous-anchor fix |
