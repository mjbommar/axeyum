# ADR-0177: Widen Glaurung lineage assertion admission

Status: accepted
Date: 2026-07-15

## Context

ADR-0176 accepts nine live sessions and 128 assertions per retained Glaurung
path on the original three-driver tier. Its consequence explicitly requires
held-out GQ10 validation and a new decision if session count or assertion depth
does not generalize. The first held-out driver does exactly that: SurfacePen
never exceeds four live sessions, but its assertion snapshots extend well past
128. The deterministic fallback remains sound, yet routes enough work cold to
lose a material warm performance opportunity.

ADR-0176 remains the decision for the nine-session default and the explicit
lineage/replay boundary. This record supersedes only its 128-assertion default.

## Decision

Raise Glaurung's default per-path assertion ceiling from 128 to 512 inside the
still-opt-in lineage policy.

- Keep the nine-live-session default unchanged.
- Keep explicit decimal overrides, fail-closed invalid values, visible limit
  identity, and deterministic one-shot fallback unchanged.
- Keep `GLAURUNG_AXEYUM_WARM_REUSE=lineage` explicit. No automatic warm policy
  or verdict cache is authorized.
- SAT continues to replay the original assertion set; UNSAT, proof, timeout,
  error, and `Unknown` handling are unchanged.

## Evidence

The 320 KiB held-out SurfacePen driver executes 2,551 same-stream checks. Its
exact v4 assertion distribution is min/p50/p90/p95/p99/max
0/52/352/416/467/479. A ceiling of 128 falls back 965 checks; 256 still falls
back 446. Both policies decide and agree every query with Z3, but one-shot work
is avoidable.

| Assertion ceiling | Warm checks | Assertion fallbacks | Axeyum | RSS |
|---:|---:|---:|---:|---:|
| 128 | 1,586 | 965 | 1,633.0 ms | 87,140 KiB |
| 256 | 2,105 | 446 | 1,257.3 ms | 82,268 KiB |
| 512 | 2,551 | 0 | 1,063.2 ms | 83,340 KiB |
| effectively unbounded | 2,551 | 0 | 1,063.8 ms | 83,332 KiB |

The 512 and unbounded runs have identical warm traffic: 121 exact snapshots,
290,670 retained prefix roots, 19,467 added roots, 147 popped roots, 358
created/closed sessions, and a peak of four. Thus 512 recovers 34.9% of Axeyum
time relative to 128 without a memory increase or an observational analysis.

The 4.8 MiB held-out NETwtw10 driver supplies a different stress shape under a
60-second analysis deadline and hard 4 GiB process cap. At 512 assertions it
has zero assertion fallbacks. Nine live sessions fall back 8,325/23,797 checks,
decide and agree all 23,797, measure Axeyum 16.840 seconds versus Z3 47.613,
and peak at 257,280 KiB RSS. Raising only the live cap to 12 recovers 417 checks
and 1.5% Axeyum time while increasing RSS to 267,232 KiB. This supports retaining
nine as the conservative memory/time choice while widening the orthogonal
assertion ceiling.

The remaining 49 KiB held-out pciidex driver issues no solver checks. Across
all six available `realworld` samples, 512 causes no assertion fallback in any
observed query stream. Glaurung `90df708` implements the change. Its fresh
unset-limit SurfacePen smoke reports `max-live-paths=9` and
`max-assertions-per-path=512`, decides/agrees 2,551/2,551 with zero fallbacks,
and measures Axeyum 1.064 seconds versus Z3 4.365 at 83,140 KiB RSS.

## Alternatives

Keeping 128 was rejected because the held-out corpus shows a large avoidable
cold fallback rate and a 35% Axeyum cost. A formula-size or retained-byte
ceiling may ultimately be more precise, but no new accounting is needed to
admit the observed 479-root shape, and 512 matches unbounded traffic at lower
policy complexity. Removing the assertion ceiling entirely was rejected
because a finite deterministic guard is part of GQ7/GQ9 admission. Raising the
live-session ceiling was rejected: the large Wi-Fi run shows a measurable RSS
cost for little recovered time.

## Consequences

The current bounded opt-in lineage envelope is 9 live sessions and 512
assertions per path. ADR-0176's three-driver evidence remains valid for the
live-session component; ADR-0177 is the held-out correction for assertion
depth.

GQ10 widening has now exercised every available realworld sample, but only the
original three-driver tier has repeated variance. Repeat SurfacePen and the
bounded NETwtw10 tier before GQ9 automatic selection, and add new driver
families when capture data becomes available. Reopen admission design if a
held-out stream exceeds 512 materially or if session count stops tracking RSS.
