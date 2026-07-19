# Wider Glaurung authority timeout/policy matrix

ADR-0262 preregistered this exact six-cell experiment before any driver
execution. It widens the tcpip sole-authority population from 15 to 20 of 338
reachable functions and crosses the default/canonical value-selection knob with
three explicit check timeouts:

```text
{AnyModel, LeastUnsigned} x {100 ms, 250 ms, 1000 ms}
```

Every cell has three order-balanced Z3-authority and Axeyum-authority
repetitions. All 36 processes pass the v6 source, binary, coverage, stability,
policy-accounting, confidence-partition, and hidden-work gates.

## Result

| Policy | Timeout | Raw findings Z3 / Axeyum | Raw backend-only | Solves Z3 / Axeyum | Median elapsed Z3 / Axeyum | Median RSS KiB Z3 / Axeyum |
|---|---:|---:|---:|---:|---:|---:|
| AnyModel | 100 ms | 211 / 209 | 11 / 9 | 3,788 / 3,745 | 6.62 s / 3.93 s | 142,748 / 125,088 |
| AnyModel | 250 ms | 211 / 209 | 11 / 9 | 3,788 / 3,745 | 6.60 s / 3.90 s | 142,992 / 125,268 |
| AnyModel | 1000 ms | 211 / 209 | 11 / 9 | 3,788 / 3,745 | 6.62 s / 3.90 s | 142,784 / 125,252 |
| LeastUnsigned | 100 ms | 185 / 185 | 0 / 0 | 96,075 / 96,075 | 94.54 s / 168.68 s | 152,976 / 191,128 |
| LeastUnsigned | 250 ms | 185 / 185 | 0 / 0 | 96,075 / 96,075 | 93.89 s / 168.68 s | 152,964 / 190,852 |
| LeastUnsigned | 1000 ms | 185 / 185 | 0 / 0 | 96,075 / 96,075 | 94.44 s / 168.90 s | 152,496 / 190,644 |

The ordered finding hashes and every reported work counter are identical across
the three timeouts within each policy/authority cell. Timeout is therefore a
measured no-op over this wider prefix between 100 and 1000 ms; value-selection
policy is not.

AnyModel is stable but authority-dependent at every timeout. The Z3/Axeyum
intersection contains 200 rows, with 11 Z3-only and nine Axeyum-only rows (220
in the combined union). LeastUnsigned produces 185 byte-identical rows under
both authorities at every timeout. Its exact policy telemetry is likewise
identical: 1,436 attempts, 1,434 completed minima, two infeasible paths, 94,646
probes, and zero inconclusive/error/unknown outcomes.

The canonical population is not a preservation result. Only 147 of its 185 rows
occur in the AnyModel combined union; 38 are canonical-only and 73 AnyModel-
union rows are absent from the canonical set. Every row in every cell remains
producer-diagnostic: all six cells have zero high-confidence findings. Without
independent labels, none of these set differences is a true-positive gain or
loss.

Every process reports the same inner worklist partition under both authorities:
21 runs = 20 completed + one deterministic state-budget stop, with zero solve-
budget, timeout-budget, or deadline stops. This is the first full two-authority
campaign to exercise ADR-0250's v6 gate over the wider tcpip prefix.

## Claim boundary

This closes the preregistered first-20 tcpip timeout/policy sensitivity cell. It
shows that, on this population, backend model choice—not the 100--1000 ms wall—
controls the raw finding divergence, and that LeastUnsigned restores exact raw
authority parity at large solve/time/RSS cost.

It does not establish real-world recall, finding preservation, a production
default, deterministic per-check solving, or a solver-speed comparison. Tcpip
still supplies no independently validated positive row. A genuinely broader
labeled population remains mandatory before BoundarySet/DiverseEnum mechanics
or symbolic memory can be admitted for coverage.

## Identities

- Axeyum preregistration/execution revision:
  `ee5b5c4aac6c6ac4614f8060bfc1ece2fe4c0562`.
- Glaurung revision:
  `ff3c0a767a0b085f8552bdb2b363c0b7fa273cbe`.
- tcpip SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`.
- Z3-authority binary SHA-256:
  `63863636b1cd064c664c593b15a29f9e5ab791b013dbf925666481df1861772a`.
- Axeyum-authority binary SHA-256:
  `f4f9312fb0257b0a8f4e2a6422247b7dfc279c1a9b308177fa1b9fda2f1c57a5`.
- [`analysis.json`](analysis.json) SHA-256:
  `7687f1cd828f91641ef88ebaad71c7f905609c5e2a7c667600df4175330ac6ee`.

The six report hashes are printed by the committed runner and preserved in the
ADR-0262 evidence section. Empty stdout/stderr logs confirm that the producer
and analyzer emitted no process diagnostics; the complete findings and
telemetry live in the JSON reports.
