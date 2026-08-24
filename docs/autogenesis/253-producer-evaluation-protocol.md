# 253 — General-producer evaluation protocol

Before a new general producer runs, its evaluation contract is frozen. It binds
the partition-safe frontier (89 ordinary candidates and nine must-decline
controls), a five-stage funnel, four mandatory outcome stages, and seven
pre-registered decline classes. This prevents a post-hoc explanation from
turning any result into a favorable one.

The protocol is deliberately not an operation registration. It cannot run a
producer, authorize target-specific logic, or credit a proof. It defines the
minimum evidence a future run must publish: one outcome per input, controls
declined, and independent checking plus clean replay before a kernel-accepted
proposal can become a reproduced result.

```sh
just autogenesis-producer-evaluation-protocol
```
