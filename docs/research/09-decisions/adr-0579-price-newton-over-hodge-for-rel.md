# ADR-0579: Price Newton-over-Hodge divisibility for REL

Status: accepted
Date: 2026-08-20
Index-summary: Record that characteristic-two Newton-over-Hodge gives only divisibility by eight for the endpoint connected trace

## Context

The companion `noh-p2-2026-08` workstream develops a Newton-over-Hodge theorem
for finite abelian characters of arbitrary `2`-power order on smooth affine
curves in characteristic two. This is materially stronger than the zero
`2`-rank input rejected in ADR-0573 and is naturally applicable to the
Carlitz character family underlying `(REL)`.

That companion directory is a read-only review artifact in this lane. Its
claimed theorem is therefore treated here as a conditional premise, not as a
tracked Axeyum dependency or imported proof.

## Decision

Add an exact conditional endpoint ledger. An exact level-`j` Carlitz
character on the affine line has Hodge slopes

```text
1/j, 2/j, ..., (j-1)/j.
```

Newton-over-Hodge therefore gives degree-`n` character-trace valuation at
least `n/j`. Exact-conductor families are Galois stable, so their integral
sum over the connected window is divisible by

```text
2^ceil(n/ell).
```

At both Lemire endpoints and every `ell>=200`, this exponent is three. Round
the existing individual-Weil envelope down to the nearest multiple of this
divisor and compare the result with `(REL)`. Grant no magnitude or sign
credit beyond that forced rounding.

## Evidence

`carlitz_connected_top_newton_hodge_ledger` performs the integer comparison.
At `ell=200`, for both `n=401` and `n=402`, it reports:

```text
forced valuation exponent = 3
forced divisor             = 8
rounding improvement       = 0
exponent needed by rounding alone = 409
missing exponent bits      = 406
```

Exact connected traces through `ell=14` are divisible by the predicted power
of two. This is a consistency control, not evidence for the untracked
Newton-over-Hodge premise.

The primary published framework is Kramer-Miller and Upton,
*p-adic estimates of abelian Artin L-functions on curves*,
<https://arxiv.org/abs/2006.04936>. The characteristic-two extension and its
audit remain in the separate companion artifact.

## Consequences

- The companion theorem is an independent mathematical result worth retaining
  and reviewing, but it does not advance the current numerical REL bound.
- Divisibility by eight cannot control the sign or magnitude of the connected
  trace; no manuscript proof credit is assigned.
- A useful slope route would need aggregate higher-slope cancellation or a
  far stronger trace valuation, not Newton-polygon domination alone.
- The localized identity-cylinder variance of ADR-0578 remains the active
  positive-square bridge.
