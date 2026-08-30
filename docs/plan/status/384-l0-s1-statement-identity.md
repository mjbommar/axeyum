# L0/S1 — Bind statement identity

<!-- plan-section: lane-status -->

Lane: `l0-s1-statement-identity`
Phase: S1 of the trusted-library safety roadmap (ADR-0717, selected by ADR-0746)
Decision: [ADR-0763](../../research/09-decisions/adr-0763-statement-identity-is-pinned-for-every-settled-fact-and-absence-is-a-violation.md)
Status: **COMPLETE.** S1's exit criterion holds and is executed on every merge.

## The gap S0 measured, re-measured from the ledger

`artifacts/safety-matrix/safety-matrix.tsv` reported `exact_statement`
142 / 2117 — the thinnest column. Split by population, read from the facts
directly so the two measurements are independent:

| population | settled | pinned before | pinned after |
|---|---:|---:|---:|
| all settled facts | 2120 | 144 | **2120** |
| `F:ml430-*` mirrors | 375 | 27 | 375 |
| native (non-mirror) | 1745 | 117 | 1745 |

Mirrors already had a stronger guard — `check-mirror-statement-fidelity.py`
hashes `formal.statement` against a preregistered catalog, 502 of 514 verified.
**The native 1,745 were the real gap**, and they are the half of S1's
specification that had nothing behind it.

### The old gate could not fail on absence, and that is measured

`check-settled-fact-statements.py` had `if pin is None: continue` — absence read
as "newly settled", never as a gap. Loading `HEAD~2`'s checker with `HEAD~2`'s
144-pin manifest against the live facts:

```
clean                                        -> exit 0
SWAPPED BINDERS on F:creal-ivt-approx        -> exit 0   ACCEPTED
same mutation on a fact it DID pin (control) -> exit 1   rejected
```

The control is what makes this a finding rather than a bug report: the gate
worked correctly and simply had no opinion about 1,976 facts.

## What landed

**Statement identity for every settled fact.** Manifest schema 2 pins, per
fact, the kernel rendering (`formal.statement`), the reader-facing prose
(top-level `statement`), and the declaration it names (`formal.kernel_theorem`),
with superseded digests preserved in `history`. Pinning the prose is new: a
native fact makes two claims, and the field most readers see was unwatched.

**Absence is a violation, and the ratchet cannot be loosened.**
`coverage_floor` bounds unpinned facts (0), identity bindings (1,294) and
headerless statements (30) — and **slack is itself a violation**. Raising an
allowance to sneak something past makes the next run fail because the actual
count is then below the raised allowance. Loosening is self-reverting rather
than merely discouraged.

**`--write` can no longer launder drift.** It used to rebuild the pins from
current state unconditionally, so running it after a drift re-pinned the damage
and the gate went green.

Detail moved to [`../notes/384-l0-s1-statement-identity.md`](../notes/384-l0-s1-statement-identity.md).

