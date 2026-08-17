# Lane: capability-assurance — the strand's own metric was unmeasurable

<!-- plan-section: lane-status -->

**The mathematics strand's primary metric drifted 4 → 11 areas unnoticed**
(`WIP`, capability-assurance, 2026-08-17). Detail:
[`01-decide-vs-certify.md`](../../mathematics-2026-08/01-decide-vs-certify.md).

```
CAPABILITY_ASSURANCE|entries=101|areas=23|external=36|self=48|differential=2|unclassified=15
```

It asks "can a third party check without trusting us?" and calls that the
strand's primary metric — but the answer lived in 101 prose `evidence` fields,
so nobody could count it. Seven areas beyond the documented four had gained
external checking, mostly via Carcara. Agreement with an oracle is tiered
separately so it cannot inflate the number; 15 entries stay `unclassified`
rather than being sorted into a flattering bucket. Now floored.

**Item B is done, and derived** (`--rank`, also in `just flywheel`): the 12
unchecked logics are banded by *distance to an external checker*, not by
opinion. Band 1 — `QF_IDL`, `QF_RDL`, `SAT` — already build a refutation
artifact; `propositional_interpolant` constructs a DRAT proof, checks it with
`check_drat`, and returns `Option<BoolExpr>`, dropping the artifact on the floor.

Ranking exposed a defect in the metric itself: `tier` is per *row*, and three
logics (`QF_AUFBV`, `QF_IDL`, `QF_RDL`) are known only through a compound row,
so a quarter of the gap was uniform-by-assumption. Measured, `QF_IDL / QF_RDL`
genuinely differ — QF_RDL renders a 47 KB Lean theory reconstruction that
official Lean 4.30.0 accepts (two mutations rejected), QF_IDL renders only an
attestation. The table is deliberately **not** edited to claim QF_RDL as
external: `check-lean-gate.sh` compiles a one-module-per-family slice that
contains no QF_RDL module, and moving this metric by rewriting the prose it
reads is the failure this strand exists to prevent.

**Next.** Hand a `QF_RDL` module to the Lean gate — the cheapest gap closure in
the ranking, and plumbing rather than a proof format. Then items A (generate the
table) and C (explicit "decided, not certified" status), which are the real fix:
this checker is a heuristic over prose and says so.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `07de6526` | Mathematics strand's primary metric derived and gated: 36 of 101 capabilities name an external artifact checker, across 11 of 23 logics, against a documented 4 of 26. Control: disabling the external tier drops it to 0 and the floor fires. |
| 2026-08-17 | `a8a862133` | Denominator counts LOGICS not `area` strings: a compound like `QF_UFLIA/UFLRA` spans two, and its abbreviated second element named a phantom `UFLRA`. The 12 logics with no external check are now an explicit queue. |
| 2026-08-17 | `pending` | Item B answered by derivation: the gap is banded by distance to an external checker, and the ranking found QF_RDL already renders a Lean theory module official Lean accepts — a "gap" logic blocked only on gate wiring. Controls: 6 new tests, incl. one proving a solved logic never appears in the queue. |
| 2026-08-17 | `pending` | A control no gate RUNS cannot fail, so it is not a control: 63 of 137 control modules were executed by nothing, and running the 51 needing no cargo found 264 tests — 258 passing and gated for free, 6 erroring, four of them import failures against renamed scripts. Ratcheted; the gate caught its own controls being unwired. |
