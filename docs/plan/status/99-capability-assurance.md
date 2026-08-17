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

**Next.** Items A (generate the table) and C (explicit "decided, not certified"
status) are the real fix — this checker is a heuristic over prose and says so.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `07de6526` | Mathematics strand's primary metric derived and gated: 36 of 101 capabilities name an external artifact checker, across 11 of 23 logics, against a documented 4 of 26. Control: disabling the external tier drops it to 0 and the floor fires. |
| 2026-08-17 | `pending` | Denominator counts LOGICS not `area` strings: a compound like `QF_UFLIA/UFLRA` spans two, and its abbreviated second element named a phantom `UFLRA`. The 12 logics with no external check are now an explicit queue. |
