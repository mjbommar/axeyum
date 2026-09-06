# Lane s11a — UF / QF_UF Ackermann + declared-sort CEGAR cap

Status: **routing explanation landed; the census's cause attribution for 67 of
the 70 files does not survive a front-door re-measurement.**

Plan anchor: `docs/plan/smt-parity-plan-2026-09-05.md` §2.5, §4 row S11.
Census: `docs/research/11-design-review/2026-09-05-parity-loss-census.md`
(QF_UF 38 files, UF 32 files).
Measured note: `docs/research/11-design-review/2026-09-06-s11a-uf-ackermann-measured.md`.

## 1. Why the 70 files reach the Ackermann routes instead of `euf-online`

Short answer: **35 of them do not.** `euf-online` is already tried first, and on
most of these files it is the route that spends the budget. The census's
per-file `class` is the message of the *last* route in the trace, and on this
family the last route is a millisecond-scale tail after the budget is gone.

`crates/axeyum-solver/src/auto.rs::dispatch_uf_fast_paths` orders the UF ladder
as: `uf-arith-lazy-overbound` (arithmetic-sorted functions only) →
**`euf-online`** (`euf_egraph::check_qf_uf_online_cdclt`, the backtrackable
congruence-closure theory on the CDCL(T) driver) → `dispatch_ufbv_online` →
`euf-offline` → eager Ackermann elimination (`qf-bv`). So the lever the census
names — "try the online e-graph before the eager Ackermann expansion" — is
already the shipped order, and `MAX_ACKERMANN_CONGRUENCE_PAIRS` already gates
only the eager fallback.

`check_qf_uf_online_cdclt` carries **no admission constant of its own**. Its
four decline sites are: no equality atoms; `boolean skeleton outside the online
CDCL(T) encoder`; `timeout in the online CDCL(T) QF_UF driver`; and `model did
not replay (base-sort semantics outside congruence)`. There is nothing to raise.

Per file class, confirmed by `explain_corpus --json --timed-trace` on five
QF_UF and five UF census files and then by the **front door**
(`uf_unknown_probe`, which is `solve_smtlib`):

| Class | Files | What actually happens |
|---|---:|---|
| QF_UF "eager Ackermann would emit N" | 35 | `euf-online` is entered first and **times out** (23.5 s of a 24 s budget, measured). The `qf-bv` Ackermann decline is a 0.3–15 ms tail. The cap is not the binding constraint. |
| QF_UF "declared-sort lazy CEGAR refuses N (bound 64)" | 3 | `euf-online` declines fast (`model did not replay`, 20 ms / 1.1 s), `euf-offline` says `boolean skeleton undecided`, then the 64-pair bound fires **with 21–24 s of budget unspent**. This is the only class the cap actually blocks. |
| UF (all 32) | 32 | The census class is an artifact of the diagnostic tool. `explain_corpus` runs `check_auto_explained` on the **flat assertion view** and its own banner warns it disagrees with `solve_smtlib` on 134 of 397 files; this is one of those classes. At the front door these files never reach the CEGAR bound: they run the e-matching / MBQI / finite-model ladder (`egraph-seg`, `match-seg`, `nested-quant`, `uf-fmf-probe`) and end at `unknown kind=Incomplete detail: query has quantifiers instantiation does not reach (nested, existential, or non-top-level)`. |

Measured trace excerpt (QF_UF, 24 s budget), the shape behind row 1:

```
probe                    probe       9.6ms  fragment {uf}
dl-online                declined  516.4ms
euf-online               declined  23513.6ms  timeout in the online CDCL(T) QF_UF driver
qf-bv                    declined   14.6ms   eager Ackermann ... 14629 congruence constraints ... bound 64
```

Consequence: raising or removing `MAX_ACKERMANN_CONGRUENCE_PAIRS` /
`MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS` can move **at most 3 files**, not 70.

## Landed changes

| Commit | What |
|---|---|
| (pending) | Routing explanation, front-door re-measurement, probe artifacts |
