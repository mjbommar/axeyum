# Lane: ledger-5 — register the last two days' proved mathematics, plus the first honest `cas-internal` fact

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-5, 2026-08-27).** Registered 29 new facts
in `artifacts/facts/` (28 `kernel-lean` + 1 `cas-certificate`).
`python3 scripts/validate-facts.py` is green:

```
805 facts checked, 0 errors  (computed=2 conjectured=3 open=176 proved=620 refuted=4)
  routes: cas-certificate=24(kernel-reconstructed=0,cas-internal=24) imported-kernel-lean=5 kernel-lean=559 search-certificate=12 smt-clausal=9 smt-term-level=17; 557 axiom-free on kernel-lean (not comparable across routes)
  cas-certificate: 24 total -- kernel-reconstructed 0, cas-internal 24
```

(776 pre-existing + 29 new = 805.)

**Ch.24 completion (uniform convergence):** `F:creal-weierstrassmtest` (the
Weierstrass M-test — notes record its two mathematically-necessary
hypotheses: `f` must respect `CReal.Equiv` because `CReal` is a Bishop
setoid, not a literal quotient (ADR-0512); the limit is built at the CLAMPED
point `max a (min pt b)` because `CReal.le` is undecidable and there is no
way to conjure the domain-membership proof an arbitrary symbolic point would
need), `F:creal-uniform-converges-add`, `F:creal-close-within-of-within`.

**The five skipped from batch 4 (`ledger-uc`, see
[133-ledger-uc.md](133-ledger-uc.md)'s Findings — these did not exist on that
lane's base and were correctly refused there; they exist on this lane's
merged `main`):** `F:nat-even-or-odd` (the computed `k := n/2` parity split,
never existential), `F:creal-alternatingbracketupper`,
`F:creal-alternatinglowerbound`, `F:creal-alternatingupperbound`. (The fifth
named in that lane's findings, `CReal.weierstrassMTest`, is registered above
as its own Ch.24-completion entry, not duplicated here.)

**Trig (16 facts):** `F:creal-sinterm`, `F:creal-sinseriespartial`,
`F:creal-sintermabsledominant`, `F:creal-sinone`, `F:creal-sinoneconverges`,
`F:creal-sinone-alternating-lower`/`-upper`, `F:creal-sinone-nonneg`,
`F:creal-sinone-le-exp-term-one`, `F:creal-expterm-antitone`,
`F:creal-expterm-zero-eq-one`, `F:creal-expterm-one-eq-one`,
`F:creal-cosone-alternating-lower`/`-upper`, `F:creal-cosone-nonneg`,
`F:creal-cosone-le-exp-term-zero`. The last two are the REAL `[0,
expTerm(0)]` bound on `cos(1)` and are recorded as SUPERSEDING (without
deleting) the loose `[-4,4]`-style bound in `F:creal-cosone-le-four`;
`F:creal-sinone-nonneg`/`F:creal-sinone-le-exp-term-one` do the same for
`sin(1)`.

Detail moved to [`../notes/135-ledger-completion.md`](../notes/135-ledger-completion.md).

