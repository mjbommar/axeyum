# Lane: ledger-integral — register Spivak Ch.13/14 integral facts in the fact ledger

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-integral, 2026-08-27).** The kernel had
~60 inventory rows matching `riemannSum|CReal.integral` (roughly thirteen
lanes' work this session) and the fact ledger had **zero** — a real negative,
confirmed against a 180-fact `CReal` control. Registered ten new facts
covering the construction and its algebra: `F:creal-riemannsum-cauchy`,
`F:creal-integral`, `F:creal-integral-converges`, `F:creal-integral-const`,
`F:creal-integral-add`, `F:creal-integral-le`, `F:creal-integral-scale`,
`F:creal-integral-witness-independent`, `F:creal-riemannsum-integral-close`,
plus the supporting bridge `F:creal-sharedindextocanonical` (the only one of
the optional bridges with a fully honest `depends_on` — every one of its
three direct dependencies was already a registered fact).

Canonical types and direct dependency edges were read from the kernel via a
standalone probe binary (built in the session scratchpad, deleted after use)
and cross-checked against `theorem_dependency_inventory`'s own output on this
tree. `depends_on` links to existing ledger facts wherever
`theorem_dependency_inventory` names one (most of `riemannSum_cauchy`'s
14-edge dependency set was already registered); unregistered prelude
dependencies (`riemannSum_reblock_close`, `riemannSumDeepCauchyFolded`, the
rest of the `riemannSumDeepCauchy*` family, `common_refinement` — a private,
unregistered Rust helper, not a kernel declaration) are named in each fact's
`notes` rather than registered speculatively.

Detail moved to [`../notes/130-ledger-integral.md`](../notes/130-ledger-integral.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Ten new `artifacts/facts/F-creal-*.json` entries for the Ch.13/14 Riemann integral construction and algebra (`riemannSum_cauchy`, `integral`, `integral_converges`, `integral_const`, `integral_add`, `integral_le`, `integral_scale`, `integral_witness_independent`, `riemannSum_integral_close`, `sharedIndexToCanonical`); `python3 scripts/validate-facts.py` green (708 facts, 0 errors). |
