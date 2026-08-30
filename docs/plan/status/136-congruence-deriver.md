# Lane: congruence-deriver — the setoid congruence deriver

<!-- plan-section: lane-status -->

**Built the setoid congruence deriver (`done`, congruence-deriver,
2026-08-27).** `07-the-cost-model-and-pareto-position.md` §3's "known token
sink to mechanize next": `CReal` is a Bishop setoid, so every function used
under `Equiv` needs its own `Equiv`-respect theorem, and lanes hand-assembled
`mul_congr ∘ pow_congr`-style compositions all week. Structural recursion over
a term's shape, encoded once.

Detail moved to [`../notes/136-congruence-deriver.md`](../notes/136-congruence-deriver.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `cb8b54e20` (+fixups) | Setoid congruence deriver: new `creal/congruence.rs` (registry of 6 congruence lemmas + `Op`/`Arity`/`CongruExpr`/`derive`/`declare_derived_congr`) and `creal/inventory/congruence.rs`; one permanent registration `CReal.mulPowCongr` (power-series term congruence) dispatched from `build_creal_prelude_uncached`; four kernel-checked demos plus a negative control and its mutation test. One new `CRealPrelude` field (`mul_pow_congr`). No other `creal/*.rs` module touched. |
