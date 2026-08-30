# Lane: pi-rung3 — `CReal.sinFnLowerBoundOneToR`, pi rung 3

<!-- plan-section: lane-status -->

**Status: LANDED and kernel-accepted (`DONE`, pi-rung3, 2026-08-28).**

`CReal.sinFnLowerBoundOneToR : ∀ z, le one z → le z (ofRat (natDivSucc 8 4))
→ le (ofRat (natDivSucc 1 3)) (sinFn z)` — pi rung 3
(`docs/plan/status/169-pi.md`'s own sizing): a uniform lower bound
`sin z ≥ 1/4` on `[1, 8/5]`. Confirmed by
`existing_step_order_is_topologically_valid` (~97–99 s across three runs,
`test result: ok`), which builds the FULL prelude through
`Kernel::add_declaration` — the trusted gate, not a syntactic check.

**The 169-pi.md arithmetic checked out exactly as sized**, verified before
building anything: `119·4 = 476 ≥ 375·1 = 375` (`119/375 ≥ 1/4`); the
antitonicity chain `z² ≤ 64/25 ≤ 6 ≤ (2k+2)(2k+3)` for every `k ≥ 0`
(minimum of the RHS is `2·3 = 6` at `k = 0`); `k := 3` is the correct
constant (`natDivSucc 1 3 = 1/4`). No shift is needed, unlike cosine's own
`8/5` bound (rung 2) — sine's magnitude sequence is globally antitone on
this domain.

Detail moved to [`../notes/172-pi-rung3.md`](../notes/172-pi-rung3.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | pi-rung3 | `CReal.sinFnLowerBoundOneToR` -- pi rung 3: a uniform lower bound `sin z >= 1/4` on `[1, 8/5]`, kernel-accepted (`existing_step_order_is_topologically_valid`, ~97-99s). Five kernel rejections fixed: an empty-context `infer` on an open term, two `Int`/`Nat` argument mixups in `normalize_mul_normalize` calls, a `rat_eq_rewrite` anchor typed wrong, `NatOps`'s `Nat`-hardcoded transport misused on a `CReal` value (new `creal_transport`/`creal_eq_motive` fix it), and a ι-defeq assumption between a succ-chain exponent and `Nat.succ_add`'s own target that does not hold without the propositional bridge |
| 2026-08-28 | pi-rung3 | measured: `alternatingLowerBound`'s internal `t_lam` (RIGHT-associated `sign*(coeff*pow)`) is Equiv but never defeq to `CReal.sinFnTerm` (LEFT-associated `(sign*coeff)*pow`) -- the largest of the five rejections. Fixed by building the whole domination/Converges/squeeze chain around `t_lam` directly (`build_t_lam_here`, interning-identical to `alternating.rs`'s own private `build_t_lam`) and bridging to `sinFnTerm` only at the two points that need it (`dom_hyp`, and the squeeze's `sinFnUniformConverges`-derived leg), the second via a per-fixed-`n` `sum_range_congr` equiv rather than any uniform-in-`n` `Converges` transport |
| 2026-08-28 | pi-rung3 | verified before building: 169-pi.md's own arithmetic (`119/375 >= 1/4` via `119*4=476>=375`, antitonicity `z^2<=64/25<=6<=(2k+2)(2k+3)`, `k:=3`) checks out exactly; largest cross-product actually needed (`64*8=512`, sum-check denominator `3000`) stayed comfortably under the 10^3 estimate |
