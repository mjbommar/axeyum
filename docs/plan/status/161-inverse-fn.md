# Lane: inverse-fn — Spivak ch. 12, the inverse function theorem

<!-- plan-section: lane-status -->

**Done for this session (inverse-fn, 2026-08-27).** First job was
establishing state, since `creal/inverse.rs` and `creal/inverse_fn.rs` are not
what their names suggest and the chapter's status was not written down
anywhere reliable.

**`creal/inverse.rs` (1,137 lines) is unrelated to the inverse FUNCTION
theorem.** It is `CReal.inv` — the multiplicative (field) reciprocal
`1/x` — with its shift/index/congruence plumbing and
`declare_mul_inv_cancel`/`declare_inv_congr`/`declare_inv_index_irrelevant`.
Nothing there was touched.

**`creal/inverse_fn.rs` already carried one landed theorem before this
session**, and it was landed on `main` (commit `94160585a`,
2026-08-26 — a day before this session started, not this session's work):
`CReal.order_reflect_of_pos_deriv`, the order-reflecting converse of
`strict_mono_of_pos_deriv`, conditional on a given `Apart x y`. Its own module
doc already explains why UNCONDITIONAL order-reflection is out of reach
(deciding `x<y` vs `y<x` from a codomain fact alone is IVT-exact-preimage
territory, and `ivt_approx` is still open) and why the `Apart`-conditional
form is exactly what Chapter 12 needs to compose with
`strict_injective_of_pos_deriv`. Also already landed (commit `7156f5304`,
same day, in `monotone.rs`, not `inverse_fn.rs`):
`CReal.inverse_lipschitz_of_pos_deriv`, the CONTINUITY-of-the-inverse
statement (`Apart x y → |x−y| ≤ (2k+2)·|Fx−Fy|`), built by the same
case-split-on-given-`Apart` idiom. So of the brief's three plausible
rungs, **rung 1 (continuity on the image interval) was already done**
before this session, by a prior lane, and needed no further work — it is
exactly what `inverse_lipschitz_of_pos_deriv` states.

**This session landed rung 2: `CReal.ivt_exact_root_at`** — existence of the
inverse as a function:

```
CReal.ivt_exact_root_at :
  ∀ F F' a b, HasDerivativeOn F F' a b →
  UniformlyContinuousOn F a b → le a b →
  ∀ y, le (F a) y → le y (F b) →
  ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
  ∃ c, le a c ∧ (le c b ∧ Equiv (F c) y)
```

Detail moved to [`../notes/161-inverse-fn.md`](../notes/161-inverse-fn.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `7d08d970f` | `CReal.ivt_exact_root_at` — Ch12 inverse existence via shifted IVT, wrapping `ivt_exact_root` around `F − y`. |
| 2026-08-27 | `adbfdee31` | rustfmt the above commit's touched files. |
