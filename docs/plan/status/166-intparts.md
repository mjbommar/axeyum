# Lane: intparts — integration by parts (Spivak ch. 19), substitution characterised as blocked

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, intparts, 2026-08-27).** Integration by parts is
landed. `CReal.integral_by_parts : ∀ u u' v v' a b (hab : le a b),
HasDerivativeOn u u' a b → HasDerivativeOn v v' a b →
UniformlyContinuousOn u a b → UniformlyContinuousOn u' a b →
UniformlyContinuousOn v a b → UniformlyContinuousOn v' a b →
Equiv (integral (fun r => mul (u' r) (v r)) a b hab ‹u'v witness›)
      (add (add (mul (u b) (v b)) (neg (mul (u a) (v a))))
           (neg (integral (fun r => mul (u r) (v' r)) a b hab ‹uv' witness›)))`
— accepted by `Kernel::add_declaration` on the **second attempt** (one real
bug, see below), axiom-free.

**Route, exactly as the brief characterised.** `has_derivative_mul` gives
`(uv)' = u'v + uv'`. `BoundedOn` witnesses for `u`, `u'`, `v`, `v'` are
derived from the four `UniformlyContinuousOn` hypotheses via
`bounded_of_uniformly_continuous` (**not** taken as independent hypotheses
the way `hasDerivative_cube`/`hasDerivative_mul` itself does — here they are
all cheap since the theorem already assumes uniform continuity of all four
functions). FTC-II (`integral_eq_antideriv_diff`) applied to `u*v` gives
`∫(u'v+uv') = u(b)v(b) − u(a)v(a)`; `integral_add` splits the left side into
`∫u'v + ∫uv'`; the final rearrangement `I1 + I2 ~ D ⟹ I1 ~ D − I2` reuses
`integral.rs`'s own private `add_cancel_right` (already built for FTC-II's
own closing step — no new algebra lemma needed). Every gap between a
hand-built lambda (`u'v`, `uv'`, `u'v+uv'`, `u*v`) and the shape a
combinator's own conclusion produces is a pure beta redex, bridged via
`echain` relying on the kernel's defeq check — the same technique FTC-II's
own `h_dab` bridge uses.

Detail moved to [`../notes/166-intparts.md`](../notes/166-intparts.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | intparts | `CReal.integral_by_parts` — integration by parts, axiom-free, second attempt (one `arrow`-vs-`pi_fv` bug, diagnosed and fixed) — via `has_derivative_mul`, FTC-II (`integral_eq_antideriv_diff`), `integral_add`, and the shared private `add_cancel_right` |
| 2026-08-27 | intparts | Substitution (chain-rule composition) characterised as BLOCKED by `hasDerivative_chain`'s own hypotheses, not merely sized as harder: the outer function's `HasDerivativeOn` shares the inner function's exact `[a,b]`, and the inner function must self-map `[a,b] → [a,b]`, so a range-changing substitution cannot be invoked at all — a new chain-rule variant with an independent outer domain is needed, not a composition of landed pieces |
