# Lane: agent-complex-foundation — ℂ constructed over the constructed ℝ

<!-- plan-section: lane-status -->

**ADR-0508: ℂ is built, it is free, and its missing order is REFUTED rather than
omitted (`WIP`, agent-complex-foundation, 2026-08-18).** `Complex` — a
one-constructor pair of `CReal`s with equality the *defined* relation
`Complex.Equiv` — carries `zero`/`one`/`I`/`ofReal`, `add`/`neg`/`mul`/`conj`,
four congruence obligations, and **9 of 9** commutative-ring laws. Thirty-nine
named declarations, every axiom footprint empty, whole trusted surface **0**
(`Axiom` + `Opaque` + `Quotient`, not `Axiom` alone):
`cargo run -q -p axeyum-lean-kernel --example complex_ring_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

The other 13 of the `Real` package's 22 laws are the order laws, and they are
**not deferred**: `Complex.no_compatible_order` quantifies over both relations
and derives `False` from seven of them, with `I` as the witness through
`Complex.I_sq`. The witness also checks that `Complex.le`/`Complex.lt` are not
declared — a refutation and an omission look identical otherwise.

Next: (a) a plain-commutative-ring telescope, since ADR-0457's is parameterised
over an *ordered* ring and ℂ is not one; (b) ℚ(i) for `geometry_certify`, which
ADR-0512 deferred ℂ in favour of; (c) `CReal` completeness, which `abs`, `√` and
algebraic closure are all downstream of.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `pending` | **ADR-0508: ℂ is constructed over the constructed ℝ at zero trusted declarations, and ℂ's absence of an order becomes a theorem.** `Complex` is `mk : CReal → CReal → Complex` with `Complex.Equiv` componentwise — no quotient at either level, so `Quot.sound` is never needed. Every ℂ law reduces by δι to two `CReal.Equiv` obligations that are *algebraic*, so they are **decided, not hand-derived**: `complex/ring.rs` normalizes a `CReal` expression to a sorted multiset of signed monomials with opposite pairs cancelled and emits the `Equiv` proof, declaring nothing (every function returns a proof term, in `shifted_bound_le`'s style), so the `CReal` namespace and the trusted surface are untouched by construction. `add` and `mul` are the same commutative monoid, so the reassociation machinery is `rsum_perm`/`iprod_perm` written once against an `Op` tag, one level up and over a *defined* equality — the transcription ADR-0512 predicted. Landed with `conj`, `normSq`, `mul_conj` (`z·z̄ = ‖z‖²`, the law that needs the cancellation pass) and `normSq_nonneg` into `CReal`'s existing nonneg cone. **The finding that is not a construction:** `Complex.no_compatible_order : ∀ le lt, le_refl → lt_irrefl → lt_of_le_of_lt → add_le_add → le_congr → sq_nonneg → zero_lt_one → False`, proved directly with no classical step, so the 13 order laws are refuted rather than skipped. |
