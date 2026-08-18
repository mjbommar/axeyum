# Lane: agent-creal-field — the field structure over the constructed ℝ

<!-- plan-section: lane-status -->

**ADR-0474: ℚ is now a FIELD, ℝ has Bishop apartness, and the inverse's
partiality is two theorems rather than a scoping note (`WIP`,
agent-creal-field, 2026-08-18).** The prerequisite nobody had listed:
`Rat.inv` existed from the start as a definition with **no law about it**, so
the development had 22 ordered-*ring* laws and an operation named `inv`.
`Rat.mul_inv_cancel` closes that, plus five derived ordered-field lemmas. Over
ℝ: `CReal.Apart := lt x y ∨ lt y x` with four laws, `CReal.no_total_inverse`,
and `pos_of_pos_bound`/`pos_bound_of_lt` — `0 < x` and `∃ k, 1/(k+1) ≤ x` are
the **same** `Prop`, so the modulus always exists and can never be extracted.
71 `CReal` declarations; `rat` and `creal` trusted surfaces still **0**.
**`CReal.inv` itself is NOT built**; design fixed and cost measured in
[`../notes/creal-field.md`](../notes/creal-field.md), which is also where the
next task is.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `PENDING` | **Positivity is closed under multiplication**, over ℚ and over ℝ. Not one of the 22 — they give `mul_nonneg`, of which the zero product is a model — and over ℚ it is a *field* lemma, going through `inv_pos`. Over ℝ it needs no estimate: `CReal.lt`'s rational gaps plus `ofRat_mul`. First proof to open the strict order's `Exists` twice, which works because the target is a `Prop`. |

| 2026-08-18 | `fc52b07f3` | **The inverse's domain, both directions, and the Prop/data line drawn correctly.** `0 < x` and `∃ k, 1/(k+1) ≤ x` are the same proposition, and the `Exists` is a `Prop`, so the modulus can never be extracted into a `CReal`. It is *computed*, not searched: `CReal.lt` already carries a rational gap. **Corrects the previous commit's doc** — a function may TAKE a `Prop` and return a `Type`, it may not BRANCH on one, so the disjunctive `Apart` blocks a definition and the one-sided `PosBound` does not. Plus `CReal.ofRat_le`, `Rat.natDivSucc_pos`. |
| 2026-08-18 | `b91b6dac5` | The four ordered-field lemmas ℝ's inverse is written in — `sub_mul`, `mul_inv_sub_one`, `inv_sub_inv`, `inv_le_of_pos_le` — from `mul_inv_cancel` and the 22 alone, so each transcribes one level up. |
| 2026-08-18 | `6375d7746` | **ℚ is a FIELD.** `Rat.mul_inv_cancel : 0 < q → q·q⁻¹ = 1`, axiom-free: the one proof here about the representation, since `Rat.inv q` is stuck until `num q` is in constructor form. The `negSucc` branch needs no lemma — `Int.lt Int.zero (negSucc m)` **ι-reduces to `False`**. Guard: `Rat.inv (2/1)` REDUCES to `1/2`; the identical script pointed at `= 2/1` is REFUSED. |
| 2026-08-18 | `baf81fd66` | ℝ gets **Bishop apartness**, verbatim rather than encoded — `CReal.lt` already carries the separation as a rational gap. Four laws, `not_equiv_of_apart` ONE-WAY (its converse is Markov's principle), and `CReal.no_total_inverse`. |
