# Lane: holomorphy — the complex derivative is the real shelf's UNIFORM one

<!-- plan-section: lane-status -->

**`Complex.HasDerivativeOn` landed; Leibniz did not, and the obstruction is not
algebra** (`WIP`, holomorphy, 2026-09-05). The brief asked for
`Complex.HasDerivAt` "in the ε–δ form the real shelf uses". The real shelf has
no pointwise derivative: `CReal.HasDerivativeOn F F' a b` is Bishop's *uniform*
differentiability on a closed interval, a one-constructor inductive in `Type`
whose first field is a modulus `Nat → Nat` as DATA. So the lane declared the
same shape on a CLOSED disc and no `Complex.HasDerivAt` at all — a pointwise
complex derivative beside a uniform real one makes every future bridge a
conversion rather than a transcription. **Eighteen** new checked, axiom-free
declarations in `crates/axeyum-lean-kernel/src/complex/deriv.rs`:
`Complex.abs_zero`, `Complex.InDisc`, `Complex.HasDerivativeOn` with its
`.mk`/`.rec`/`.modulus`/`.spec`, the witnesses `hasDerivative_const` / `_id` /
`_neg` / `_add`, and holomorphy on the disc — `Complex.HolomorphicOn` as a
`Sigma` (it CANNOT be an `Exists`: that predicate must land in `Prop` and
`HasDerivativeOn` is in `Type 0`), with `holomorphicDeriv` (`Sigma.fst`),
`holomorphic_spec` (`Sigma.snd`, dependent) and `holomorphic_const` / `_id` /
`_neg` / `_add`.

The lane's measurable finding is **which half of the transcription gets
cheaper**. The ALGEBRA does: `complex/ring.rs`'s `ring_law_proof` decides every
error-term identity in one call, replacing the 87 lines of the real sum rule's steps A–E
(`creal/derivative.rs:3110-3196`) and its five named helpers, and `Complex.abs`'s nonnegativity removes the
real closing step's two-sided `abs_le` split. The ANALYSIS does not:
`hasDerivative_add` uses `Rat.natDivSucc_antitone` at the identical indices and
fuses its two `1/(2e+2)` bounds through `Rat.natDivSucc_add` and
`Rat.natDivSucc_halve` exactly as the real proof does — that bookkeeping is
about rational indices, not about the carrier, and moving up a carrier neither
helps nor hurts it.

**Leibniz is blocked on three missing ℂ ESTIMATES, not on the ring
identity.** The decomposition
`E = EF·G(y) + F'(x)(y−x)(G(y) − G(x)) + F(x)·EG` is one `ring_law_proof`
call; bounding it needs a uniform bound on `|G|`, one on `|F'|`, one on `|F|`,
and a modulus of continuity for `G`. The real `hasDerivative_mul` takes exactly
these as `UniformlyContinuousOn` plus two `Nat` witnesses. Neither
`Complex.BoundedOn` nor `Complex.UniformlyContinuousOn` exists — checked against
the full `Complex.*` inventory. ADR-1642 records both routes and recommends the
hypothesis-carrying one, because `Complex.abs_mul` is an exact `Equiv` where
the real side needed `abs_mul_le_of_bounds`. `polyEval`'s derivative is blocked
behind Leibniz and nothing else; Cauchy–Riemann needs
three named bridge lemmas (`abs_ofReal`, `abs_re_le`, `abs_im_le`). Complex
power series, `exp` on ℂ, and Cauchy's theorem on a triangle were not started.

One measured negative result worth carrying forward: the first version of the
`InDisc` argument-order control was **vacuous**, and vacuous in a way no amount
of care with closed arguments could have fixed. `|z − c| = |c − z|` always, and
at closed arguments the kernel simply COMPUTES both moduli to the same `CReal`
and accepts the exchanged claim — so **no closed instance can distinguish the
argument order at all**. Both halves are now stated at free variables, where
the equality is a theorem rather than a reduction.

Detail and the sizing of each obstruction:
[ADR-1642](../../research/09-decisions/adr-1642-the-complex-derivative-is-the-real-shelfs-uniform-one-not-a-pointwise-hasderivat.md).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `7045bbd18` | `PLAN.md` regenerated for this lane's status block (it was untracked on the first `gen-plan.py` run and skipped): lanes 599 -> 600, landed rows 1105 -> 1106. |
| 2026-09-05 | `aa383393d` | Holomorphy on a disc: `Complex.HolomorphicOn` as `Sigma (Complex -> Complex) (fun F' => HasDerivativeOn F F' c r)` -- it CANNOT be an `Exists` -- plus `holomorphicDeriv` (`Sigma.fst`), `holomorphic_spec` (`Sigma.snd`, dependent) and four constructors. Replaces the VACUOUS `InDisc` argument-order control with a symbolic one (no closed instance can distinguish the order: `\|z-c\| = \|c-z\|` and the kernel computes both). `prelude_fields.rs` mirror regenerated for the 18 new `Complex` fields. ADR-1642. |
| 2026-09-05 | `189fbc799` | Nine tests for `complex/deriv.rs`, each with a negative control; `EXPECTED_STEP_ORDER` gains `deriv::declare_derivative` at position 93; `mutation_controls.py` gains a `complex-derivative` suite whose own comment records that two of its four mutants kill through `ring_law_proof`'s panic and are therefore MASS kills, i.e. weak evidence. |
| 2026-09-05 | `a3066cd01` | `complex/deriv.rs`: `Complex.HasDerivativeOn` on a closed disc, the transcription of `CReal.HasDerivativeOn` — carrier, `.modulus`/`.spec` projections, `InDisc`, `abs_zero`, and the constant / identity / negation / sum witnesses. New module registered from `complex.rs` with its own `DerivNames` (the `poly.rs` arrangement: no hub edit for a new declaration inside the file). All nine names registered in `every_named_complex_declaration_is_checked_and_footprint_free`, which derives coverage from the ENVIRONMENT. |
