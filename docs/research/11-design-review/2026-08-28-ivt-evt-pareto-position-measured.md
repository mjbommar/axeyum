# IVT and EVT: the Pareto position, measured rather than asserted

Date: 2026-08-28. The standing goal is to *confirm* that IVT and EVT are
Pareto-dominant over a traditional Mathlib formalization. This is that
confirmation, with the measurements, and with the places the claim does **not**
hold stated first-class rather than omitted.

Everything below was read from `kernel.environment()` via
`prelude_theorem_inventory --include-constructed --release` (6,904 rows) and
from `scripts/validate-facts.py`, not from source text or prose.

## What is measured

**Both families are entirely axiom-free.** Every declaration, footprint 0:

| family | declarations |
| --- | --- |
| IVT | `ivt_approx`, `ivt_exact_root`, `ivt_exact_root_at`, `ivt_iter`, `ivt_step`, `ivt_bisect_approx`, `ivt_bisect_cauchy`, `ivt_bisect_cauchy_bound`, `ivt_bisect_invariant` |
| EVT | `bounded_of_uniformly_continuous`, `evt_attained_max_decides_sign`, `evtLinear_uniformly_continuous` |

**Row 1 is a computed object, not an existential.**
`CReal.bounded_of_uniformly_continuous : ∀ F a b, UniformlyContinuousOn F a b →
le a b → BoundedOn F a b K` for a **COMPUTED** `K` — never `∃ K`.
`CReal.ivt_exact_root : ∃ c, le a c ∧ (le c b ∧ Equiv (F c) zero)` is an
**exact** root, `Equiv (F c) zero` outright, not `ivt_approx`'s `|F c| ≤ eps`
per accuracy — produced by a named five-step chain (`ivt_bisect_hi` as data,
then `_approx`, `_cauchy`, `converges_of_cauchy`, `converges_comp_eventually`).

**Row 2 exists and is non-vacuous, and the non-vacuity was checked.**
`evt_attained_max_decides_sign` shows an attained maximum of `t ↦ t·v` on
`[0,1]` yields `∀ v, v ≤ 0 ∨ 0 ≤ v`. That is only a boundary if the disjunction
is unavailable — and **`lt_total` is absent from the environment**, confirmed by
the same inventory. IVT's is a kernel-*computed* reduction test
(`ivt_bisect_diag_reduces_on_the_identity_bracket_neg_one_two`), exhibiting a
concrete bracket converging to the wrong value.

**Row 2's own last assertion was closed 2026-08-28.**
`evtLinear_uniformly_continuous` is now proved, so the counterexample family is
*machine-checked* to lie inside classical EVT's hypothesis class rather than
resting on the reader knowing an affine map is Lipschitz.

## Where it dominates

- **Trusted base 0 against 3.** Mathlib's analysis rests on `propext`,
  `Quot.sound` and `Classical.choice`. Both families here rest on nothing, and
  a referee reads that off the kernel in one command.
- **Executable where the classical development is `noncomputable`.** The root
  is produced by a named Cauchy sequence that is data; the bound is a computed
  `K`. Mathlib's `intermediate_value_Icc` asserts a classical existential.
- **Row 2 has no counterpart at all.** Mathlib does not carry a machine-checked
  statement of *where* the classical form fails, because it has no reason to.
  That is a capability class, not a better version of an existing row.
- **Checkability.** `validate-facts.py` prints the route split, so second-class
  evidence cannot read as first-class.

## Where it does NOT dominate — stated plainly

- **`ivt_exact_root` is not Mathlib's statement.** It carries one extra
  hypothesis, a uniformly positive derivative. That hypothesis does not make
  any sign decidable; it makes the root unique **with a modulus**, which is
  what turns approximate roots into a Cauchy sequence. So the honest comparison
  is: *stronger in trust and in computational content, weaker in hypothesis-
  freedom.* Anyone claiming plain per-statement dominance here is overclaiming.
- **Row 2 is an UNPROVABILITY witness, not a refutation.** The file says so
  itself: it shows the classical conclusion is at least as strong as a decision
  principle this kernel lacks, **not that the principle is false** — it is
  consistent, hence unprovable here rather than refutable. ADR-0603 calls the
  row "boundary refutation"; that name is looser than what is proved.
- **Row 3 is mostly CAS-internal.** Of 29 `cas-certificate` facts, **1 is
  kernel-reconstructed and 28 are cas-internal**. `F:cas-ivt-sign-bracket-
  cbrt2-kernel-checked` carries `kernel-term` evidence; `F:cas-ivt-cbrt2-in-1-2`
  and `F:cas-extremum-irrational-argmax` are `witness-replay`. Per ADR-0601 that
  is second-class until it reconstructs, and the validator labels it as such.
- **Row 4 does not exist for either family**, and cannot yet: there is no
  axiomatized carrier in this repository a classical IVT or EVT import would
  attach to. `AxReal` axiomatizes only a compatibly-ordered commutative ring —
  no completeness, no Archimedean axiom. Building row 4 means *adding axioms
  first*, which is the opposite of the headline metric.
- **Breadth is conceded, explicitly and by design.** This is two theorem
  families against a ~200k-theorem library.

## Verdict

**Per-statement dominance holds on trust and on computational content, and is
overclaimed if stated without the hypothesis difference.** The uncontested
axes — an axiom-free constructive development, a machine-checked boundary
witness, and CAS answers that arrive as checkable kernel artifacts — are real
and have no Mathlib counterpart. Rows 3 and 4 are where the family is thin, and
row 3's 28-of-29 cas-internal split is the specific number to move.

The architecture question the goal asks about is answered in the affirmative
for a narrower reason than "we proved more": **the four-row family is what makes
the comparison legible at all.** Without row 2 there is no way to say what the
constructive version gives up, and without the route split in the validator
there is no way to stop CAS evidence reading as kernel evidence. Both existed
before today; what changed today is that EVT's row 2 stopped resting on an
assertion.
