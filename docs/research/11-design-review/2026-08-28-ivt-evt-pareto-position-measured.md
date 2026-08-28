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

## Row 3, followed up: 1 → 3 reconstructed, and 28 is a BACKLOG not a boundary

A lane took the `kernel-reconstructed 1, cas-internal 28` number as its task.
Result: **`cas-certificate: 31 total — kernel-reconstructed 3, cas-internal 28`**.
Nothing was relabelled and no checker was weakened; the two additions are
`F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve` and
`F:cas-difference-of-squares-free-x-kernel-checked`.

**The question I most wanted answered has an answer: 28 is a backlog.** No
`cas-certificate` fact poses a Richardson obligation. The only transcendental
anywhere is the WZ rows' Gamma-quotient *specification*, and its verification
obligation is a rational-function identity reached by the functional equation —
which is exactly why Gosper/Zeilberger terminate. Clusters: WZ 9, NRA geometry
10, real-algebraic 4, partial fractions 1, gf2 4, all inside the decidable
fragment.

### Three qualifications, each of which lowers the headline

**1. For 19 of the 28, reconstruction RELOCATES the assumption rather than
discharging it.** Proving `Σ hᵢgᵢ = f` does not prove that those polynomials
mean the geometric predicates they are named after
(`geometry.cartesian-coordinatisation-of-the-euclidean-plane`); the same holds
for "the Gamma spec denotes this summand". The modelling axiom becomes a kernel
*definition choice* — **better, not removed**. So the honest ceiling for the WZ
and geometry clusters is lower than the phrase "kernel-reconstructed" suggests,
and a future 31-of-31 would still not mean what it sounds like.

**2. Neither addition was new proof work — and that is the finding.** Both were
CAS→kernel bridge tests already authored and passing, never registered as
facts. `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`'s own notes *cited a fact
id that did not exist*. The `cas-certificate` rows were written per
mathematical result, and slice 1's mathematics is trivial — but **under
ADR-0601 the unit of account for row 3 is the ROUTE, not the theorem.** Some
part of the 28 is a registration gap rather than a proving gap.

**3. My two named targets were the wrong ones, for a good reason.** I pointed
the lane at `F:cas-ivt-cbrt2-in-1-2` and `F:cas-extremum-irrational-argmax`.
Folding the existing sign-bracket evidence into either would make
`classify_cas_certificate_fact` label the **whole** certificate —
Sturm count included — as reconstructed, which `cas_ivt_bridge_tests`'s own
module doc warns against. Declining my targets and registering honest ones was
the better answer.

### A briefing error worth recording

**I scoped the lane read-only on `crates/axeyum-lean-kernel/` and asked it to
produce kernel-reconstructed rows. That is structurally impossible.**
`add_declaration` is reachable only through `IntDev::new`, which is
`pub(crate)`, and `axeyum-cas` deliberately does not depend back — both
`Cargo.toml`s say so. Registering already-existing bridges was the entire
reachable surface under my scope. The lane worked out the constraint and said
so; I should have seen it before writing the brief.

**Next step, needing no new kernel machinery**: EVT endpoint exclusion. For
`p = x³ − 6x` on `[−3, 2]`, shift to `q = p − p(−3)` and `r = p − p(2)`, then
admit `0 < polyEval q 4 (ofInt −1)` and `0 < polyEval r 4 (ofInt −1)` with the
existing `zero_lt_via_nat_le` — kernel-proving the maximum is **interior**, as
a sibling fact.

Also corrected: the cbrt2 fact records root containment as needing a polynomial
division construction that "does not yet exist". True over `Rat`; **false over
`Complex`** — `complex/poly.rs` already has `polyMul`, `polyEval_polyMul`,
`factorQuotient` and `factorQuotient_degreeLt`.
