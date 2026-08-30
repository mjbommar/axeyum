# ADR-0716: Row 2 of a decidable subject — the boundary moves, or the dominance argument does

Status: accepted
Date: 2026-08-30
Index-summary: For carriers whose order is decidable in the kernel (ℕ, ℤ, ℚ), the decision principle every analysis row 2 extracts is already a proved theorem, so that row is provably empty; two other boundaries survive (unbounded search, which reduces to full excluded middle, and expressiveness, which becomes a new row 2′), and where neither applies the Pareto argument must rest on row 1 + row 3 under one trust anchor rather than on boundary mapping.
Index-status: accepted

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
makes a classical theorem land as a graded family, and its Amendment 2 defines
row 2 precisely: an **unprovability witness**, a kernel-checked declaration
showing `classical statement ⟹ a decision principle this kernel lacks`.
Amendment 3 allows a family with **no** row 2, provided the absence is argued
from the shape of the classical proof. Amendment 4 forbids inferring a row 2
from prose describing an absence.

All of that was worked out on real analysis, where the missing principle is
order totality over `CReal` — `CReal.evt_attained_max_decides_sign` extracts
analytic LLPO from an attained maximum, and that is the strongest thing this
design claims over a classical library.

The curriculum names three destinations. Extending the treatment to the other
two — number theory (Stein, Shoup) and linear algebra (Boyd–Vandenberghe) —
forces a question ADR-0603 never had to answer: **what is row 2 when the subject
is decidable?** If the answer is "nothing", then for those subjects the row that
carries the dominance argument is empty, and the argument has to come from
somewhere else or be dropped.

## Decision

### 1. For ℕ, ℤ and ℚ, the analysis row-2 mechanism is EMPTY, and this is measured

Read from a freshly built `--release` `shape_search --include-constructed`
(2,426 declarations; every negative paired with a same-kind positive control):

| declaration | present? | axioms |
|---|---|---|
| `Nat.le_total`, `Nat.lt_or_ge` | FOUND (theorem) | 0 |
| `Int.le_total` | FOUND (theorem) | 0 |
| `Rat.le_total`, `Rat.le_or_lt`, `Rat.ble_total` | FOUND (theorem) | 0 |
| `CReal.le_total`, `CReal.lt_total` | ABSENT | — |
| `CReal.lt_cotrans`, `CReal.apart_cotrans` (control) | FOUND (theorem) | 0 |

The principle every analysis row 2 lands on is a **proved, axiom-free theorem**
over the discrete and rational carriers. A reduction terminating in something
the environment already contains carries no information, so **no statement of
number theory, and no statement of rational linear algebra, can have a row 2 of
the analysis kind.**

This satisfies Amendment 3's requirement — "say which decision principle would
have been extracted and why the classical argument never reaches it" — **once
for a whole subject** rather than theorem by theorem. It is a positive
measurement, not a failure to find something, which is the distinction
Amendment 4 exists to protect.

### 2. Two boundaries survive, and they are not the same kind of thing

**(a) Unbounded search.** "Decidable" is pointwise. Bounded minimization is a
theorem here (`Nat.least_divisor_search`, `Nat.minFacAuxMinimal`, both 0
axioms); unbounded minimization does not exist (no `Nat.find`-shaped
declaration; control: `Nat.least_divisor_search`, FOUND), and neither does
unrestricted excluded middle (the kernel has `Decidable.em`, which takes a
`Decidable` instance; controls `em_of_dne`, `em_of_peirce`, `dne_of_em`,
`peirce_of_em`, `not_not_em`, all FOUND and all conditional or weak).

So number theory's row-2 target is the **least-number principle for an
arbitrary predicate**, and it reduces to *full* excluded middle:

> `LNP : ∀ (P : Nat → Prop), (∃ n, P n) → ∃ m, P m ∧ ∀ k, P k → m ≤ k`
> implies `∀ A : Prop, A ∨ ¬A`
>
> — take `P n := (n = 0 ∧ A) ∨ (n = 1)`; `P` is inhabited at 1, so `LNP` gives a
> least `m`; `Nat.lt_or_ge m 1` decides, and `A` would force `m ≤ 0`.

This is a **stronger** boundary than any analysis row 2 in this repository:
`evt_attained_max_decides_sign` extracts LLPO, which is consistent with BISH;
this extracts EM for an arbitrary proposition. It is non-vacuous by
construction, because the *bounded* form is a landed theorem — satisfying
Amendment 2's mandatory non-vacuity control — and falsifiable in Amendment 2's
sense: land an unrestricted `em` and it stops being a boundary result.

**(b) Expressiveness — and it must NOT be called row 2.** Unique factorization's
existence half is landed (`Nat.exists_prime_factorization`, 0 axioms, encoding a
factorization as a function plus a length via `prodRange`). Uniqueness is
multiset equality, and the kernel has no `List`, `Finset`, polymorphic `Prod`,
or quotient by permutation. **The obstruction is that the classical statement
cannot be written, not that a decision is missing.**

Calling that a row 2 would let an expressiveness gap masquerade as a
constructive-strength result — the same category error Amendment 4 corrects
from the other direction, and one that would silently convert this framework's
hardest row into a freebie.

### 3. Therefore: row 2′, the expressiveness witness

A graded family gains an optional **row 2′**. It is discharged by:

1. naming the type the classical statement would need, verified absent against
   the inductive census rather than asserted;
2. stating the strongest form the kernel's type theory *does* admit; and
3. **proving that form** — a row 2′ that states a reformulation without proving
   it is a plan, not a row.

For UFD this needs no new type: `Nat.countRange_permute` already gives
permutation invariance over `[0,n)` (permutations are `Nat → Nat` plus
`injectiveOn`/`mapsInto`), so uniqueness is expressible as multiplicity
agreement at each prime. This is the same distinction ADR-0668 draws between
**evaluating** an unavailable object and **inducting past** it.

Row 2′ is not a weaker row 2 and does not substitute for one. A family may have
both, either, or neither.

### 4. Where no boundary exists, the dominance argument moves to rows 1 + 3

For a subject with no row 2, the family degenerates to rows 1 + 3, and **row 3
stops being a consolation prize — it becomes the entire claim.** The axis is not
"we prove more" but:

> **one statement, one trust anchor, three artifacts** — the general theorem, an
> executable that settles it at any concrete instance, and a certificate a third
> party re-derives, all admitted through `Kernel::add_declaration` (ADR-0601).

Mathlib has `Nat.totient_mul`; it does not attach to that proposition an
executable computing φ(n) and emitting a re-checkable receipt. That is
per-statement dominance of the kind
`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
licenses, and it is falsifiable: it dies the day a classical library ships a
checked decision procedure bound to the same proposition.

**This is a load-bearing obligation, not a rhetorical move.** Surveyed this
session, classical number theory's row 3 barely exists: `axeyum-cas`'s
`is_prime`, `factorize`, `mod_inverse`, `crt`, `legendre_symbol`,
`discrete_log` are bare computation with no witness type and no verifier
(control: 19 `verify_*`/`check_*` functions exist elsewhere in the same crate,
none number-theoretic), and `axeyum-scenarios::number_theory` is BitVec
scenarios validated by `self_check()`, not producer/verifier pairs. The one
genuine exception is
`prove_lia_unsat_by_diophantine_certified`/`check_diophantine_certificate`
(`axeyum-solver/src/lia_gcd.rs`). Linear algebra is much better served —
`simplex::feasible`/`check_farkas` and `lra::FarkasCertificate::verify`, two
independent re-checkers, kernel-reconstructed.

So this ADR moves the argument onto a row that, for number theory, is mostly
unbuilt. Naming that is the price of the move; concealing it would produce
exactly the unfalsifiable claim this project audits against.

## Consequences

- **A three-row family (1, 3, 4) is the normal case in a decidable subject**,
  not a deficiency. ADR-0603 Amendment 3 reached that conclusion for FTA as a
  property of one theorem; this generalizes it to a property of a subject, with
  the decision principle named and measured.
- **A family in a decidable subject must still state its row-2 verdict**, and
  may discharge it by citing §1 of this ADR — but only after confirming the
  statement's decision content really is over ℕ/ℤ/ℚ. A number-theoretic
  statement quantifying over reals, or over an unbounded search, does not
  qualify.
- **Row 2′ claims require the same evidentiary discipline as row 2**: the
  missing type is verified absent against the environment, and the reformulated
  statement is proved, not proposed.
- **Row 3 in number theory is now the tracked gap.** The specific list:
  primality, factorization, CRT and the Legendre symbol each need a witness type
  and a verifier sharing no code with the producer, in the
  `polynomial_mvt`/`verify_mvt_certificate` shape.
- **The curriculum's coverage vocabulary is not adequate to this.**
  `curriculum.toml`'s `covered` conflates "a decidable exercise exists" with "a
  general kernel theorem exists", which is why `number-theory` and
  `linear-algebra` read identically in the map while their kernel content
  differs sharply. Splitting that status is a schema change with a validator and
  an `axeyum-scenarios::mathtour` mirror behind it, and is deliberately left to
  its own ADR rather than decided here.

## Evidence

Measurements, method, per-family tables for both subjects, and the three
highest-yield next targets:
[`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`](../../curriculum/graded-statement-families-number-theory-and-linear-algebra.md).

Two corrections that note records against its own working assumptions, both
relevant to anyone applying this ADR:

- **`Nat.Fin` exists** as a genuine dependent inductive (`val`/`isLt`/`mk`/
  `rec`). What the kernel lacks is a *polymorphic* `Fin`, `List`, `Finset`,
  `Prod`.
- **General-dimension linear algebra over ℚ is already landed**, refuting the
  premise that it needs an absent type: `Rat.dotN` with `dotN_cauchy_schwarz`
  at arbitrary `n`, 0 axioms, over the same finite-function encoding number
  theory uses for `prodRange`. The near-miss is worth repeating — `Rat.dot`
  returns 0 matches and `Rat.dotN` returns 9, so a name-shaped search reports
  the whole subject absent. `funext` is genuinely absent (control: `congrFun'`,
  FOUND), so every matrix identity must be stated **pointwise** rather than as
  equality of functions.
