# Curriculum scenario and teaching backlog

This is the narrow backlog for the curriculum graph and
`axeyum-scenarios` teaching surface. It is not the master queue for Axeyum and
does not authorize solver work. Current project priority lives in root
[`PLAN.md`](../../PLAN.md); the larger content and evidence queue lives in the
[foundational resource build sequence](../foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md).

## Source-driven status

The original backlog on this page has largely landed. The current scenario
catalog includes CRT witnesses, quadratic residue and non-residue cases, sums
of two squares, RSA round trips, finite-field inverses and composite-modulus
controls, rational density and trichotomy, exact linear solutions, polynomial
factorization and division-with-remainder, Fermat's little theorem at fixed
modulus, pigeonhole/counting exercises, and 3×3 finite-field matrix identities.

Do not copy that old list back into a future-work section. Current gaps come
from two checked sources:

- [`Concept::families`](../../crates/axeyum-scenarios/src/concept.rs) identifies
  teaching concepts with no mapped scenario family;
- the generated [curriculum status
  audit](../foundational-resources/generated/curriculum-status-audit.md)
  distinguishes scenario status from resource-pack maturity.

## Priority 1: close explicit concept-family gaps

The current concept graph deliberately leaves these teaching rungs without a
direct scenario family:

1. **SAT and CNF.** Show a small Boolean formula, its Tseitin variables and
   clauses, the SAT/UNSAT result, and the mapping back to the source formula.
2. **Bit-vectors as values.** Teach width, wraparound, signed interpretation,
   and total SMT-LIB operations directly rather than only through downstream
   arithmetic families.
3. **Bit-blasting.** Trace one source predicate through term bits, AIG nodes,
   CNF variables, SAT, and model lifting.
4. **Proofs and independent checking.** Pair an untrusted search result with a
   small checked DRAT/LRAT, Alethe, Farkas, or kernel-reconstructed artifact and
   include a tamper rejection.
5. **Decidable geometry.** Add an exact real-closed-field exercise with a clear
   boundary between the finite/algebraic claim and general Euclidean theory.
6. **Limits of automation.** Contrast a decided query, a resource-limited or
   unsupported `unknown`, and a theorem-horizon claim without presenting
   `unknown` as a crash or counterexample.

Acceptance for each item:

- add or reuse a deterministic self-checking exercise;
- map the family in `Concept::families` only after the exercise exists;
- add a focused learner page or link an existing end-to-end lesson;
- state whether success is witness replay, exhaustive finite checking, sampled
  regression evidence, or an independently checked certificate;
- keep the full scenario and foundational-resource gates green.

## Priority 2: deepen, do not duplicate

The project already has broad example-pack coverage. New work should improve a
trust or teaching boundary instead of adding another near-identical finite
example:

1. Promote representative replay-only negative rows when a distinct checker or
   certificate shape is educationally useful.
2. Connect scenario exercises to the matching foundational pack and learner
   page so the same mathematical object is not maintained twice without a
   cross-check.
3. Promote selected pack rows into solver regressions or fuzz seeds only when
   the source pack, expected result, and solver pressure are all explicit.
4. Add malformed-evidence and wrong-witness controls to lessons that teach a
   proof route.
5. Prefer exact rational or finite-domain examples; label numerical
   approximations and sampled checks at their actual assurance level.

Use the [proof-upgrade queries](../foundational-resources/PROOF-UPGRADE-QUERIES.md),
[proof-route family selector](../foundational-resources/PROOF-ROUTE-FAMILY-SELECTION.md),
and [curriculum-node queries](../foundational-resources/CURRICULUM-NODE-QUERIES.md)
before selecting a new example.

## Priority 3: theorem-horizon bridges

Lean-horizon work should create deterministic interfaces, not imply that a
general theorem is solved:

- connect finite induction obligations to their corresponding quantified
  theorem and reconstruction target;
- connect algebraic calculus shadows to the missing completeness,
  continuity, compactness, or convergence statement;
- distinguish a kernel-checked reconstructed slice from full Lean source,
  elaboration, tactic, workflow, or Mathlib compatibility;
- retain explicit unsupported/unknown cases as teaching artifacts.

The [reconstruction targets](reconstruction-targets/README.md) are frozen proof
goals, not benchmark credits.

## Validation

```sh
cargo test -p axeyum-scenarios
just foundational-resources
just parity-docs
./scripts/check-links.sh
```

Stop if a new `covered` mapping lacks a realized self-checking family, a pack
changes without regenerated dashboards, a solver claim disagrees with the live
support/capability/trust authorities, or a finite shadow is worded as a general
theorem.
