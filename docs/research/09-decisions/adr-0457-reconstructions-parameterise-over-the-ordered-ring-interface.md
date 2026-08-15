# ADR-0457: Arithmetic reconstructions parameterise over the ordered-ring interface

Status: accepted
Date: 2026-08-15
Index-summary: a Farkas/SOS refutation is generalized over the 30 `Real` declarations, so its axiom footprint is empty and real Lean agrees; the `Real`-specific statement is recovered by instantiation

## Context

[ADR-0456](adr-0456-real-is-an-ordered-ring-modelled-by-int.md) measured that the
`Real` package is an **ordered commutative ring with 1** — 8 carrier/operation
constants and 22 laws, no inverse, no division, no completeness, no Archimedean
axiom, not even totality — and named the route that eliminates its 30 axioms
without constructing a carrier:

> parameterise the consumers over the ordered-ring interface, so a Farkas
> refutation becomes `∀ (R : Type) … <22 law hypotheses> → <refutation>` — a
> theorem with an empty footprint that is *stronger* than today's `Real`-specific
> statement, and which recovers the current statement by instantiation at `Real`.

Until now every arithmetic reconstruction was a statement *about* `Real` resting
on those 30. `F:schedule-critical-chain-infeasible` records `axiom_footprint` as
30 named axioms and its diary states flatly that "axiom-free is not on offer and
cannot be" for this route.

## Decision

**A reconstructed LRA/SOS refutation is generalized over the ordered-ring
interface before it is shipped as evidence.** Concretely:

1. `generalize_over_ordered_ring`
   (`crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs`) takes a
   proof term the kernel has already gated to `False` and λ-abstracts, in
   declaration (= dependency) order, the `Real` declarations, the per-variable
   opaque constants, and the per-constraint hypothesis axioms. Each binder's
   type is computed from the declaration **as it stands in the environment**;
   the resulting statement is whatever `Kernel::infer` returns for the wrapped
   term and is never written by hand.
2. Two telescope scopes are offered and both are public. `FullInterface` binds
   all 30 — one uniform statement shape for every refutation. `Used` binds only
   the declarations the proof rests on, giving a strictly stronger theorem whose
   instantiation reproduces the original footprint name for name.
3. The generalization **fails** rather than returns if the refutation rests on a
   trusted declaration outside the telescope, or if the measured footprint of the
   admitted theorem is not empty. An unexplained axiom is a finding about the
   route, not a nuisance to be tolerated.
4. The `Real` package is **not** reduced. `real: axiom=30` stands, and a consumer
   wanting a `Real`-specific conclusion instantiates at it.

## Evidence

- **Empty footprint, measured.** `Kernel::axiom_footprint` on the admitted
  generalized theorem returns `[]` for all five committed fixtures (three Farkas
  shapes, a strict cycle, and a sum-of-squares). The same run prints the
  un-generalized theorem's footprint beside it — 18, 22, 24, 7 and 10 — so the
  zero is discriminating rather than vacuous, and the fact's `checker_command`
  regex fails on that control row.
- **An independent kernel agrees.**
  `tests/fixtures/lean-modules/arithmetic-ordered-ring-farkas.lean` contains no
  `axiom` declaration at all, and Lean 4.30.0 answers
  `'axeyum_ordered_ring_refutation' does not depend on any axioms`.
  `scripts/check-lean-gate.sh` goes 112 → **113** real-Lean checks (floor 105).
- **Nothing is lost.** Applying the generalized theorem to the 30 `Real`
  constants and the refutation's own variable/hypothesis axioms is a term the
  kernel accepts against `False`, recovering the original statement with its
  original trusted base. Under `Used` the recovered footprint is identical to the
  original's.
- Recorded as `F:ordered-ring-farkas-refutation`, route `kernel-lean`,
  `axiom_footprint: []`.

## Consequences

- **`axiom_footprint: []` is now reachable on the arithmetic route.** The
  earlier statement that it "cannot be" was true of the un-generalized term and
  is superseded for the generalized one; the difference is not a stronger kernel
  but the same proof term with its assumptions moved into the theorem.
- **`theorem_axiom_footprint` cannot audit these theorems** — it builds the
  three preludes and nothing else, so an empty grep of its output is not
  evidence. Footprint claims about solver-built kernels must call
  `Kernel::axiom_footprint` where the declaration lives, and should be
  cross-checked by real Lean's `#print axioms` on a rendered module.
- Coverage is bounded by the reconstructors, not by this ADR: the QF_LIA routes
  still have no Farkas path to a kernel, and `prove_unsat_to_lean_module` still
  routes a pure-Real conjunctive `unsat` to the contentless `LraDpll` shim.
  Generalizing that shim would yield an axiom-free theorem with no content, so
  the entry point is the direct reconstructor until the dispatch order is fixed.
- The abstraction is universe-monomorphic dependent-function abstraction, so it
  needs no kernel change and none was made. A future package law that quantifies
  over predicates is still just a Pi binder here; the cost of such a law lands on
  whoever satisfies the hypothesis at instantiation.
- Revisit when: a `Real` axiom is added (the telescope's completeness test
  `the_ring_telescope_is_every_real_declaration` fails first), or when a
  reconstructor mints a trusted declaration this module does not know how to
  abstract (the generalization refuses, by name).
