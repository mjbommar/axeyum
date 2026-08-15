# ADR-0458: Lean modules declare whether they contain reasoning, and the LRA facade prefers the reconstructor that does

Index-summary: A rendered Lean module carries a content class (theory reconstruction vs structural attestation); the conjunctive-LRA facade routes to the genuine Farkas reconstructor first
Status: accepted
Date: 2026-08-15

## Context

`prove_unsat_to_lean_module` is the entry point a caller reaches for when they
want an `unsat` turned into a Lean proof. For 29 of its fragments it returns a
module produced by a single shared emitter,
`reconstruct_checked_structural_certificate_to_lean_module`:

```lean
axiom axeyum.reconstruct.prop._0 : Prop
axiom axeyum.reconstruct.hyp._1 : axeyum.reconstruct.prop._0
axiom axeyum.reconstruct.hyp._2 : Not axeyum.reconstruct.prop._0
theorem axeyum_refutation : False :=
  axeyum.reconstruct.hyp._2 axeyum.reconstruct.hyp._1
```

The module kernel-checks, is `sorry`-free, declares a theorem of type `False`,
and is byte-identical across all 29 routes. It contains none of the reasoning it
attests to: the refutation is *asserted* in `hyp._2`. For those routes the real
evidence is the Rust certificate that the route's checker re-derived and verified
before the module was rendered — the module was never the carrier.

Two lanes hit this independently. The `infeasibility` lane
(`docs/mathematics-2026-08/diary-infeasibility.md`) found that a pure-`Real`
conjunctive `QF_LRA` core routed to `ProofFragment::LraDpll` and got the shim,
while `ProofFragment::Lra` — the genuine Farkas reconstructor — occurred in the
whole tree only at its produce and consume sites, with no test asserting any
query reaches it. The `ordered-ring-reconstruct` lane
(`docs/mathematics-2026-08/diary-ordered-ring-reconstruct.md`, ADR-0457) declined
to generalize the shim over the ordered-ring interface on the grounds that it
would yield an axiom-free theorem that says nothing.

Two questions therefore had to be closed: which reconstructor owns a conjunctive
real query, and whether a contentless module may be returned from a route that
advertises proof.

## Decision

**A rendered Lean module carries a declared content class, the two classes are
distinguished at the type level and in the artifact's own text, and the
conjunctive-LRA facade routes to the genuine Farkas reconstructor before the
lazy-SMT arm whenever the genuine reconstruction actually builds.**

1. `LeanModuleContent::{TheoryReconstruction, StructuralAttestation}`, with
   `ProofFragment::lean_module_content() -> Option<LeanModuleContent>` as an
   exhaustive match (`None` only for `ProofFragment::Unsupported`, which emits no
   module).
2. Every structural attestation opens with `STRUCTURAL_ATTESTATION_MARKER`
   (`-- axeyum-lean-module-content: structural-attestation`), the refuter's name,
   and a warning that kernel-checking the module establishes nothing about the
   query. `LeanModuleContent::of_module_source` reads the class off the artifact.
3. `reconstruct_proof_fragment_to_lean_module` cross-checks the artifact's class
   against the fragment table on **every** call and refuses a mismatch with
   `ReconstructError::ModuleContentMismatch`.
4. `prove_unsat_to_lean_theory_module` is the entry point for callers who will
   *report* the module as a proof. It returns
   `ReconstructError::NoTheoryContent { fragment }` — a **typed decline** — rather
   than a module with nothing in it.
5. `scan_arithmetic_proof_fragment` gains an arm before the lazy-SMT arm:
   `ProofFragment::Lra` when `lra_farkas_certificate` yields a self-checked
   certificate **and** `reconstruct_lra_proof` builds a term the kernel infers to
   `False`.

The structural attestation is **kept**, not removed or restricted.
`prove_unsat_to_lean_module` keeps its `(ProofFragment, String)` signature.

## Evidence

- **The shim is load-bearing.** 29 routes emit it, including `LraDpll`,
  `ArithDpll`, `BoundedIntBlast`, `NraEvenPower`, the datatype-structural family
  and the whole array-structural family. Four of these are exercised under a real
  Lean binary by `tests/lean_crosscheck.rs`; removing the emitter would drop
  real-Lean checks and would delete the only Lean-side record that those routes'
  certificates were re-derived. Restricting it to a subset would have needed a
  principle that distinguishes the subset, and none exists: the shim is equally
  contentless everywhere.
- **The dispatch fix is safe by construction.** The predicate trial-builds the
  proof term rather than testing shape, so a certificate the reconstructor
  declines keeps falling through to `LraDpll`. The reordering can move a query
  from "attestation" to "arithmetic" and cannot move one to "declined".
- **Reached and measured.** `x < 0 ∧ 0 ≤ x` and `x+y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y` now
  reach `ProofFragment::Lra` through both `scan_proof_fragment` and the facade,
  and the emitted modules carry `axiom Real : Sort (1)`, `Real.add_le_add`,
  `Real.lt_irrefl`, one `axeyum.reconstruct.lra.hyp._N` per asserted row and one
  `axeyum.reconstruct.lra.x._N` per variable. The tests assert that *content*,
  because "kernel-checks and has no `sorryAx`" is true of the shim.
- **No coverage lost.** The two cvc5 `QF_LRA` audit rows (`arith__ite-lift`,
  `simple-lra`) are genuinely Boolean-structured and stay on `LraDpll`;
  `check-lean-gate.sh` is unchanged at 113 real-Lean checks (floor 105).

## Alternatives

- **Delete the structural emitter.** Rejected: see above. It would remove
  capability from 29 routes to fix a labelling defect.
- **Make `prove_unsat_to_lean_module` itself decline structural attestations.**
  Rejected: it would turn ~29 working routes into errors at 199 in-workspace call
  sites, including consumer SDKs (`axeyum-property`, `axeyum-verify`) whose
  contract is "a module when one exists". The permissive door plus a strict door
  gives callers the choice, and the strict door is the one named in the docs for
  anything that will be reported.
- **Change the facade's return type to carry the class.** Rejected *for now*:
  199 call sites across five crates in a shared checkout is a refactor, not a
  labelling fix. This is the honest residual — a caller who ignores the marker,
  the doc, the classifier and the strict door still receives a shim. Recorded
  rather than papered over.
- **A per-fragment table alone, without the artifact marker.** Rejected: a
  hand-written table drifts, and this repository's recurring defect is a tool
  reporting a stale answer confidently. The marker makes the artifact
  self-describing and the cross-check makes the table a live measurement.
- **Route on `lra_farkas_certificate` alone, without trial reconstruction.**
  Rejected: it would route certificate shapes the reconstructor does not cover
  into a hard error where they previously reached a working route.

## Consequences

- **Easier.** A caller can ask, before or after reconstruction, whether a module
  contains reasoning. A reviewer reading a `.lean` file sees it in line 1. A fact
  claiming `kernel-lean` can be checked against the class rather than against the
  exit status. Conjunctive `QF_LRA` from the front door now produces a term that
  `generalize_over_ordered_ring` (ADR-0457) can consume.
- **Harder.** Adding a `ProofFragment` now requires stating its content class.
  The `Lra` classifier costs a second reconstruction of the proof term; on the
  small fixtures this is invisible and it was **not** measured on the 60-row
  `schedule-deadline` core, whose reconstruction is a 5 MB term.
- **Revisited when.** (1) If the classifier's double build costs on a large core,
  the fix is to return the built context from the classifier, not to weaken the
  predicate. (2) The 28 non-arithmetic structural routes are now *marked* gaps;
  each closing one is a separate slice. (3) If the facade's return type is ever
  refactored, the strict door and the permissive door should collapse into one
  that returns the class.
