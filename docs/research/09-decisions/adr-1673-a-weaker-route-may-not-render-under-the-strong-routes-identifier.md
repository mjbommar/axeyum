# ADR-1673: A Fallback That Produces Weaker Evidence May Not Render Under The Strong Route's Identifier

Status: accepted
Index-summary: A route that mints its own assumptions renders under `axeyum_attested_refutation`, a name derived from the kernel's axiom footprint, never under `axeyum_refutation`
Date: 2026-09-06

## Context

`crates/axeyum-solver/src/reconstruct.rs` routes a `ProofFragment::Sos` query
to `reconstruct_sos_to_lean_module_raw`, which runs the honest reconstructor and,
on `ReconstructError::UnsupportedTerm` — **exactly when the honest route cannot
do the work** — hands the query to
`reconstruct_sos_certificate_wrapper_to_lean_module`. That function mints an
opaque `Prop`, an axiom asserting it, an axiom refuting it, and closes `False`
by applying one to the other. It contains none of the reasoning it attests to.

Until this ADR it rendered through `render_ctx_module`, which uses
`LEAN_MODULE_THEOREM` — `axeyum_refutation`, **the same theorem name the honest
route uses**.

Three measurements, all taken on `main` at `29953abe1`:

1. **The wrapper is a hand-inlined copy of the shared attestation emitter, minus
   its banner.** `direct::reconstruct_checked_structural_certificate_to_lean_module`
   builds the identical four steps and then prepends
   `structural_attestation_banner`, whose first line is
   `STRUCTURAL_ATTESTATION_MARKER`. The SOS wrapper repeats the four steps and
   omits the banner.

2. **So the two guards that exist for this could not fire on it.**
   `LeanModuleContent::of_module_source` classifies by that marker; with no
   marker the module reads as a `TheoryReconstruction`. Therefore
   `gate_module_content` agreed with `ProofFragment::Sos`'s declared class and
   passed, and `prove_unsat_to_lean_theory_module` — the function whose entire
   job is to decline a module that contains no reasoning, quoting "the honest
   answer is *there is no Lean proof of this query*" — handed it back as a
   proof. This is the "checker that cannot fail" pattern of
   [evidence-and-checker-discipline.md](../../contributor-guide/evidence-and-checker-discipline.md):
   both guards were live, both were keyed on a sticker the emitter forgot to
   apply, and every counter or grep keyed on `axeyum_refutation` added the
   attested population to the reconstructed one.

3. **The artifact cannot say which query it refuted.** Measured by
   `sos_fallback_labelling_tests::the_fallback_module_is_the_same_bytes_for_two_different_queries`:
   the wrapper emits **byte-identical** modules for `x*x < 0` and
   `(x-y)*(x-y) < 0`, while the honest route emits different ones for the same
   pair. Kernel-checking such a module establishes nothing about either query.
   That impossibility, not the name, is the reason the two populations must not
   share an identifier.

The kernel already distinguishes them. `Kernel::axiom_footprint` of the honest
SOS refutation over the constructed reals, filtered by
`ordered_ring::minted_axioms_of`, is **empty** — it assumes only the query's own
variables and hypotheses. The wrapper's rests on `axeyum.reconstruct.prop._N`,
an assumption it invented. The difference was visible in the module text all
along; what was not distinguishable was the identifier a consumer greps for.

### How often the fallback fires

**Partial. The whole-corpus census did not run**; what follows is the one
slice that completed, and the rest is an open question rather than a zero.

The probe is a throwaway example that walks a directory, keeps every `.smt2`
file declaring a `Real` sort (only those can carry an SOS certificate), and
counts which route each `ProofFragment::Sos` query takes. Post-fix a fallback
firing is a `ModuleContentMismatch`, never an `Ok`, so the count is exact.

Completed slice, `corpus/public-curated/synthetic/QF_NRA`:

```
smt2_files=33 real_sorted=33 parse_fail=0 sos=10 honest=10 fallback=0 err=0
```

**Positive control, in the same shape:** with `reconstruct_sos_proof` forced to
return `UnsupportedTerm`, the same command over the same directory reports
`sos=10 honest=0 fallback=10`. The zero above is therefore a measurement and
not a broken detector.

**What did not run:** the same probe over `corpus/public-curated` (100
`Real`-sorted files of 903) and over `corpus/` as a whole (142 `Real`-sorted
files of 1,329). Both were started and both produced **no output at all** —
the whole-tree run was killed at its 50-minute timeout, and the
`public-curated` run had printed nothing after 10 minutes. The cost is in
`scan_proof_fragment`, which runs refuters, and in the reconstruction itself:
one SOS module over the constructed reals is 2 MB and the four-test fixture
takes ~290 s in debug. Some file early in sort order — the run is sorted, so
`non-incremental/` precedes `synthetic/` — absorbs the whole budget. A census
lane should give the probe a per-file deadline and skip on it, rather than
lengthening the overall timeout.

Two false detectors were discarded on the way to the slice above, both of which
would have printed "0 fallbacks" for the wrong reason:

- Grepping the rendered module for the prop-atom **stem**
  (`sos_certificate_assertions`). `ReconstructCtx::prop_atom_const` uses the
  stem only as a map key and declares the axiom under
  `axeyum.reconstruct.prop._N`; the stem never reaches the module, so this
  reports every fallback as honest. The first "0 fallbacks in the graduated
  NRA set" reading of this lane used it and was void.
- Piping the sweep through `tail`, which discards everything when the run is
  killed rather than finishing.

## Decision

**A route whose refutation rests on assumptions it minted renders under
`LEAN_MODULE_ATTESTED_THEOREM` (`axeyum_attested_refutation`) and carries the
structural-attestation banner. `LEAN_MODULE_THEOREM` (`axeyum_refutation`) is
reserved for a refutation the query paid for. Which name a module gets is
derived from the kernel's own axiom footprint, never chosen by the emitter.**

`render_ctx_module_named_by_footprint` implements it: declare the refutation as
a probe theorem, read `Kernel::axiom_footprint`, run `minted_axioms_of` over it,
and branch on the answer. An empty minted set keeps `axeyum_refutation` and the
bytes are unchanged; a non-empty one gets `axeyum_attested_refutation`, the
shared `STRUCTURAL_ATTESTATION_MARKER` banner, and a line naming which
assumptions bought the `False`.

Two supporting choices:

- **The attested name is not an extension of the honest one.** Several
  consumers ask the question with a bare `contains("axeyum_refutation")` —
  `probe_selected_evidence_lean`'s `lean_theorem_present`, `lean_crosscheck`'s
  `assert_structural_shape`, and the real-Lean `#print axioms` transcript check.
  An `axeyum_refutation_attested` would have satisfied every new assertion while
  leaving all three conflating.
  `assert_names_are_not_substrings_of_each_other` fails if either constant ever
  answers a grep for the other.
- **The front door now refuses the attestation rather than relabelling it.**
  `ProofFragment::Sos` declares itself a `TheoryReconstruction`, and the
  attestation is not one, so `gate_module_content` returns
  `ModuleContentMismatch`. That is the machinery working as designed: the
  fragment table's claim about the route is now falsifiable by the route's own
  output.

### The general rule

> A fallback that produces weaker evidence must not be able to render under the
> strong route's identifier — and "identifier" includes being a substring of it.
>
> The durable form is to derive the identifier from the trusted measurement
> (here, the kernel's axiom footprint) rather than to add a second hard-coded
> name beside the first. A name a producer chooses is a sticker; a name a
> measurement assigns is a projection. Only the second cannot be forgotten.

## Consequences

- `prove_unsat_to_lean_theory_module` declines the SOS attestation, which is
  what it was written to do.
- `prove_unsat_to_lean_module` returns `ModuleContentMismatch` for a query that
  takes the fallback. On the measured corpora no query does, so no shipped
  behaviour changes.
- `evidence.rs`'s `produce_nra_sos_evidence` stores
  `reconstruct_sos_to_lean_module(...).ok()` in `Evidence::UnsatSos::lean_module`
  **without** passing it through `gate_module_content`, and that field's doc
  comment says "when `lean_module` is present, the refutation is ALSO backed by
  a kernel-checked Lean proof". For a fallback query that sentence was false.
  It is now at least self-declaring: the stored module carries the banner and
  the attested name. Making `Evidence::UnsatSos` carry the content class, or
  storing `None` for an attestation, is the right next step and is left to the
  lane that owns `evidence.rs`.

### What this does not fix

`minted_axioms_of` is **calibrated for the LRA naming scheme, and over-reports
over a plain `ReconstructCtx`.** `is_query_local` recognizes a query's own
assumption as `axeyum.reconstruct.<route>.hyp._<n>` — it requires that route
segment and a numeric tail. `ReconstructCtx::fresh_name` emits
`axeyum.reconstruct.hyp._<n>` with no route, which does not match, so **every**
`ReconstructCtx`-built refutation reports a non-empty minted set — honest
`QF_BV` and `QF_UF` reconstructions included.

This was measured, not reasoned: mutant **MD** moved the wrapper's opaque
proposition from `prop._n` to a `hyp._n` name expecting the guard to fall
through to the honest name, and it did not, because the `hyp._n` name is
counted as minted too. The prediction was wrong in the direction that matters
less, but the fact it uncovered is load-bearing: **`render_ctx_module_named_by_
footprint` is scoped to the SOS attestation and must not be reached for from
another route without recalibrating `is_query_local` first.** Applied to
`QF_BV` today it would rename a module that has earned the honest name. The
helper's doc comment says so.

What MD did kill was the fixture's anchor, which at the time grepped the
rendered module for an `axeyum.reconstruct.prop.` line — a name assertion in a
test whose whole point is that names are not the authority. The wrapper is now
split so the minted footprint is returned alongside the module and the fixture
asserts on the `Vec`.

## Alternatives considered

- **Add a `ProofFragment::SosCertificateAttestation` variant** declared
  `StructuralAttestation`, so the fragment a caller receives carries the
  distinction. Only two files in the workspace match `ProofFragment`
  exhaustively, so the variant is cheap — but the fragment is chosen by
  `scan_proof_fragment` *before* the reconstructor runs, and the route taken is
  not known until it declines. Threading the decision back out of
  `reconstruct_proof_fragment_to_lean_module` is a larger change to a file
  another session was working in. Worth doing if the fallback is kept.
- **Delete the fallback.** The right end state, and **not decided here,
  because the census that would decide it did not run.** The one slice that
  completed has it firing zero times out of ten SOS queries, and the honest
  reconstructor's coverage is wide enough that twelve hand-written adversarial
  shapes (odd cross terms, scaled coefficients, nonzero affine parts, the `p >
  0` dual, three variables, a conjunction) all took the honest route — so the
  fallback is plausibly unreachable through the front door. Plausibly is not
  measured. Deletion also changes `evidence.rs`'s `lean_module` from
  `Some(shim)` to `None` on any shape that does reach it, and that consumer
  belongs to another lane. This ADR labels first so that, whichever way the
  census lands, the route is honestly named in the meantime.
- **Detect an attestation by its shape** (an axiom whose type is a bare `Prop`,
  applied to its own negation) instead of by a marker. Rejected as a *general*
  classifier: honest `QF_BV` reconstructions declare
  `axiom axeyum.reconstruct.prop._0 : Prop` for their Boolean atoms, so the
  shape does not separate the populations on its own.
