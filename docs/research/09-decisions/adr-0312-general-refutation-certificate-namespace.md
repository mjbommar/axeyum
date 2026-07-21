# ADR-0312: Complete the checked-refutation certificate catalog

Status: accepted
Date: 2026-07-20

## Context

After ADR-0311, warning-denied all-feature rustdoc reports 128 documented
`axeyum-solver` root items. The remaining wall mixes two kinds of API that must
not be grouped together:

- compact solver, backend, model, query-construction, and routing contracts that
  are appropriate at the crate root; and
- checked refutation certificates, deterministic constructors, and independent
  validators that lack a canonical domain catalog.

The latter census finds 51 existing entries in four semantic families:

- 22 integer, real, and mixed-arithmetic entries;
- 10 exhaustive finite-domain and finite-bit-vector entries;
- 7 small structural refutation entries; and
- 12 uninterpreted-function and mixed-UF entries.

These are certificate-facing contracts, not general decision procedures. For
example, the arithmetic family includes checked DPLL(T), Farkas, Diophantine,
bounded-integer-blast, even-power, and sum-of-squares artifacts, but excludes
`check_with_lra` and other theory solvers. The finite-domain family owns
exhaustive certification, but not the lazy or local-search backends. Likewise,
`check_model` remains the general original-term SAT replay API.

The census also finds one QF_UF Alethe emitter that still has only its historical
root path even though ADR-0305 established `proofs::alethe` as its canonical
owner.

Everything selected here is full-profile only. Glaurung's production dependency
selects minimal `qfbv`, while full-profile callers still require historical root
paths to compile.

## Decision

**Extend the existing `certificates` catalog with four semantic submodules,
add the missing QF_UF emitter to `proofs::alethe`, and hide corresponding
historical aliases only from root rustdoc.**

The new canonical certificate paths are:

- `certificates::arithmetic` for checked arithmetic refutations;
- `certificates::finite_domains` for exhaustive finite-domain certification;
- `certificates::structural` for small original-term structural refutations;
  and
- `certificates::uninterpreted_functions` for UF and mixed-UF refutations.

`proofs::alethe::prove_qf_uf_unsat_alethe` becomes the canonical proof-emission
path. Every historical crate-root path remains callable and type-identical. No
implementation module, private helper, or new solver capability becomes public.

## Evidence

- Strict all-feature rustdoc reports 77 documented root items, down from 128.
- The `certificates` subtree contains 160 entries. The new subtrees contain 22
  arithmetic, 10 finite-domain, 7 structural, and 12 UF entries, plus their four
  grouping modules.
- The `proofs` subtree contains 116 entries after taking ownership of the QF_UF
  Alethe emitter.
- The minimal `qfbv` profile remains at 26 documented root items, exposes only
  `proofs`, and has no `certificates` module.
- Dedicated compatibility tests compare representative type identity and
  function addresses in all four new submodules and the Alethe path against
  their historical root aliases.
- All 891 full-profile solver library tests, strict all-target Clippy, and both
  warning-denied rustdoc profiles pass under the bounded one-job configuration.

## Alternatives

- **Create one `refutations` catch-all.** Rejected: arithmetic, finite-domain,
  structural, and UF artifacts have distinct semantics and consumers; a flat
  bucket would reproduce the root wall one level down.
- **Group every name ending in `Certificate`.** Rejected: interpolation,
  verification, array, quantifier, proof-format, and solver-backend contracts
  already have different recorded owners.
- **Move general decision procedures beside their certificate types.** Rejected:
  a certificate catalog is not a theory or backend facade. `check_auto`,
  `check_model`, lazy solving, local search, and direct theory procedures remain
  outside this boundary.
- **Delete the historical root paths.** Rejected: artifact readability does not
  require a breaking consumer migration.

## Consequences

- Checked refutations now have domain-owned canonical paths without changing
  their algorithms, validation, trusted boundary, or feature footprint.
- The all-feature root is small enough for a final core/helper ownership audit
  rather than another broad sweep.
- Existing callers remain source-compatible. Removing aliases still requires a
  separately recorded breaking-release decision.
- R4 should next inspect the residual query-construction and solver-helper APIs
  once, preserving compact front-door/backend/model contracts at the root and
  stopping if no independent non-catch-all boundary is justified.
