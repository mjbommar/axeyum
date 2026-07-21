# ADR-0311: Group interpolation APIs by logic

Status: accepted
Date: 2026-07-20

## Context

After ADR-0310, warning-denied all-feature rustdoc reports 148 documented
`axeyum-solver` root items. The next independent R4 census covers interpolant
construction and its checked certificates.

The existing root surface contains 21 interpolation entries:

- one common `InterpolantOutcome`;
- three `QF_BV` entries;
- three `QF_UF` entries;
- four LIA entries, including CNF construction;
- four LRA entries, including CNF construction;
- three UFLIA entries; and
- three UFLRA entries.

Nearby model-based projection functions are quantifier-elimination primitives,
not interpolants. Two `verify_*_interpolant` functions declared `pub` inside
private implementation modules were never reachable from the crate surface and
must not become public accidentally. The general `Solver` object stays at the
root as a compact consumer facade.

The interpolation surface is full-profile only. Glaurung's production
dependency selects `qfbv`, so it does not compile these APIs. Existing
full-profile callers use root paths, making source compatibility a required
gate.

## Decision

**Add a full-only `interpolation` facade with one common outcome and six
logic-owned submodules, hide corresponding historical root aliases only from
rustdoc, and expose no previously unreachable implementation item.**

The canonical paths are:

- `interpolation::InterpolantOutcome`;
- `interpolation::bitvectors` for `QF_BV`;
- `interpolation::uninterpreted_functions` for `QF_UF`;
- `interpolation::linear_integer` for LIA and its CNF route;
- `interpolation::linear_real` for LRA and its CNF route;
- `interpolation::uflia`; and
- `interpolation::uflra`.

Historical crate-root paths remain callable and type-identical. No interpolant
algorithm, certificate verifier, partition semantics, solver routing, feature
selection, or consumer import changes.

## Evidence

- Strict all-feature rustdoc reports 128 documented root items, down from 148.
- The `interpolation` subtree contains 27 entries: one outcome, six submodule
  links, and 20 logic-specific contracts.
- Subtree counts are 3 `QF_BV`, 3 `QF_UF`, 4 LIA, 4 LRA, 3 UFLIA, and 3 UFLRA.
- The minimal `qfbv` profile remains at 26 documented root items, exposes only
  the `proofs` module, and has no `interpolation` module.
- Dedicated all-feature API tests compare representative type identity and
  function addresses in all six logic submodules against historical root paths.
- All 891 full-profile solver library tests, strict all-target Clippy, and both
  warning-denied rustdoc profiles pass under the bounded one-job configuration.

## Alternatives

- **Include model-based projection.** Rejected: MBP eliminates variables from a
  model/region; it is useful to interpolation internally but has a different
  public contract.
- **Expose each implementation module.** Rejected: the UFLIA/UFLRA modules
  contain verifier functions that were never in the public crate surface, and
  the LIA/LRA CNF routes are split across files despite one semantic family.
- **Move interpolants under `proofs`.** Rejected: an interpolant is a derived
  formula satisfying partition obligations, while the proof facade owns
  refutations, evidence artifacts, and kernel reconstruction.
- **Delete historical root paths.** Rejected: a breaking migration is not needed
  for canonical ownership and documentation discovery.

## Consequences

- The documented all-feature root is 20 items smaller net of the new
  `interpolation` module.
- Interpolation users gain a logic-organized API tree while all existing imports
  continue to compile.
- Previously unreachable internal verifier functions remain unreachable.
- The production `qfbv` footprint remains unchanged.
- R4 should next census the remaining general refutation/certificate utilities
  and core solver helpers rather than create a miscellaneous facade.
