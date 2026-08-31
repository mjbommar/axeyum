# ADR-1090: IVT/EVT row 4 (labeled import) lands; Mathlib's own topology chain admits clean

Status: accepted
Date: 2026-08-31
Index-summary: ADR-0603 row 4 was ABSENT for both IVT and EVT. It now exists for both, sourced from Mathlib itself rather than invented: `intermediate_value_Icc` and `IsCompact.exists_isMaxOn`, exported with their FULL transitive dependency closures (3142 and 2171 declaration records, general topology and all), admitted by `Kernel::add_declaration` with ZERO declines. Labeled `imported-kernel-lean`, non-empty `axiom_footprint`, never counted as ours.
Index-status: accepted

## Context

`docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`
tracked ADR-0603's four-row graded family for both theorems and reported row 4
(labeled import) ABSENT for both — the only row missing for either. This
mattered because IVT/EVT are the theorems the Pareto claim (ADR-0692,
ADR-1030) is argued on, so an incomplete family on the headline example
weakens exactly the comparison a referee would check first.

The existing `imported-kernel-lean` route (5 facts: `Nat.le_refl`,
`Nat.le_succ`, `List.nil_append`, `Bool.and_comm`, `Classical.em`) had never
imported anything from Mathlib — every prior stream's `MANIFEST.json` entry
says explicitly "`Init` alone suffices... no `Std` or Mathlib import is
needed." A prior lane's decline census (`artifacts/lean-imports/
decline-census-2026-08-17.json`) sampled only `Init`+`Std`. So it was an open
question whether the import pipeline could handle a Mathlib theorem's full
dependency closure — general topological spaces, order structures,
`ContinuousOn`, filters — at all, as opposed to the small self-contained
`Init` lemmas it had exercised so far.

## What was verified before building anything

1. **The Lean import toolchain is provisioned and runnable on this host.**
   `scripts/check-lean-gate.sh --print-toolchain` resolves the pinned
   4.30.0 toolchain via `elan` (not on `PATH` — this is documented in
   CLAUDE.md as a recurring false-negative trap). `scripts/
   provision-lean-import-toolchain.sh --verify` passes with no network:

       LEAN_IMPORT_TOOLCHAIN|mathlib=c5ea0035…|lean4export=a3e35a58…|
                             lean=d024af09…|verdict=PASS

   mathlib4 is checked out at the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`
   with oleans already built (`.lake/build/lib/lean/Mathlib/Topology/Order/
   IntermediateValue.olean` etc. present); `lean4export` is built.

2. **How row 4 is done elsewhere.** `proof_route: "imported-kernel-lean"` is
   the mechanism (fact.schema.json's `proof_route` field documents it in
   full); five existing facts use it, all sourced from Lean's own `Init`.
   `F:bool-and-comm` was read in full as the template: two evidence rows
   (a `kernel-term` re-derivation via `cargo test -p axeyum-lean-import
   --test imported_fact_evidence`, and an `exhaustive-enumeration`
   cross-check of the axiom footprint against a real `lean` binary via
   `scripts/check-imported-fact-lean-axioms.sh`), `epistemic_status: proved`
   (the kernel independently admitted the term — that IS something this
   project established, distinct from constructing the proof),
   `axiom_footprint` non-empty by construction (the validator rejects `[]`
   on this route), and `provenance.established_by` stating explicitly that
   the proof was not constructed here. This ADR's two facts mirror that
   shape exactly rather than inventing a new one. The `ml430-*` mirror
   family is a DIFFERENT mechanism (statement-only target, flips to
   `kernel-lean` once WE prove it) and is not row 4.

## Decision

Land row 4 for both theorems, sourced from Mathlib at the pinned commit.

**Export.** `lake env <lean4export> Mathlib.Topology.Order.IntermediateValue
-- intermediate_value_Icc` and the analogous EVT invocation (`Mathlib.
Topology.Order.Compact -- IsCompact.exists_isMaxOn`) from within the mathlib4
checkout. `lean4export` pulls the constant's TRANSITIVE DEPENDENCY CLOSURE,
not the whole module.

**Result: both admit clean, with zero declines.**

| | records | admitted declarations | declines |
| --- | --- | --- | --- |
| `intermediate_value_Icc` | 3,142 | 3,585 | **0** |
| `IsCompact.exists_isMaxOn` | 2,171 | 2,486 | **0** |

Every declaration either theorem's proof transitively rests on — the general
topology chain (`ConditionallyCompleteLinearOrder`, `OrderTopology`,
`DenselyOrdered`, `IsCompact`, `ClosedIciTopology`, `ContinuousOn`, `Set.image`,
`IsMaxOn`, the instance dictionaries connecting them) — is independently
admitted by `Kernel::add_declaration`. This answers the open question from
the census: the pipeline is not scoped to small `Init` lemmas; it handles a
real Mathlib dependency closure at this scale with no blocker.

**New facts**, both `proof_route: imported-kernel-lean`,
`epistemic_status: proved`, `external_status: proved`:

- `F:ivt-mathlib-import-intermediate-value-icc`
- `F:evt-mathlib-import-compact-exists-is-max-on`

`formal.statement` is `Kernel::render_lean` of the admitted type, verbatim —
long and instance-dictionary-heavy (Mathlib's real statement, not a
paraphrase), exactly as row 4 requires: Mathlib's own statement, not ours.

**Axiom footprint: 8 names, not Lean's own 3, and BOTH theorems agree.**
`Kernel::axiom_footprint` over the imported environment reports the identical
set for both:

    Classical.choice, Quot, Quot.lift, Quot.mk, Quot.sound,
    String.Internal.append, propext,
    wrapped._@.Mathlib.Topology.Defs.Filter.2998874748._hygCtx._hyg.2

Cross-checked independently: a real `lean 4.30.0` binary (`lake env lean`
inside the mathlib4 checkout, `#print axioms`) reports **[propext,
Classical.choice, Quot.sound]** for both — matching the existing measurement
in `08-ivt-and-evt-measured-against-mathlib.md` §3 and ADR-1030 exactly. The
five extra names are NOT a translation defect:

- `Quot`, `Quot.lift`, `Quot.mk` alongside `Quot.sound` — this kernel
  classifies the whole Quotient package as trusted declarations, the same
  finer split already documented for `Classical.em` in
  `scripts/check-imported-fact-lean-axioms.sh`'s header comment.
- `String.Internal.append` and `wrapped._@.Mathlib.Topology.Defs.Filter…` are
  new relative to the five `Init`-only facts: real opaque/wrapped
  declarations this specific dependency closure reaches (the second is a
  `wrapped._@...` name, the pattern this kernel uses for a well-founded
  recursion's opaque residual) that the small `Init` lemmas never touched.
  Not a defect in the translation — both are genuine trusted declarations
  Mathlib's own proof rests on for this statement, reported faithfully.

`scripts/check-imported-fact-lean-axioms.sh` gained a `MATHLIB_ROWS` table and
a `lake env lean` code path (bare `lean` cannot resolve a Mathlib name) so this
cross-check is executable and re-runnable, not a one-off measurement:

    scripts/check-imported-fact-lean-axioms.sh intermediate_value_Icc
    scripts/check-imported-fact-lean-axioms.sh IsCompact.exists_isMaxOn

Both exit 0. `crates/axeyum-lean-import/tests/imported_fact_evidence.rs`
gained two `Row` entries (now 7 total) so `cargo test -p axeyum-lean-import
--test imported_fact_evidence -- --nocapture` re-derives sha256, admitted
count, `Kernel::render_lean` type, and `Kernel::axiom_footprint` for these
two on every run, exactly like the five existing rows.

**Negative controls, run in `scripts/lane-snapshot.sh` scratch copies, never
in the tracked tree.** Mutating the IVT row's `declaration` field to a name
that does not exist makes `import_ndjson`'s `.find(...).unwrap_or_else(||
panic!(...))` abort the whole test process before either new row's marker
prints, so BOTH facts' `checker_command`s (`grep -c` on the marker, `-ge 1`)
correctly go to exit 1 (`cargo test` exit 101, marker counts both 0).
Mutating `check-imported-fact-lean-axioms.sh`'s pinned axiom set for
`intermediate_value_Icc` makes that script report `FAIL` and exit 1. Both
restored before committing.

## What this is not

Not a claim that this project proved IVT or EVT: `proof_route` is
`imported-kernel-lean`, `axiom_footprint` is non-empty, and neither fact
counts toward any axiom-free or originated headline (ADR-0601 §3, enforced
structurally by the validator). Not a change to the Pareto verdict —
ADR-1030's per-statement dominance call for IVT and concession for EVT stands
unchanged; row 4 supplies the labeled scaffolding statement, it does not
re-argue dominance. See `08-ivt-and-evt-measured-against-mathlib.md`'s table,
updated alongside this ADR.

## Consequences

- The graded family (ADR-0603: general form, boundary refutation,
  decidable-fragment exact form, labeled import) is now complete — all four
  rows present — for both IVT and EVT.
- The import pipeline is now demonstrated at Mathlib dependency-closure scale,
  not just `Init`. A future row-4 target should expect a similar closure size
  (low thousands of records) rather than the ~50-1,100 records the five
  `Init` facts needed.
- `scripts/check-imported-fact-lean-axioms.sh`'s Mathlib code path is reusable
  for the next Mathlib-sourced import without further script changes — add a
  `MATHLIB_ROWS` entry naming the declaration, expected axiom set, and
  importing module.
- `artifacts/lean-imports/` gained two large (9.9 MB, 6.2 MB) NDJSON fixtures.
  This is a real cost of importing Mathlib-scale closures rather than
  `Init`-scale ones; the MANIFEST records reproduction instructions
  (`reproduction_mathlib`) so the streams need not be trusted as opaque blobs.
