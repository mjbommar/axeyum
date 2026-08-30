# Notes: kernel-mutant-survivors

Detail moved out of [`../status/kernel-mutant-survivors.md`](../status/kernel-mutant-survivors.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| case | mutant it kills | cases flipped |
|---|---|---|
| `projections::two_constructor_projection_negative` | `projection_inference_data`'s `constructor_count != 1` | 1, to P0 |
| `literals::malformed_nat_bootstrap_negative` | `nat_literal_bootstrap`'s shape validation (the SAME mutation ADR-0780 ran) | 1, to P0 |
| `quotient::lift_without_respectfulness_negative` | `validate_quotient_package`'s per-declaration type contract | 1, to P0 |

Every one flips exactly one case. No case added by this lane kills nothing.

### One case was written, measured, and replaced

The first quotient case exchanged `Quot`'s and `Quot.mk`'s types. Measured
under the mutation it stayed `AgreeReject` — the exchanged package is not
well-typed at all, so the transaction's own `check_declaration` rejects it. The
redundancy trap catches you twice if you are not looking for it. Replaced with
a package that is fully well-typed and simply not Lean's.

### `quotient`'s named reason was stronger than ADR-0780 stated

`reduce_quotient`'s `mk` name sub-check is **unkillable by construction**, not
merely uncovered: `add_quotient_package` is the only route to a
`Declaration::Quotient` and it hard-codes the four names, so a rival
`mk`-shaped constructor cannot exist. Recorded as `redundancy_findings[2]` (R3)
rather than papered over with a case that could not discriminate.

## No P0

The unmutated kernel agrees with pinned Lean 4.30.0 (`d024af09`) on all 35
cases; the only disagreement is the pre-registered `quotient::quot_sound_absent`
incompleteness. Every P0 above is an artefact of a deliberately mutated kernel.
`crates/axeyum-lean-kernel/src/` was restored byte-identical after every
mutation (`diff -q` exit 0, `git status` over `src/` empty) before each commit.

## What the differential still cannot see

It compares accept/reject on a whole declaration, so it is blind to a kernel
that accepts the right things for the wrong reason — in particular to a defect
in a predicate both positivity implementations share and that this corpus does
not exercise: `mentions_group_family`'s `Proj`, `Let` and `App` arms are
reached by nothing here.

## Landed changes

| what | where |
|---|---|
| ADR-0815 | `docs/research/09-decisions/adr-0815-a-mutation-aimed-at-a-call-site-cannot-see-a-shared-predicate.md` |
| three corpus cases + `build_quotient_declarations` seam | `crates/axeyum-lean-kernel/tests/kernel_differential.rs` |
| `KernelError` diagnostic probe | `crates/axeyum-lean-kernel/tests/kernel_differential_probe.rs` |
| kill table: 8/0, `superseded_mutation` blocks, `redundancy_findings` R1–R3 | `artifacts/kernel-differential/mutant-kill-table.json` |

## Not attempted, deliberately

ADR-0780's uncovered list (mutual/nested inductives, indexed families beyond
0-index, Prop-restricted large elimination, structure eta, string literals,
zeta reduction, well-founded recursion, longer reduction chains) is unchanged.
Three cases were added and no more: a case that does not change a mutant's
outcome is decoration, and each of these three is shown to change one.
