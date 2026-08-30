# Lane: kernel-mutant-survivors — closing the ADR-0780 mutant survivors

<!-- plan-section: lane-status -->

**Status:** COMPLETE — all four ADR-0780 mutant survivors closed. Kill table is
8 killed / 0 survived over a 35-case corpus. No P0 in the unmutated kernel.

Decision: [ADR-0815](../../research/09-decisions/adr-0815-a-mutation-aimed-at-a-call-site-cannot-see-a-shared-predicate.md)

## What this lane was for

ADR-0780's kernel differential found zero Axeyum-accepts/Lean-rejects
disagreements, which is the result we wanted, and then mutation-tested the
kernel itself and had **four of eight mutants survive**. A survivor means a
soundness guard was removed and the differential did not notice. The
`inductives` one was unexplained, which made it the most important open item
in L0 — ADR-0717's risk 1 is exactly "our own kernel could have a shared
semantic defect", and this was a place where we removed a check and the
detector shrugged.

## Headline

**All four had one cause between them, and it is not a corpus weakness.**
Three of the four (`inductives`, `projections`, `quotient`) were killed by a
SECOND guard implementing the same predicate at a different call site; only
`literals` was a genuine missing case. A mutation aimed at a call site cannot
be killed when a redundant implementation still rejects — and the fix is to aim
at the predicate, not to write more cases.

### `inductives` — outcome 1: a different real guard rejects

Five measured rebuilds, `--release`, in this worktree.

| # | kernel state | `add_inductive(Bad, …)` |
|---|---|---|
| E1 | unmutated | `Err(NonPositiveInductiveOccurrence)` |
| E2 | positivity `Err` off (`inductive.rs:1933`) — ADR-0780's mutation | `Err(ReflexiveOrNestedNotSupported)` |
| E3 | field-shape classification off (`inductive.rs:2076`) | `Err(NonPositiveInductiveOccurrence)` |
| E4 | **both off** | **`Ok(())`** — P0 |
| E5 | shared predicate `mentions_group_family` `Const` arm → `false` | **`Ok(())`** — P0 |

E1 rules out the possibility ADR-0780 could not: the case does reach the
targeted guard. E2 names the taker-over. E3 shows symmetry. **E4** proves the
pair is jointly load-bearing rather than both being decoration. E5 is the
correctly-aimed single mutation and it KILLS.

`check_group_positive_occurrence` and `open_group_recursive_field_shape` are
the same algorithm written twice; one returns `Some` exactly where the other
returns `Ok`. **No case can separate them** — that impossibility is the
finding, not a corpus gap.

### Survivors closed, and the mutant each new case kills

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
