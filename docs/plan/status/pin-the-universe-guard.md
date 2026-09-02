# Lane: pin-the-universe-guard — does anything notice if ADR-1495's soundness fix is removed?

<!-- plan-section: lane-status -->

**DONE, pin-the-universe-guard, 2026-09-01.** ADR-1495 closed a `Type : Type`
hole in `Kernel::add_inductive` (Lean's `check_constructor` universe
constraint, `KernelError::ConstructorFieldUniverseTooBig`). The question here
was whether anything detects its removal. Full reasoning in
[ADR-1500](../../research/09-decisions/adr-1500-a-soundness-fix-is-not-pinned-until-a-control-dies-without-it.md).

**Reproduced the surviving mutant, and found the measurement was aimed at the
wrong suites.** In an isolated snapshot with the guard's first conjunct
replaced by `false`, all three suites the coordinator ran survive —
`kernel_seam_fuzz`, `mutual_inductive_group_grammar` and
`nested_inductive_grammar` each report **1 passed, exit 0**. But
`cargo test -p axeyum-lean-kernel --lib inductive` **does** die: ADR-1495 had
landed `reject_ctor_field_universe_above_result_universe`, which the
three-suite sweep did not include. So the guard was pinned by exactly one test
and nobody had shown it. The generators survive because ADR-1495's own fixture
change moved their `Type` families from `Sort 1` to `Sort 2`, so they now emit
only Lean-legal shapes.

**The one pinning test measured less than it looked.** It carried the rejection
and both admission controls in a single `#[test]`, so it dies on its first
assertion and the admission controls are unreachable in the only configuration
where their answer matters. Split into eight, each reported with AND without
the guard:

| control | with | without |
| --- | --- | --- |
| `reject_ctor_field_universe_above_result_universe` | pass | **FAIL** |
| `reject_ctor_field_universe_above_result_universe_polymorphic` (new) | pass | **FAIL** |
| `admit_sort1_field_under_sort2_family` | pass | pass |
| `admit_bundled_sort2_structure_with_sort1_carrier` (new) | pass | pass |
| `admit_nat_like_family_baseline` (new) | pass | pass |
| `admit_prop_family_with_sort1_field` | pass | pass |
| `prop_exemption_is_sound_because_large_elimination_is_denied` (new) | pass | pass |
| `positivity_prepass_precedes_the_universe_check` (new) | pass | pass |

`--lib inductive` baseline: **56 passed, 0 failed** (was 49).

**Nothing checked that `Prop`'s exemption is sound rather than present.** It is
sound because a *separate* mechanism — `allows_large_elimination`'s
`exposes_non_prop_fields` arm — denies large elimination to a `Prop` family
carrying a non-proof field, so the second half of the Girard construction is
unavailable. No test connected the two. It does now, with a fieldless
`True`-like `Prop` singleton (which DOES get large elimination) as the
non-vacuity control. This is mutation testing's documented blind spot exactly:
the connection between two correct mechanisms is not a guard, so there was
nothing to delete.

**The check order is the reverse of what the tree says.** A test asserting the
universe check precedes positivity was written and the kernel refuted it:
`check_group_constructor_positivity` is a whole separate pre-pass over every
constructor, so it masks the universe error even when the universe-illegal
field comes FIRST (`field_index: 1`, the non-positive one, for a constructor
whose field 0 is universe-illegal). Recorded as an ordering control.

**Registered in `scripts/tests/mutation_controls.py` as
`inductive-universe-guard`** — the harness does cover Rust, via its `Cargo`
runner through `scripts/cargo-serialized.sh`. Two mutations failing in opposite
directions: guard made dead kills 2 tests, `Prop` exemption dropped kills 6.
Re-run the whole measurement with
`python3 scripts/tests/mutation_controls.py inductive-universe-guard`.

**Deferred, with a design: restoring illegal coverage to the grammar
generators.** They once emitted 360 Lean-illegal cases asserting ADMIT and now
emit none; neither is right. Not done here because
`mutual_inductive_group_grammar` pins a byte-exact fnv1a64 digest over all 360
descriptors — regenerating it in the commit that changes it is the
"editing a file that pins its own digest" failure — and because the positivity
pre-pass makes the sort axis and the positivity axis non-independent, so
`expected_error` becomes order-dependent. ADR-1500 §Decision 3 carries the
design.

**Over-refusal, checked against the eleven preludes rather than argued.**
A guard in `add_inductive` sits in the path of all 98 `add_inductive` call
sites, so refusing too much would break everything at once:

    cargo test -p axeyum-lean-kernel --lib prelude_builds
    -> 8 passed, 0 failed, finished in 191.65s

`clippy -p axeyum-lean-kernel --all-targets -- -D warnings` exits 0. Note
that clippy caught an `items_after_statements` defect in a new test that
all 56 tests passed over, both before and after — the same class that
caught a detached `#[test]` attribute earlier this week, and one no test
count can see.

**DID NOT RUN:** `cargo test -p axeyum-lean-kernel --lib` (the whole
1,318-test crate sweep). Started, reached `running 1318 tests`, and was
SIGTERMed at the harness timeout — **exit 143, killed, not a failure**. The
bounded `prelude_builds` and `inductive` filters above are what ran to
completion; the full sweep is for the coordinator's pre-merge gate.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `1e33d51ee` | Split ADR-1495's bundled universe-guard test into seven named controls so each admission control is observed in the configuration whose answer it gives; added the polymorphic refusal, the bundled-structure and Nat-like admissions, and the `Prop`-exemption soundness control. `--lib inductive` 49 -> 55 passed. |
| 2026-09-01 | `d9b9249d9` | Ordering control (the positivity pre-pass masks the universe error, refuting the assumption this lane started with); registered `inductive-universe-guard` in `scripts/tests/mutation_controls.py` (baseline green 56 tests, both mutations killed, disjoint kill sets); ADR-1500. |
