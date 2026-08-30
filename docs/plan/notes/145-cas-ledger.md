# Notes: 145-cas-ledger

Detail moved out of [`../status/145-cas-ledger.md`](../status/145-cas-ledger.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Taylor is materially weaker on the kernel side, and the fact says so in
its evidence notes, not a footnote.** `crates/axeyum-lean-kernel/src/rat_prelude/taylor.rs`'s
`Rat.taylor_deg1` is degree `<= 1` only (`n = 0`), carries **no remainder
term**, and produces **no witness `xi`** — it establishes only that a
degree-`<=1` polynomial equals its own linear approximation. The CAS
certificate this fact registers is general-degree, carries the exact Lagrange
remainder, and names `xi` as a genuine `AlgebraicReal`. `F:cas-taylor-quartic-lagrange-witness`
states this explicitly in its evidence row's `notes` and does **not** claim a
kernel-reconstructed sibling the way the IVT sign-bracket fact does — there is
no partial reconstruction to claim here, and pretending otherwise is exactly
the failure ADR-0601 exists to prevent.

MVT and EVT (extremum) each have kernel-side family members
(`creal/fermat.rs`, `creal/extreme_value.rs`) — but those are rows 1/2 of the
*graded* family, about arbitrary uniformly-continuous functions, and are
either a hypothesis-taking theorem (Fermat) or a refutation of the general
case (EVT attainment). Neither reconstructs the CAS's specific
this-polynomial-on-this-interval claim, and both facts' notes say so
explicitly rather than let the reader infer a bridge that does not exist.

## Checkers: all four executed, all four shown able to fail

**Executed, not sampled: 4 of 4 checker commands run**, each confirmed to
match exactly 1 test (`grep -c` on the emitted `... ok$` line), never 0:

```
mvt::tests::cubic_irrational_witness_x_cubed_on_0_3          count=1
extremum::tests::irrational_argmax                            count=1
taylor::tests::quartic_irrational_witness                     count=1
partial_fractions::tests::mixed_general_case                  count=1
```

`scripts/cargo-serialized.sh test -p axeyum-cas --lib`: **802 passed, 0
failed, 5 ignored** (baseline unchanged by this lane — no CAS source was
touched, per scope).

**Failure demonstrated in an isolated `scripts/lane-snapshot.sh HEAD` tree**
(`/data0/axeyum/scratch/snap-cas-ledger-0222e711c`, deleted after use), never
the shared checkout. `mvt.rs`'s producer-side `pa` evaluation was mutated to
evaluate at `a+1` instead of `a` (asymmetric: `verify_mvt_certificate`
recomputes `pa` independently from `poly`/`a` in its own code, so this breaks
only the producer's stored `slope`, not the checker's recomputation):

```
mvt::tests::cubic_irrational_witness_x_cubed_on_0_3   MUTATED  -> FAILED
  assertion `left == right` failed
    left: Some(false)
   right: Some(true)

extremum::tests::irrational_argmax                    control  -> ok
taylor::tests::quartic_irrational_witness             control  -> ok
partial_fractions::tests::mixed_general_case          control  -> ok
```

The three controls, run in the **same mutated tree**, confirm the failure is
the mutation, not a broken build. First attempt at this mutation (negating
the slope computation's `checked_sub` to `checked_add`) was a **false
negative**: `a=0` in the chosen instance, so `pb + p(a)` and `pb - p(a)` are
identical when `p(a)=0`, and the checker passed unchanged — recorded here
because it is exactly the "ask what the command prints if broken" trap this
repository's CLAUDE.md names, caught before being reported rather than after.

## Ledger numbers, before and after

```
validate-facts.py:      1,379 facts, 0 errors  ->  1,383 facts, 0 errors
  cas-certificate:       25 total (kernel-reconstructed=1, cas-internal=24)
                     ->  29 total (kernel-reconstructed=1, cas-internal=28)
gen-ledger-coverage.py:  kernel_theorems=1418 registered=1026 curated=474
                     ->  kernel_theorems=1418 registered=1026 curated=474  (UNCHANGED)
```

**`curated` did not move, and it is correct that it did not — not merely
"did not move for the wrong reason."** `gen-ledger-coverage.py`'s `join()`
skips any fact whose `proof_route` is not in `KERNEL_ROUTES = {"kernel-lean"}`
before it ever reaches the curation check (`scripts/check-fact-depends-derived.py`).
All four new facts are `proof_route: cas-certificate`, so they are invisible
to that script's counters by construction — this is not a special case
handled for this lane, it is the pre-existing behavior of a script scoped to
kernel-lane coverage specifically. No `provenance.curation` or
`provenance.generated_by` was stamped on any of the four (per this task's
explicit instruction); they are hand-written and would count as curated
*if* they were on a kernel route, which they are not.

`gen-ledger-coverage.py`'s numbers moved once, incidentally, while this fact
file was open to a temporary re-run of the script: `kernel_theorems`
1411→1418 (the merges this lane pulled in at the start — `CReal.meshMax_mono`,
`CReal.meshMax_step_le`, new `Rat.*` theorems — landed real kernel content
between the pre-merge and post-merge measurement). That regenerated
`artifacts/ledger-coverage.json` was reverted (`git checkout --`) rather than
committed: it is not in this lane's scope (facts + this status file only) and
regenerating/committing it is a different lane's call to make.

## What ADR-0601 left underspecified, applied to a real result

The ADR was written before any of these four modules existed, and applying it
surfaced one real gap and one non-gap:

1. **Gap: the ADR's `classify_cas_certificate_checker` machinery (added to
   `validate-facts.py` for the IVT facts) is generic and worked unchanged for
   all four new modules** — this is a non-finding, recorded because it was
   worth checking rather than assuming: the classifier keys only on which
   Cargo package a `cargo test`/`cargo run` segment names, so it needed no
   awareness of `mvt`/`extremum`/`taylor`/`partial_fractions` specifically.
2. **Real gap: ADR-0601 SS2 describes the split as "the bridge, starting with
   the polynomial-identity slice landing against `Complex.polyEval`/`polyMul`"**
   — i.e. it anticipates ONE bridge project covering CAS-certificate facts in
   general. What this lane found is that the four modules are **not equally
   far from a bridge**: `partial_fractions.rs`'s own module doc states it
   "carries no analytic content at all... a single linear algebraic identity,"
   while `mvt`/`extremum`/`taylor` all need a kernel-reconstructed Sturm
   root-count (sized, and still outstanding, in `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`'s
   own notes) as a shared prerequisite. The ADR's roadmap language does not
   distinguish "needs Sturm" from "needs only exact multiplication and a
   linear solve," and a future bridge lane choosing a next target should read
   `partial_fractions.rs` as the plausible **shortest** path to a second
   kernel-reconstructed `cas-certificate` fact, not equally-far alongside the
   other three. This is a finding about relative difficulty, not a defect in
   the ADR's decision — recorded here rather than silently assumed.

## Scope discipline

Touched only `artifacts/facts/F-cas-mvt-cubic-witness-sqrt3.json`,
`artifacts/facts/F-cas-extremum-irrational-argmax.json`,
`artifacts/facts/F-cas-taylor-quartic-lagrange-witness.json`,
`artifacts/facts/F-cas-partial-fractions-mixed-general-case.json`, and this
status file. `crates/axeyum-cas/` was read but not modified (the mutation
demonstration ran in a throwaway `lane-snapshot.sh` tree, deleted after use).
`artifacts/ledger-coverage.json`'s incidental regeneration was reverted.
`PLAN.md` and `docs/plan/global/` untouched.
