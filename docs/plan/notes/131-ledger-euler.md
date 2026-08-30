# Notes: 131-ledger-euler

Detail moved out of [`../status/131-ledger-euler.md`](../status/131-ledger-euler.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Mutation-tested in an isolated `/data0` snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout): renamed
`CReal.integral`'s display string to `"integral_MUTATED"` at
`crates/axeyum-lean-kernel/src/creal.rs:4389`, rebuilt, and confirmed the
`--require-declaration CReal.integral --require-kind definition` check
returns count 0 / exit 1, while the SAME rebuild's check for an unrelated
control (`CReal.e`) still returns count 1 / exit 0, and a check for the new
name `CReal.integral_MUTATED` correctly returns count 1 / exit 0. Restored
the source before building the real change. `F:creal-integral`'s
`kernel-CReal.integral` evidence row was upgraded from the indirect route
(via `CReal.integral_const`'s own admission) to this direct checker; its
`notes` record the upgrade and the mutation test.

**Task 2 — registered 14 new facts:**
`F:creal-e` (the construction itself — via `CReal.mk` on an explicit
`speedup`/`diagonal` regular sequence, **never** `Exists`-elimination, since
an eliminated existential witness cannot be extracted as data for `CReal.mk`
to consume), `F:creal-e-converges`, `F:creal-two-le-e` (the EVENTUAL-bound
case: `expSeriesPartial 0 = 0 < 2`, so `converges_lower_bound_shift` at
shift 2 is load-bearing), `F:creal-e-le-three` (a genuine `{0, 1, k+2}` case
split at the mathematical kink, not an artifact), `F:creal-e-le-four` (one
uniform bound at every `n`, deliberately registered alongside `e_le_three`
to record the contrast the source module's own doc calls out),
`F:creal-expterm-le-geom`, `F:creal-expdominantcauchy`,
`F:creal-cauchyofpointwiseequiv` (the domination-bridge triple named in this
lane's brief), `F:creal-geomcauchy` (base-1/2 geometric Cauchy — NOT the
general-base `geomCauchyOfLt`, which lives on an unmerged sibling branch and
is deliberately excluded), `F:creal-sumrange-comparisontest` (comparison
test for nonnegative series), `F:creal-sumrange-cauchy-of-dominated` /
`F:creal-sumrange-converges-of-dominated` (dominated convergence, Cauchy and
Converges forms), and `F:creal-sumrange-cauchy-of-abs-cauchy` /
`F:creal-sumrange-converges-of-abs-converges` (absolute convergence implies
convergence — what makes the comparison/ratio tests usable on a signed
series). Chapter 21 (`e` irrational) and `geomCauchyOfLt` were NOT registered,
per this lane's scope.

Canonical types were read from the kernel via a standalone probe binary
(`axeyum-lean-kernel` path dependency, public `Kernel` API only — `environment()`,
`display_name()`, `render_lean()`, `axiom_footprint()`, `theorem_dependencies()`
— built in the session scratchpad, deleted after use) and every
`formal.statement` field is programmatically constructed from that probe's
own JSON dump rather than hand-retyped, specifically to eliminate
transcription-error risk in these deeply nested Pi types (verified by a
second script comparing every fact's `formal.statement` against the probe's
raw output byte-for-byte). `depends_on` links to existing ledger facts (and
to the other 13 facts registered in this same batch) wherever
`theorem_dependency_inventory` names one; every unregistered prelude
dependency is named in the fact's own `notes` rather than registered
speculatively. `axiom_footprint: []` for all 14, confirmed via
`nat_axiom_inventory --include-constructed --require-axiom-free creal`
(`creal: axiom=0 opaque=0 quotient=0 total_trusted=0`).

Every one of the 14 `kernel-term` checker commands was run and verified to
print count 1 / exit 0 on this tree before being written into a fact file.
`python3 scripts/validate-facts.py` is green: **722 facts, 0 errors**
(708 before this batch + 14 new).

Nothing under `crates/axeyum-lean-kernel/src/` was touched except the new
`--require-declaration` flag on the EXAMPLE
`crates/axeyum-lean-kernel/examples/kernel_declaration_projection.rs`
(Task 1's own scope) — four lanes were live in `creal/geometric.rs`,
`creal/exponential.rs`, `creal/trig.rs`, `creal/crossing.rs`, and `complex/`.
