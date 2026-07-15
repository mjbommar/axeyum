# ADR-0154: Record complete post-word QF_BV operator inventories

Status: accepted
Date: 2026-07-14

## Context

ADR-0153 reduces the accepted full Glaurung corpus from 15.64 to 14.11 seconds
and moves the Axeyum/Z3 ratio from 2.02x to 1.85x. Re-aggregating its five
artifact-v27 processes shows that the remaining excess is no longer owned by a
single family: `register-slice` contributes about 3.47 seconds above Z3 at
1.60x, while `slice-partial` contributes about 3.10 seconds at 2.95x.

Artifact v27 can attribute those rows to word processing, bit blast, CNF, SAT,
AIG outcomes, clauses, and the extract/concat/extension shapes needed by
ADR-0142. It cannot say which arithmetic, bitwise, comparison, shift, equality,
or `ite` applications survive the v3 word policy. Another rewrite selected from
lexical source counts would repeat the pre-ADR-0153 inference problem: an
operator may be frequent in the input yet disappear before lowering. GQ1
requires profiling the actual post-policy DAG before choosing GQ2--GQ6 work.

## Decision

Advance `axeyum-bench` to artifact version 28 and record a deterministic
operator inventory in both original and post-word query-shape snapshots.

- Count unique reachable DAG applications, preserving the existing
  sharing-aware traversal and stable manifest order.
- Classify every scalar Bool/QF_BV operator individually, grouped in JSON as
  Boolean, BV bitwise, BV arithmetic, shifts, comparisons, structural
  operators, and polymorphic equality/`ite`.
- Retain an explicit `other` bucket. A claimed QF_BV corpus can therefore show
  that every application was classified rather than silently dropping an
  unexpected theory operator.
- Publish both per-instance inventories and corpus totals. This permits exact
  family and slow-query aggregation without reparsing source text or expanding
  shared trees.
- Add per-instance distributions for add/sub, bitwise, comparisons, and `ite`
  to distinguish broad frequency from concentration in a few expensive rows.
- Keep the inventory observational. It neither changes rewriting/lowering nor
  enters Axeyum's reported cold pipeline time; it extends the query-shape walks
  that already run outside the measured word/bit/CNF/SAT boundary.
- Version-lock the regular gate and repeated-run consumers to v28 so a schema
  transition cannot be compared as if it were an identical experiment.

The next optimization remains unselected until a clean full v28 profile reports
the post-v3 inventory by manifest family. SAT tuning, broad relevant-bit
lowering, subtraction normalization, and further CNF ownership work remain
gated by that evidence.

## Evidence

The 31-test `axeyum-bench` suite covers every scalar Bool/QF_BV `Op` exactly
once, verifies the `other` bucket with an array operator, and checks that
sharing-aware query-shape summaries expose the new totals. Strict Clippy and
the 22 repetition/regular-gate Python tests pass under the 4 GiB cap.

The dirty-worktree semantic gate emits artifact v28 for both raw and canonical
policies and decides 128/128 representative queries with zero errors,
disagreements, or replay failures. Its canonical post-word inventory contains
7,019 applications and zero `other` operators. The largest surviving classes
are 3,326 equalities, 1,788 `ite`s, 1,008 `bvadd`s, 245 `bvult`s, 222 extracts,
and 193 zero extensions. These representative counts validate the schema; they
do not select the full-corpus optimization.

## Alternatives

- **Use lexical SMT-LIB counts again.** Rejected: they do not describe the DAG
  handed to the bit-blaster after v3 and overcount repeated source structure.
- **Add a one-off external parser script.** Rejected: it would duplicate Axeyum
  semantics, could not apply the exact Rust rewrite policy, and would not share
  the manifest/replay evidence boundary.
- **Record only corpus totals.** Rejected: Glaurung's residual is family- and
  outlier-concentrated; per-instance data is required to correlate operators
  with measured construction cost.

## Consequences

Artifact v28 files are larger because each instance carries two fixed operator
maps. In exchange, future Glaurung optimization ADRs can cite exact post-word
operator counts for the family and rows they target. Historical v27 artifacts
remain valid evidence for ADR-0143 through ADR-0153, but v27 and v28 repetition
series are intentionally not cross-compared as identical configurations.
