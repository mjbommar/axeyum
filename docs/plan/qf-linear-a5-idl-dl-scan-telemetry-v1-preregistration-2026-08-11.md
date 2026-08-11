# QF linear A5 IDL DL scan telemetry v1 preregistration — 2026-08-11

**Passed and retained.** All four cases were result-invariant and exposed stable
counts; see the [result](qf-linear-a5-idl-dl-scan-telemetry-v1-result-2026-08-11.md).

## Need

The [extended-slice result](qf-linear-a5-idl-extended-dl-slice-v1-result-2026-08-11.md)
rejects inference from fallback DPLL atom counts to DL scan structure. The
unchanged route decides both losses with more time, but BubbleSort did not match
the first structural predicate. Another budget policy without actual scan data
would be benchmark-driven guesswork.

## Authorized increment

Add deterministic post-scan counts to the existing `dl-online` timeout detail:

- distinct difference atoms;
- numeric equality gates;
- Boolean equality gates;
- encoded variables; and
- materialized clauses when those structures exist at the timeout site.

Use one stable field order and report only counts already computed by the
route. Do not add a clock read, traversal, allocation-sized clone, filename,
logic label, verdict-dependent branch, public API, schema version, or new
solver state. Do not change scan/encoding/search order, timeout selection,
model replay, conflict checking, or any solver result. Sites reached before a
count exists must omit that field rather than fabricate zero.

Focused tests must verify exact detail for a bounded timeout after scan and
that SAT/UNSAT outcomes and zero-budget refusal remain unchanged. Strict
all-feature solver Clippy and the complete solver library must pass.

## Measurement gate

Build one exact release binary and run the shipped 24,000 ms setting once each
on BubbleSort, GraphPartitioning, `lpsat-goal-18`, and the retained maze gain,
then repeat only unstable count records. Compare verdict and terminal route to
the unchanged exact binary; the only permitted JSON difference is appended
timeout-detail telemetry. Use fresh 8 GiB workers, zero stderr, exact identity,
and group-start load at most 12.

This increment may be retained as route observability after focused/full tests
and ADR-0375 documentation, but its counts authorize no budget change. A later
candidate needs a new preregistration, target/control matrix, all 173 retained
QF_IDL/QF_RDL decisions, allocation controls, and a complete exact-pushed gate.
