# ADR-0195: Skip empty warm-theory model projection

Status: accepted
Date: 2026-07-16

## Context

ADR-0194's exact Glaurung v6 profile attributes 165.192 of 175.049 ms
(94.37%) of incremental model lift to complete-model construction. The same
run reconstructs and completes only 5,066 symbol values, so the cost is not
value insertion. Source inspection finds that `complete_model_with_warm_theories`
always traverses every active original assertion to discover user array-select
terms, even when no active or one-shot warm array/UF projection work exists.

This is common in Glaurung's scalar QF_BV lineage stream. The solver must still
return a complete public model, validate the AIG assignment, and replay every
original assertion; omitting any of those would manufacture an unsound or
incomparable speedup.

## Decision

After `complete_model_filtered` has constructed the same deterministic public
model and default-completed every inhabitable user symbol, return it directly
when all active and one-shot warm projection inputs are empty. The gate checks
array selects, scalar UF applications, array-valued UF applications, array
equalities, and array relation flags in both retained frames and one-shot work.

Any non-empty class takes the unchanged full projection pipeline. The fast
path does not skip AIG recomputation, assignment reconstruction/validation,
model completion, cache replay, or original-term replay. It adds no public API,
configuration, allocation, nondeterminism, or persistent state.

## Evidence

The test was introduced red against the absent structural predicate. Its green
form proves an empty solver declines projection, one-shot select work requires
projection, retained UF work requires projection, and clearing those inputs
restores the empty case. A public incremental test proves the fast-path model
still carries the constrained value plus an unconstrained symbol's typed zero
default and evaluator-replays the original assertion.

All 877 all-feature library tests pass. Eighty focused all-feature incremental,
cache, structural-array, array-relation, array-valued-UF, and warm projection
integration tests pass, as does strict all-target/all-feature solver Clippy.
The broader integration run was stopped in unrelated long quantified-evidence
targets after every completed target passed; it is not claimed as a complete
workspace gate.

On the exact 2,551-check v6 SurfacePen stream, all outcomes, AIG/CNF structure,
path/cache traffic, model counts, and replay results are identical. Model
completion falls 165.192 to 1.088 ms (-99.34%), total model lift 175.049 to
10.379 ms (-94.07%), and profiled internal total 746.817 to 593.561 ms
(-20.52%). All checks decide and agree; unknown splits and replay failures are
zero.

An unprofiled same-current three-process baseline/candidate gate measures
median Axeyum time 636.6 to 474.6 ms (-25.45%), normalized ratio about 0.147x
to 0.108x Z3, and median RSS 83,480 to 83,428 KiB (-0.06%). Absolute Z3 drift
is +1.19%, below the 2% alarm. All 15,306 combined checks agree and exact warm
and cache traffic repeats.

The held-out NETwtw10 repetition confirms a smaller but material gain on the
large fallback-bearing stream. Across three same-current processes per side,
median Axeyum time falls 17,765.2 to 16,996.6 ms (-4.33%), normalized ratio
about 0.342x to 0.328x Z3 (-3.99%), and median RSS 261,428 to 257,796 KiB
(-1.39%); Z3 drift is -0.36%. All 170,136 combined checks agree, findings and
exact warm/cache traffic repeat, and replay failures remain zero. This causal
repetition does not itself replace the existing machine-readable lineage
artifact; regenerate that artifact separately from the accepted revisions.

## Alternatives

Skipping model completion or returning only constrained symbols was rejected:
public model completeness and original replay are solver correctness
contracts. Removing the second AIG validation pass was rejected by ADR-0194's
measurement; it is only 4.08% of model lift. Caching user-select discovery was
rejected because an exact emptiness predicate eliminates all such work without
new invalidation state.

## Consequences

Scalar QF_BV warm checks avoid a traversal whose cost grows with the retained
assertion prefix. Warm array/UF queries preserve the existing projection and
replay path exactly. Future projection classes must enter the gate in the same
change that makes them active; otherwise the empty-path proof would become
incomplete.
