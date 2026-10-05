# Lane: int-divmod-witness — the second ADR-1721 slice: `eliminate_int_divmod`'s missing artifact

<!-- plan-section: lane-status -->

**Lane block (`WIP`, int-divmod-witness, 2026-09-07).** ADR-1721 §4 named
`eliminate_int_divmod` the sharpest remaining preprocessing gap and left the
*direction* of its `MAX_CONGRUENCE_GROUPS = 48` mode change open. It is now
established from the semantics rather than from the source comment (ADR-1730),
and the slice that follows from it is landed.

**The direction: the cap is a RELAXATION.** The zero-divisor congruence lemmas
are added conjuncts, so dropping them above 48 groups only enlarges the model
set. Therefore `unsat` transfers soundly at every group count — the cap can never
produce a wrong `unsat`, and the source comment's claim is correct — and the
direction that silently degrades is **`sat`**: above the cap the `_/0`
relaxation is no longer congruence-closed, so a satisfying assignment need not
induce a total `div(·, 0)` function and need not be a model of the original.

That matters because `dispatch_int_linear_refuters` is not only a refuter: it
runs `check_with_lia_simplex_within` and `check_with_lia_dpll` on the eliminated
form and returns their verdict — `Sat(model)` included — as the answer for the
original query.

**What landed.** `IntDivModElimination` replaces the bare `Vec<TermId>`: split
index (rewritten originals as a prefix, added constraints as the tail, so the
added count is a subtraction), the replacement map, and `ZeroDivisorCongruence`
(`NotApplicable` / `Closed` / `Omitted`) whose `sat_transfers()` is false exactly
for `Omitted`. `witness_int_divmod` interprets both halves the pass owes —
replacement and added constraints — under sampled concrete assignments with the
ground evaluator on the ORIGINAL term as the reference; it does not re-run the
transform. `guard_zero_divisor_sat` in `auto.rs` turns an `Omitted`-mode `sat`
into a first-class `unknown` naming the group count; `unsat` and `unknown` pass
through untouched at every group count.

**Teeth, measured on an isolated snapshot and reverted.** Mutating the Euclidean
remainder bound from `|c| − 1` to `c − 1` makes `solve` return `Unsat` on the
satisfiable `mod(x, −3) = 2` — a wrong `unsat` at the front door. **All 30 of the
30 solver tests that exercise this pass pass under that mutant** (`int_divmod` 7,
`lia` 10, `nia_divmod_linearize` 13), as do all 154 `axeyum-rewrite` lib tests;
the pass had no artifact, so nothing could reject it. Exactly one test catches
it: `witness_covers_a_negative_constant_divisor`. Deleting each of four guards in
turn killed exactly one test each, four different ones.

**Three defects found and fixed on the way**, all pre-existing: the pass iterated
`HashMap`s so its fresh symbol names and constraint order depended on per-process
hash seeding (determinism is a public API promise); `divisor.abs() - 1` overflows
at `i128::MIN` (debug panic, release silent weakening); and a group with only
`mod a c` emitted a constraint naming a fresh `q` that stood for no recorded
term, which the witness itself found on its first honest run.

**Not established:** that the `Omitted` mode is reachable through the front door.
Two probe shapes with 49–102 zero-divisor groups were either declined on the
lazy-arithmetic resource envelope or refuted correctly by an earlier route, so
`guard_zero_divisor_sat` was never observed to fire. It is defensive and cannot
regress a sound `sat`.

**Gates run in the worktree, all green with nonzero counts:**
`check --workspace --all-targets --all-features`; `clippy --workspace
--all-targets --all-features -D warnings`; `cargo test -p axeyum-rewrite` (154
lib + 27 integration); `-p axeyum-solver --lib --features full` **1468 passed**;
`--features full --test corpus_regression` 1; `--features full --test int_divmod
--test lia --test nia_divmod_linearize` 7+10+13; `--test progress_frontier
--features full -- --test-threads=1` 12 passed, no REGRESSION line.
**Did not run:** the workspace test sweep, `just check`, `check.sh`, the z3
differential fuzzes, and `gen-plan.py` (this lane was told not to regenerate
`PLAN.md`, so `check-merge-hygiene.sh` will flag it until the coordinator
regenerates).

**Next for whoever picks this up:** the same witness shape for
`eliminate_functions` (ADR-1721 §4 records it as an identical split); deciding
whether `guard_zero_divisor_sat`'s reachability is worth constructing a fixture
for, or whether the `_/0` route should move to the lazy-CEGAR UF congruence path
and retire the cap entirely; and retaining the ADR-0408 denotation guard's
verdict past the pass, which `auto.rs` still swallows as an ordinary decline.

<!-- plan-section: landed-changes -->

| 2026-09-07 | int-divmod-witness | `witness_int_divmod` + `IntDivModElimination` + `guard_zero_divisor_sat`: the pass reports its mode and both halves get interpreted, not re-derived; the wrong-`unsat` mutant passes 30 of 30 pre-existing tests and dies on exactly one of the new ones |
| 2026-09-07 | int-divmod-witness | ADR-1730: the `MAX_CONGRUENCE_GROUPS` cap is a relaxation, so the direction it silently changes is `sat`, not `unsat` |
