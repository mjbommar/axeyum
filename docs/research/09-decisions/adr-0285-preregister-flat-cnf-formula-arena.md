# ADR-0285: Preregister a flat CNF formula arena

Status: proposed
Date: 2026-07-19

Result state: preregistered; implementation and corpus observation have not
started

## Context

The surviving publication thesis is correctness, deployability, proofs, and a
measured performance regime rather than blanket solver speed. The remaining
cold one-shot engineering target is nevertheless clear on the accepted
Glaurung client population: bit lowering plus CNF encoding account for about
84% of Axeyum's cold pipeline, while SAT search is only about 15%.

ADR-0200 rejected a primary fingerprint-table replacement at an 8.55% CNF
regression. ADR-0259 through ADR-0277 then attributed and closed the fixed
duplicate-generation lane without an accepted optimization. A new research
note identifies retained clause storage as an independent mechanism:
`CnfFormula` owns `Vec<CnfClause>`, and every `CnfClause` owns a separate
`Vec<CnfLit>`. The accepted representative encoding retains 271,991 clauses,
almost all empty through ternary.

The code audit sharpens that hypothesis in two ways. First, `clauses()` is a
publicly consumed surface used across 27 Rust files, so this is not a private
field swap. Second, `TseitinEncoder::add_encoded_clause` creates a fresh
canonicalization `Vec` per attempt; changing retained storage while preserving
that temporary would not remove the hot allocation pattern. Conversely, the
proof SAT core already repacks `CnfFormula` into one literal arena plus headers,
showing that the representation is useful but currently paid for only after a
fragmented formula has been built.

The research note reports favorable standalone arena microbenchmarks, but its
named `scratchpad/clausedb-proto` reproduction directory is absent from the
current checkout. Those ratios motivate this preregistration; they are not
accepted or publishable evidence. Only the in-tree gates below can select the
change.

## Decision

Test one production representation change:

- store all formula literals in one ordered `Vec<CnfLit>`;
- store one monotone `u32` end offset per clause, so clause `i` is the slice
  between the previous and current end;
- reject a formula whose total literal count cannot be represented exactly by
  that offset type with a new stable `CnfError` rather than truncating;
- keep `CnfClause` as the owned construction/export value, but expose borrowed
  formula clauses as an exact-size deterministic iterator of `&[CnfLit]` plus
  indexed `clause(index)` and `clause_count()` access;
- migrate every in-tree consumer explicitly, including DIMACS, RustSAT/BatSat,
  proof production/checking, LRAT/Alethe/interpolation, simplification,
  vivification, XOR routes, solver statistics, and benchmark examples; and
- give the one-shot Tseitin encoder one reusable canonical-clause scratch
  buffer. Clear and reuse it for each attempt, then fingerprint, compare, and
  append the slice into the authoritative formula arena.

The formula remains append-only and deterministic. Clause order, literal order,
empty clauses, duplicate handling, fingerprints, collision buckets, AIG/CNF
maps, roots, assignments, proof input, and model replay do not change. Do not
touch the accepted fingerprint map, AIG unique table, encoding rules, SAT core,
rewrites, or solver policy.

The arena is the production representation if accepted; the existing
`--profile-cnf-construction` switch reports additive storage diagnostics but is
not a runtime legacy/arena toggle. A toggle would either retain both layouts or
put policy branches on the hot path. Baseline and candidate timing therefore use
distinct prebuilt commits.

Add deterministic profiled fields for formula clause/literal counts, logical
arena bytes, arena capacity bytes, and the prior representation's logical lower
bound (outer `CnfClause` storage plus exact literal payload, excluding allocator
metadata and spare capacity). The logical arena must use at most 80% of that
conservative prior lower bound on both native and wasm32 layouts. Capacity and
process RSS are reported separately; logical bytes are not relabeled as RSS.

## Pre-observation acceptance gates

Tests begin red and then require:

1. empty, unit, binary, ternary, and larger clauses preserve exact ordered
   iteration, indexed access, cloning, equality, evaluation, and DIMACS;
2. invalid variables and unrepresentable total literal counts fail with stable
   typed errors before mutating the formula;
3. deterministic structured formula generation agrees with a test-only
   `Vec<Vec<CnfLit>>` oracle for clause content, evaluation, and DIMACS;
4. ordinary and profiled Tseitin encoders remain byte-identical in formula,
   roots, bindings, assignments, and all pre-existing construction counters;
5. the reusable scratch covers constants, tautologies, repeated literals,
   duplicates, forced fingerprint collisions, and clauses larger than its
   initial capacity without cross-attempt contamination;
6. BatSat SAT assignments replay on the arena formula, while DRAT, LRAT,
   Alethe, interpolation, simplification, vivification, BVE, XOR, and
   incremental routes retain their existing focused gates;
7. storage diagnostics satisfy their internal accounting and the <=80%
   logical-byte gate on a formula with ADR-0259's observed clause-size mix;
8. all workspace tests, formatting, strict Clippy, strict rustdoc, and link
   checks pass; `axeyum-cnf`, `axeyum-solver`, and `axeyum-bench` pass their
   no-default/QF_BV builds; and
9. both ordinary and SIMD-enabled wasm32 `qfbv` builds compile without a native
   dependency. This ADR does not claim a wasm speedup from compilation alone.

Implementation and tests must be committed before any corrected-wide-v3 query
is run through the candidate. A failure rejects the candidate without timing.

## Fixed structural observation

After the pre-observation commit, run exactly one clean detached profiled
process over the accepted corrected-wide-v3 representative population:

- manifest SHA-256 `7818686b...`;
- 162 queries: 88 SAT and 74 UNSAT;
- families 36 arithmetic, 12 comparison, 7 mixed, 52 register-slice, 54
  slice-partial, and 1 trivial;
- raw/rewrite-off `sat-bv`, in-process Z3, one job;
- 10,000 ms wall, 2,000,000 BatSat progress checks, 300,000 term nodes,
  3,000,000 CNF variables, and 8,000,000 CNF clauses; and
- 100% decided, manifest/Z3 agreement, and all SAT original-model replays.

The candidate must reproduce ADR-0259/0276's exact aggregate construction
population: 396,270 attempts, 5,019 tautologies, 119,260 exact duplicates,
271,991 emitted clauses, and every literal/length/probe/collision counter.
Every per-query AIG node, CNF variable, emitted-clause, outcome, and replay row
must match the accepted baseline. Its formula-literal count must equal the sum
of actual emitted clause lengths, every clause end must be monotone and in
bounds, and its logical storage ratio must pass the frozen <=80% gate. Any
failure rejects the candidate and forbids timing.

## Conditional unprofiled performance protocol

Only after the structural observation passes, compare the documentation-only
preregistration commit with the committed implementation using distinct
prebuilt release executables. Run six order-balanced pairs in the fixed sequence
`B,C,C,B,B,C,C,B,B,C,C,B` over the same 162 queries. Omit construction
profiling and otherwise preserve the structural run's corpus, backend, oracle,
worker count, and deterministic limits.

Fail closed unless every process has 162/162 decisions, 88 SAT replays, complete
manifest/Z3 agreement, no error/unknown/unsupported result, and identical
per-query AIG/CNF structure. Configuration, environment, corpus, linkage, and
order identities may differ only in the registered source and binary hashes.

For each pair, sum per-query `cnf_encode_ms` and `cold_total_ms`. Accept only if:

- the six candidate/baseline CNF ratios have geometric mean at most `0.97` and
  a deterministic paired-bootstrap 95% upper bound below `1.0`;
- neither baseline nor candidate CNF run-total CV exceeds 3%;
- no family with at least 5 ms aggregate baseline CNF time has a paired
  geometric mean above `1.02`; all smaller families are still reported;
- cold-total geometric mean is at most `1.0` with a paired-bootstrap 95% upper
  bound at most `1.02`; and
- candidate process peak RSS is no more than 5% above paired baseline.

The total-CNF gate is the selection criterion. A faster scratch microbenchmark,
lower logical bytes, or a favorable point estimate cannot rescue a failed
correctness, identity, variance, family, total-time, or RSS gate. Do not rerun
to select a quieter sample or combine this with another optimization. On
rejection, restore the prior representation and retain the ADR and measurements
as negative evidence.

## Consequences

If accepted, Axeyum removes per-clause retained allocation and repeated
canonical-clause allocation from the one-shot CNF path while preserving the
trusted AIG-to-CNF contract. The same representation also avoids proof-SAT's
initial repack from a fragmented formula, but proof performance is not a claim
without a separate measurement.

This is a cold-path engineering result, not a new algorithm or publication
headline. It does not reopen the rejected duplicate-clause population, change
warm policy, soften strict IR errors, alter proof assurance, or imply native or
WASM leadership. LLVM memory semantics remain a separate Track 5 prerequisite.

## References

- ADR-0200, ADR-0259, and ADR-0276--0277.
- `docs/research/08-planning/cold-path-data-structures.md`.
- `docs/research/08-planning/benchmarking-and-performance-methodology.md`.
- Varisat's clause-storage design and CaDiCaL/Kissat's contiguous clause-memory
  precedent, used as design references rather than dependencies.

## Alternatives

- Keep the outer formula fragmented and flatten only at the solver handoff:
  rejected because the proof core already does this and pays both layouts.
- Change only `CnfFormula` while retaining a fresh Tseitin `Vec` per attempt:
  rejected because it preserves the hot allocation mechanism.
- Use inline small clauses instead of an arena: not selected because it is a
  different representation from the PLAN-selected contiguous-storage
  hypothesis and would require its own preregistration.
- Add a runtime legacy/arena switch: rejected because it contaminates the hot
  layout or branch path; distinct commits are the clean control.
- Combine the arena with fingerprint, AIG, or encoding changes: forbidden by
  the isolated measurement contract and ADR-0200/0277 negative evidence.
