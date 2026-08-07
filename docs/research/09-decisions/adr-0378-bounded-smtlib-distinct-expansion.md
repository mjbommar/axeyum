# ADR-0378: Deterministically bounded SMT-LIB `distinct` expansion

Status: accepted
Date: 2026-08-07

## Context

The SMT-LIB parser represents an n-ary `distinct(a_1, ..., a_n)` as the exact
conjunction of all `n(n-1)/2` pairwise disequalities. This is semantically
simple, but the previous implementation entered the quadratic loop without an
admission bound.

The preregistered A3 QF_NIA reference-only census exposed the failure on
`20210219-Dartagnan/ReachSafety-Loops/array_3-1-O0.smt2`. The 10,002,338-byte
source contains 99,421 top-level commands and 1,676,894 S-expression nodes;
raw iterative reading and all 99,414 preceding commands completed. Command
99,414 contains one 16,525-argument `distinct` over integer memory locations.
It requests 136,529,550 pair expansions, approximately 409 million equality,
negation, and conjunction nodes. Under the retained 8 GiB process envelope,
the term interner aborted while requesting a 4,362,076,176-byte allocation.
The same file reproduced the abort in isolation, so this was not cumulative
leakage from the census.

A wall-clock deadline alone cannot protect this path: one `apply_op` call can
allocate past the process envelope before control returns to a deadline poll.
An allocator abort is also not a first-class solver outcome and invalidates a
whole exact-list measurement.

## Decision

1. Admit at most 65,536 pairwise expansions for one parsed `distinct`. This
   retains every application through arity 362 (65,341 pairs), including the
   common 256-way all-different shape (32,640 pairs), and declines arity 363
   (65,703 pairs) before constructing the first pair.
2. Type-check every argument before shortcuts or admission. A repeated term is
   then exactly `false` and may return in linear work, even above the pair
   ceiling; it cannot conceal an ill-sorted later argument.
3. Materialize admitted disequalities into a balanced conjunction. The output
   depth is logarithmic in the pair count instead of a caller-controlled linear
   spine.
4. Add `SmtError::ResourceLimit` for deterministic ingest ceilings. The solver
   text front door maps it to `CheckResult::Unknown` with
   `UnknownKind::ResourceLimit`; the benchmark harness records an `unknown`
   resource-limit blocker. It is neither `Unsupported` nor a syntax/operational
   error.
5. Do not add a public n-ary `Distinct` IR operator in this repair. Such an
   operator would require evaluator, writer, rewriting, every backend,
   model-replay, and proof/evidence semantics before becoming public. The
   current exact lowering remains the supported representation within its
   explicit budget.

## Soundness and determinism

Below the ceiling, the formula remains the exact conjunction of every pairwise
disequality. Balancing changes only association. Duplicate short-circuiting is
valid because term interning gives structurally equal source terms one
`TermId`, but full sort validation runs first.

Above the ceiling, no partial conjunction is exposed and no verdict is
manufactured. The only outcome is `Unknown(ResourceLimit)`. The pair count is a
pure function of source arity, so admission is independent of machine speed,
available RAM, hash iteration order, or elapsed timing.

## Evidence

- The exact boundary regression parses arity 362 and rejects arity 363 with
  both the 65,703 demanded pairs and 65,536 limit in the diagnostic.
- A 16,525-occurrence duplicate regression returns exact `false` in linear work;
  a mixed-sort duplicate control still returns a type error.
- The solver-front-door regression observes `UnknownKind::ResourceLimit`, not a
  `SolverError`.
- The original Dartagnan row must return a bounded `unknown` under the exact
  8 GiB wrapper before the failed A3 census is restarted from row 1.

## Consequences

- Supported but over-budget `distinct` input is observable as resource-limited
  rather than unsupported or crashed.
- Raising the ceiling requires a measured memory/time A/B and an ADR update;
  available host RAM is not a reason to move it.
- A future compact all-different theory predicate remains possible, but it is a
  cross-layer feature rather than an ingest-safety patch.
- The aborted A3 trace is inadmissible. Because this repair changes parser
  policy after the original preregistration, the complete 67-row census needs a
  versioned re-preregistration at the fixed commit and a fresh row-1 run.
