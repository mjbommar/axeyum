# ADR-0013: Uninterpreted Functions (EUF) in the IR, via Ackermann Reduction

Status: accepted
Date: 2026-06-13

## Context

The north star is a complete reasoning framework, and its theory-combination
rung (Nelson-Oppen / CDCL(T)) presupposes the theory of equality with
uninterpreted functions (EUF). EUF is also directly useful for the
symbolic-execution consumer: abstracting an unmodeled subroutine, hash, or
syscall as an uninterpreted function `f` keeps congruence (`x = y → f(x) = f(y)`)
without committing to a bit-precise model. The open research question "Should
uninterpreted functions be first-class early?" has been outstanding since the
first IR.

The array track ([ADR-0010](adr-0010-arrays-via-eager-elimination.md)) already
built an **Ackermann reduction** for `select` over array variables. EUF is the
same machinery generalized: a distinct application `f(t)` becomes a fresh
variable, and every pair of applications of the same function gets a consistency
constraint `args_i = args_j → f_i = f_j`. Reusing that pattern lets EUF land
without a new solving paradigm, and without painting the IR into a
quantifier-free corner.

## Decision

Add uninterpreted functions as a **first-class IR construct**, eliminated to
`QF_BV` by Ackermann reduction before lowering (the eager strategy proven for
arrays). This is sub-increment 1: the IR and evaluator. Later sub-increments add
the elimination pass, a first-class solver API, scenarios, and SMT-LIB I/O —
mirroring the array rollout.

- **Function declarations are separate from variables.** A function has a
  *signature* (scalar parameter sorts → scalar result sort), not a sort, and is
  not a first-class term — there is no function-sorted value and no higher-order
  use. The only way to use one is an application. New IR surface:
  `FuncId`, `TermArena::declare_fun` / `apply` / `function` / `functions`,
  `find_function`, and the operator `Op::Apply(FuncId)`.
- **Arguments and results are scalar** (`Bool` or `BitVec`). Array-sorted
  parameters/results are rejected at declaration. This keeps interpretations
  finite and keys uniform; lifting the restriction is future work if a concrete
  need appears.
- **Interpretations live in the model, keyed by `FuncId`.** `FuncValue` is the
  EUF analog of `ArrayValue`: a default result plus a normalized map from
  argument tuples to results, with arguments/results encoded to `u128` (a `Bool`
  as `0`/`1`, a `BitVec` masked to width). The ground evaluator interprets
  `Op::Apply` against `Assignment::function`, so EUF is part of the executable
  semantic reference. An application with no bound interpretation is an
  `UnboundFunction` error, never a silent default.
- **The Z3 oracle rejects `Op::Apply` during translation** (as it already does
  for array terms): UF is eliminated before the oracle is consulted, so the
  oracle never needs native UF. This keeps the oracle's role unchanged
  (ADR-0002).

## Evidence

- The evaluator now interprets `Op::Apply` against a `FuncValue`; an exhaustive
  width-3 test confirms the defining congruence property
  (`x = y → f(x) = f(y)`) holds under an arbitrary deterministic interpretation,
  which is exactly what the Ackermann constraints will encode.
- Interning is preserved: `f(x)` and `f(x)` are the same `TermId`, so the
  reduction sees one application per distinct argument tuple (the basis for the
  pairwise consistency constraints).
- Sort/arity checking is enforced at build time (`ArityMismatch`,
  `SortsDiffer`, `FunctionSignatureConflict`), consistent with the
  no-invalid-runtime-value rule.

## Alternatives

- **Lazy / on-demand congruence (a congruence-closure decision procedure).**
  The eventual CDCL(T) target, but a different paradigm; deferred until eager
  Ackermann blow-up is measured on a real corpus — the same priority gate the
  array track accepted.
- **Functions as first-class function-sorted values.** Rejected: it forces a
  function sort, complicates the evaluator and bit-blaster, and reaches toward
  higher-order logic before the finite-domain core is complete.
- **Native Z3 uninterpreted functions on the oracle path.** Unnecessary while
  elimination happens before solving, and it would expand oracle reliance
  against ADR-0002.

## Implementation Progress

- 2026-06-13: sub-increment 1 (IR + evaluator) shipped — `FuncId`,
  `Op::Apply`, `declare_fun`/`apply`, `FuncValue`, and evaluator support, with
  congruence verified exhaustively at width 3.
- 2026-06-13: sub-increment 2 (elimination + solving) shipped —
  `axeyum_rewrite::eliminate_functions` reduces `QF_UFBV` to `QF_BV` by
  Ackermann congruence reduction with `FuncValue` model projection, and
  `axeyum_solver::check_with_function_elimination` is the first-class entry
  point (eliminate → `SatBvBackend` → projected interpretation → original-query
  evaluator replay). `Model` now carries function interpretations. End-to-end
  `QF_UFBV` tests cover congruence-forced `unsat`, replayed `sat`, and binary
  functions — all oracle-free.
- 2026-06-13: SMT-LIB I/O round-trip completed — the parser accepts n-ary
  `declare-fun` (scalar signatures) and function applications (builtins keep
  priority over declared names, matching SMT-LIB reserved words); with the
  existing writer this gives a parse → write → parse round-trip for `QF_UFBV`.
- 2026-06-13: `QF_AUFBV` theory composition shipped —
  `axeyum_solver::check_with_arrays_and_functions` runs array elimination then
  function elimination, projects the model back through both passes (functions
  first, since a `select` index may mention a function application), and replays
  against the original mixed query. Oracle-free end-to-end tests cover
  cross-theory congruence `unsat` (`mem[i] = v ∧ f(v) = aa ∧ f(mem[i]) ≠ aa`),
  store-then-apply `sat` with replay, and distinct outputs over distinct loads.
  This is the first two-theory composition (the eager precursor to a general
  combination framework).
- 2026-06-13: `QF_UFBV` scenarios shipped — a `Family::Function` in
  `axeyum-scenarios` with `function_chain` (nested applications),
  `function_lookup` (unary, deliberate argument collisions exercising
  congruence), and `function_binary_merge` (two-argument map), plus a
  `function_catalog`. Each is satisfiable by construction with the function
  table carried as the witness (the existing SAT self-check path verifies it),
  and the solver-crate differential test decides the whole catalog through
  `check_with_function_elimination`, oracle-free. The EUF rollout now matches the
  array track: IR, evaluator, elimination, solver entry point, SMT-LIB I/O,
  scenarios, and `QF_AUFBV` composition. Array *equality* remains the one
  deferred theory feature.

## Consequences

- The IR can express `QF_UFBV` (and, combined with arrays, `QF_AUFBV`); the
  evaluator is a complete semantic reference for it, so `sat` models remain
  replayable end to end once elimination and model projection land.
- The Ackermann machinery is now needed in two places (arrays, UF); a later
  refactor may share it, but the array pass stays as-is until the EUF
  elimination pass exists to compare against.
- The deferred array-equality cases and EUF together motivate a shared
  extensionality/congruence story; that remains future work.
