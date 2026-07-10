# ADR-0030: Incremental (lazy) arrays for symbolic memory

Status: accepted (eager route plus bounded retained structural-read slices; full warm lazy deferred)
Date: 2026-06-14

## Context

Symbolic execution and reachability are first-class use cases, and real programs
compute over **memory**: symbolic `load`/`store` (SMT-LIB `select`/`store` over
`Array`). The stack decides QF_ABV today by **eager** array elimination
(read-over-write + Ackermann, ADR-0010) — a one-shot rewrite to QF_BV before
bit-blasting.

That is exactly wrong for the incremental engine
([`IncrementalBvSolver`], ADR-0009) that symbolic execution drives: the
bit-blaster rejects `Op::Select`/`Store`/`ConstArray` (it expects arrays already
eliminated), so a symbolic-execution client cannot `assert` a `store`/`select`
into a warm, push/pop-scoped path condition. It must instead model memory as
bit-vectors itself (the shape `axeyum-scenarios::memory_trace` demonstrates) —
workable but it pushes the array decision procedure into every client and loses
the warm solver's reuse across path steps.

Eager elimination is also a poor fit incrementally on its own terms: a `store`
on a later path step produces a new array term that must be Ackermann-related to
selects from earlier frames, so the elimination is not local to one `assert` and
cannot be undone cleanly by `pop`.

This decides how arrays enter the incremental path; it is new public surface and
an architectural choice, so it is recorded here.

## Decision

**Add lazy array support to the incremental engine: keep `select`/`store` as
first-class terms in the incremental lowering, and discharge the array axioms
*on demand* as ordinary (selector-scoped) bit-vector lemmas, in the warm
solver.** Sketch:

- The incremental lowering treats a `select(a, i)` as a fresh bit-vector of the
  element width (an Ackermann-style placeholder), and a `store(a, i, v)` as a new
  array "version" handle — neither is bit-blasted structurally.
- Array semantics are enforced by **read-over-write** and **congruence** lemmas
  added lazily: on a `check`, if the current model violates an axiom (e.g. two
  selects `select(a,i)`, `select(a,j)` with `i = j` but different values, or a
  `select(store(a,i,v), j)` not respecting `i = j ? v : select(a,j)`), add the
  instantiated lemma as a scoped clause and re-check — the same lazy-relaxation +
  replay pattern already used for bit-vectors, datatypes, and NRA. Each lemma is
  guarded by the asserting frame's selector, so `pop` retracts it.
- Soundness is unchanged: every lemma is a valid array fact, and a `sat` model is
  still replay-checked against the original `select`/`store` terms by the ground
  evaluator (which already evaluates arrays). `unsat`/`unknown` stay first-class.

This makes incremental QF_ABV (and QF_AUFBV with the existing UF reduction) a
warm, push/pop capability — the memory model a symbolic-execution / reachability
engine needs — without abandoning the eager path, which stays the default for
one-shot QF_ABV.

## Evidence

- The lazy-relaxation-plus-replay pattern is proven three times in-tree (lazy
  bit-vector, datatype-native, NRA), and the ground evaluator already evaluates
  `select`/`store`, so the replay check needs no new trusted code.
- The eager eliminator (ADR-0010) gives a differential oracle: incremental lazy
  results can be cross-checked against eager one-shot results on the same query
  during validation.
- Symbolic execution is the stated first-class consumer; `axeyum-scenarios`
  already exercises memory traces, giving ready regression material.

## Alternatives

- **Re-run eager elimination per `check`.** Sound but throws away the warm
  solver's learned clauses every step and re-blasts the whole memory each time —
  defeating incrementality, the entire point of the symbolic-execution front end.
- **Push memory modeling into every client** (status quo). Works for bounded
  cases but duplicates array reasoning per consumer and can't reuse the solver's
  array lemmas across paths.
- **A native extensional array decision procedure** (weak/strong equivalence
  classes, à la a dedicated theory solver). The complete approach; deferred as
  much larger — the lazy-axiom slice lands the symbolic-memory use case first,
  exactly as eager elimination preceded any fuller array procedure.

## Implementation status

Landed 2026-06-14, a sound first slice (correctness before warm performance):
`IncrementalBvSolver` now **accepts** `select`/`store` assertions (deferred, not
bit-blasted) and decides them with `check_with_memory`, which re-solves all
active assertions one-shot via the validated eager elimination (read-over-write
+ Ackermann, ADR-0010) over the pure-Rust BV backend, with the usual `sat`
model-replay against the original `select`/`store` terms. The warm `check`
*refuses* active array assertions (sound — never silently ignores them) and
directs callers to `check_with_memory`. `push`/`pop` scope array assertions like
any other. Tested: read-over-write unsat-when-violated, a sat reachability query
with model replay, and the warm-path refusal.

**Still deferred (the warm path):** discharging the array axioms lazily as
selector-scoped lemmas over the warm CNF (reusing learned clauses across path
steps) per the decision above. The eager route makes symbolic memory *usable*
now; the lazy route makes it *fast* incrementally.

2026-06-27 update: the warm path now has its first retained array-read slice.
After the narrow syntactic memory simplifier, reads of the form `select(a, i)`
where `a` is a BV-indexed array symbol with Bool or BitVec elements and `i` is
array-free are abstracted to internal warm scalar variables. Same-array read
pairs get selector-scoped congruence lemmas, and SAT models are projected back
into concrete array entries before original-term replay (`ArrayValue` only for
BV arrays whose index and element widths both fit in `u128`; `GenericArrayValue`
for Bool arrays and any wide BV index or element, including BV256 storage
reads). This covers symbolic-base loads, predicate/set reads, and reducible ROW
tails whose remaining base read is a plain memory symbol. A scalar UF-app
sibling now handles Bool/BV applications the same way: `f(args)` is abstracted
to a retained warm variable, same-function applications get selector-scoped
congruence lemmas, and SAT models are projected back into `FuncValue` entries
before replay. Wide-BV UF signatures, including BV256 keccak-style
arguments/results, use full-value `FuncValue` entries instead of lossy `u128`
codes. Direct equality between supported array symbols is also retained as a
scoped warm theory fact: equal-array classes generate cross-array
select-congruence lemmas for committed assertions and one-shot assumptions, and
SAT models merge equal arrays before replay. Full lazy arrays/UF remain
deferred: arbitrary array terms, general extensionality/disequality witnesses,
ROW instantiation beyond the current simplifier, non-BV indices, non-Bool/BV
element arrays, non-scalar or infinite-domain UF applications, and learned
theory-clause reuse across the whole array/UF engine are still open.

2026-07-10 update: ADR-0086 retains the first structural read semantics. Reads
over supported store, constant-array, and array-ITE parents receive private
scalar owners whose exact definitions are installed once in the persistent CNF.
Scoped user roots retract normally, only direct symbol leaves project models,
and original replay gates SAT. Exact 512-node/256-depth limits and 192 warm/
check-auto/Z3 comparisons validate the slice. This does not close the deferred
half by itself: the EVM measurement shows eager observation-time definitions
remain slower than frontend ITE folding.

ADR-0087 follows with candidate-triggered transitive ROW summaries. Admission
retains one exact bounded scalar summary per observed structural read; a SAT
candidate that violates it activates the summary permanently and resumes the
same CNF/SAT instance under one shared deadline. Default-completed replayable
misses can activate zero summaries, and inactive pending metadata creates no
work. Depth 32 improves from 30.933 ms to 11.257 ms, while direct ITE folding is
still 0.405 ms.

ADR-0088 then retains scalar-keyed array-valued UF applications as warm array
leaves. Conditional argument/index congruence constrains observed reads; private
array owners project one full array result per concrete argument tuple before
function construction and original replay. The 64-parent boundary and a 192-
comparison warm/`check_auto`/Z3 matrix validate this slice. Extensionality,
structural equality, and nested Boolean relation flags follow in
ADR-0089/0090/0091; array-valued parameters, memory BMC/k-induction, proofs, and
the remaining performance gap keep the deferred half open.

ADR-0089 adds the first exact warm extensionality relation. Positive equality
merges direct/application projection owners before function construction; top-
level disequality over symbol/store/constant/ITE/application parents introduces
one private diff index and two retained reads. A 192-comparison warm/
`check_auto`/Z3 matrix validates the slice.

ADR-0090 then admits top-level positive equality over warm-supported structural
parents. It gives store/constant/array-ITE parents cached private constructor
owners, adds bounded old/future shared-index observations, realizes owner
equations to a class-aware fixed point before array-valued function projection,
filters private symbols, and still gates SAT by original replay. Boolean
relation flags then land in ADR-0091.

ADR-0091 admits supported array equality atoms nested under scalar Boolean
structure as private candidate-sensitive flags. True flags add guarded paired-
read equality observations and are the only flagged equalities merged/realized
during projection; false flags add one guarded diff witness. Array-valued
parameters, memory BMC/k-induction, proofs, and the performance gap keep the
deferred half open.

## Consequences

- *Easier:* symbolic execution / reachability over memory becomes a warm,
  incremental capability; QF_ABV is reachable through the push/pop API.
- *Harder / to watch:* lazy axiom instantiation needs a termination guard
  (bounded lemma rounds → `unknown` with `ResourceLimit`, per the budget
  convention in review #6); extensionality (`a = b` over arrays) needs explicit
  handling or an explicit `Unsupported`.
- *Capability ledger:* add an "incremental QF_ABV (lazy arrays)" row, initially
  `experimental`, promoted to `validated` once it is differentially checked
  against the eager eliminator over the memory scenarios.
- *Unchanged:* eager elimination stays the one-shot default; soundness rests on
  valid lemmas + model replay; no new IR sort (arrays already exist).
