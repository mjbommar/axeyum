# Axeyum — Master Plan And Status

This is the single entry point for starting or resuming work. Read this file
first; it tells you what the project is, where it stands, what to do next, and
where everything else lives. Update the **Status** and **Next Actions**
sections at the end of every working session.

## What Axeyum Is

A Rust-first automated reasoning stack: typed term IR → rewriting → query
planning → solver backends (native SMT oracles + a growing pure Rust
bit-blast-to-SAT path) → models, proofs, and checkable evidence.

Identity in one sentence: **untrusted fast search, trusted small checking.**
Every `sat` gets a model checked by evaluation; every `unsat` eventually gets
a proof artifact or an independent oracle cross-check.

North star: a **usable, ideally pareto-dominant system for constrained program
optimization and software verification**, reached in three destinations:
(1) **foundation** — the decidable + arithmetic core with checkable evidence
(where we are now); (2) **complete solver replacement** — a drop-in Z3/cvc5-class
SMT solver, gated on *performance on real corpora*, not theory breadth; (3)
**Lean / angr as first-class functionality** — binary frontend + symbolic
execution/emulation (angr/unicorn) and kernel-checkable proving + proof-assistant
interop (Lean), as first-class capabilities, not consumers on top
(see [north-star](docs/research/00-orientation/north-star.md)).

**Honest status: we are at destination (1).** Not yet a solver replacement (the
pure-Rust path decides only a small slice of real public QF_BV; performance is
the open gate) and not yet Lean/angr-class (the symbolic-execution consumer is a
test-only register VM). Identity in one sentence: **untrusted fast search,
trusted small checking** — every `sat` is model-checked by evaluation, every
`unsat` gets a proof artifact (DRAT/Farkas) or independent cross-check.

Full framing: [docs/research/00-orientation/mission-and-scope.md](docs/research/00-orientation/mission-and-scope.md)

## Status

Last updated: 2026-06-13

- Consumer-models iteration 1 recorded 2026-06-13
  ([ADR-0008](docs/research/09-decisions/adr-0008-consumer-scenario-models.md),
  [consumer-scenario-models note](docs/research/07-verification/consumer-scenario-models.md)):
  added the `axeyum-scenarios` crate, a self-checking consumer-workload
  generator whose ground truth comes from the `axeyum-ir` evaluator, never from
  Z3. SAT scenarios are built by concrete execution and carry a witness
  verified by evaluation; UNSAT scenarios assert negated bit-vector identities
  proven by exhaustive small-width enumeration (or deterministic sampling above
  `EXHAUSTIVE_BIT_LIMIT`). Three families ship (`mixing` keyed-function
  inversion, `machine` register-machine path conditions + conflicting paths,
  `identity` full-adder/xor-swap/de-Morgan/two's-complement), all inside the
  supported lowering subset. A new `axeyum-solver` differential test runs the
  whole deterministic `catalog()` through `SatBvBackend`: every scenario is
  decided in ~1.7s with zero unknowns and zero soundness alarms, agreeing with
  the oracle-free ground truth. The self-check caught a real generator bug
  during bring-up. This addresses the Phase 5 stall by giving optimization a
  realistic, scalable, oracle-free corpus that exercises the pure-Rust path
  (rather than tuning the single `p4dfa` public frontier against Z3). Four
  iterations are recorded (consumer models, the incremental `Solver` façade,
  typed `BvLayerStats` + pipeline report, and a scaling profile).
- Follow-ons recorded 2026-06-13: (1) arithmetic lowering completes the **full
  scalar QF_BV operator set** — `bvmul` (truncated shift-and-add), unsigned
  division/remainder `bvudiv`/`bvurem` (a combinational restoring divider with
  SMT-LIB divide-by-zero totality), and signed `bvsdiv`/`bvsrem`/`bvsmod`
  (sign-handling wrappers over the unsigned divider) in `axeyum-bv`, each
  verified exhaustively against the evaluator, plus an `Arithmetic` scenario
  family the pure-Rust backend decides. No scalar operator is unsupported any
  more. (2) Incremental SAT stage 1
  ([ADR-0009](docs/research/09-decisions/adr-0009-incremental-sat-and-solving.md)):
  `IncrementalSat` in `axeyum-cnf`, a warm `rustsat-batsat` wrapper with
  monotone clause addition, native one-shot assumptions, and selector-literal
  push/pop, with model self-check matching the one-shot adapter. Stage 2
  (incremental bit-blasting wiring) is the next planned step.
- Downstream standing spot-check 2026-06-13: ran the pure-Rust backend on six
  small real multiplication/division SMT-LIB instances from the public QF_BV
  corpus (`bmc-bv`, `challenge`). After the full arithmetic operator set landed:
  3 sat, 1 unsat, 2 unknown (BatSat timeouts), **0 unsupported**, 0
  disagreements, 0 model-replay failures, 4 status agreements with the declared
  `:status`. Before this work every one of these would have returned
  `Unsupported`; the operator-coverage gap is now closed and the only remaining
  gap is SAT/encoding cost — the recorded performance R&D direction (ADR-0009
  stage 2 incremental bit-blasting and encoding reduction).
- Incremental bit-blasting (ADR-0009 stage 2) recorded 2026-06-13: end-to-end
  incremental solving via `IncrementalLowering` (`axeyum-bv`, persistent AIG +
  memo), `IncrementalCnf` (`axeyum-cnf`, per-node Tseitin over the warm
  `IncrementalSat` with selector-guarded roots), and `IncrementalBvSolver`
  (`axeyum-solver`, `assert`/`push`/`pop`/`check`/`check_assuming` with model
  lift + original-term replay). Decides the whole oracle-free scenario catalog
  with zero soundness alarms and passes a symbolic-execution push/pop
  path-exploration test. This is the key performance lever for the
  symbolic-execution consumer: shared subterms bit-blast once and the SAT
  solver stays warm across path queries.
- Arrays sub-increment 1 (IR) recorded 2026-06-13
  ([ADR-0010](docs/research/09-decisions/adr-0010-arrays-via-eager-elimination.md)):
  the IR now has an `Array` sort and `select`/`store` with a direct
  read-over-write evaluator (the semantic reference), backing the eager-
  elimination plan toward QF_ABV / memory-using symbolic execution. `Value`
  moved from `Copy` to `Clone` (array values are non-`Copy`), rippled across all
  crates.
- Arrays sub-increments 2 & 3-core recorded 2026-06-13: `eliminate_arrays`
  (`axeyum-rewrite`) reduces QF_ABV to QF_BV by read-over-write + Ackermann with
  model projection, and `axeyum-solver/tests/arrays.rs` shows **QF_ABV solving
  end to end** (elimination → `SatBvBackend` → projected model → original-query
  evaluator replay) on aliasing loads, read-after-write (UNSAT), and a
  satisfiable aliasing load — all soundness-checked oracle-free. Elimination is
  now a first-class entry point (`axeyum_solver::check_with_array_elimination`),
  and a memory-using symbolic-execution client
  (`tests/symbolic_execution_memory.rs`) solves a write-then-load QF_ABV query
  and confirms the found inputs + reconstructed memory by concrete
  re-execution. Remaining array work is QF_ABV scenarios, bench-harness wiring,
  and corpus blow-up measurement.
- UNSAT proof checking recorded 2026-06-13
  ([ADR-0011](docs/research/09-decisions/adr-0011-drat-unsat-proof-checking.md)):
  `axeyum-cnf` now has an independent DRAT checker (`check_drat`/`parse_drat`,
  RUP + RAT) — the trusted kernel that discharges `unsat`, depending only on the
  formula and proof. This is the most identity-critical trust piece (`sat` is
  replay-checked; `unsat` was previously unchecked). A DRAT *producer*
  (proof-capable adapter or the custom CDCL core) is the remaining step to make
  `unsat` high-assurance end to end.
- Proof-producing SAT core recorded 2026-06-13
  ([ADR-0012](docs/research/09-decisions/adr-0012-proof-producing-sat-core.md)):
  `axeyum_cnf::solve_with_drat_proof` (a **1-UIP CDCL** core) emits DRAT
  that `check_drat` verifies, giving **end-to-end checked `unsat` in pure Rust**
  — the full "untrusted fast search, trusted small checking" identity now holds
  for both `sat` (model replay) and `unsat` (DRAT proof + checker). The core is
  a correctness reference; `rustsat-batsat` stays the fast default. This is now
  wired into `SatBvBackend` via `SolverConfig::prove_unsat`: QF_BV `unsat` is
  high-assurance end to end (term → AIG → CNF → proof core → DRAT → checker),
  with a soundness alarm on any disagreement.
- First downstream consumer recorded 2026-06-13: a symbolic-execution client
  (`axeyum-solver/tests/symbolic_execution.rs`) — a register-VM symbolic
  executor that forks at branches, maintains the path condition incrementally in
  `IncrementalBvSolver` (push/pop), prunes infeasible branches by `check`, and
  finds inputs reaching a target. Every solver-found input is cross-checked by
  **concrete re-execution** of the program (unicorn-style oracle-free ground
  truth). Covers single-stage and two-stage keychecks, a multiplication/
  subtraction check, and infeasible-target pruning. This is the first Phase 7
  infosec-workflow client example (memory-using programs still need arrays) and
  validates the whole stack end to end against the real use case.
- Watched-literal CDCL recorded 2026-06-13: the proof-producing core
  (`solve_with_drat_proof`) now uses two-watched-literal propagation on top of
  1-UIP learning, validated by a 400-CNF randomized differential test against the
  `rustsat-batsat` adapter (agree on sat/unsat; `sat` models satisfy; `unsat`
  proofs pass `check_drat`). Restarts/activity heuristics and becoming the
  default solver stay benchmarking-gated (ADR-0012 follow-up).
- Uninterpreted functions sub-increment 1 (IR) recorded 2026-06-13
  ([ADR-0013](docs/research/09-decisions/adr-0013-uninterpreted-functions.md)):
  the IR now has first-class uninterpreted functions — `declare_fun` with a
  scalar signature, `Op::Apply`/`TermArena::apply`, and a `FuncValue`
  interpretation carried by the model that the ground evaluator honors (the EUF
  semantic reference). An exhaustive width-3 test confirms the defining
  congruence property `x = y → f(x) = f(y)`, exactly what the planned Ackermann
  reduction will encode (reusing the array-elimination machinery). The Z3 oracle
  rejects `Op::Apply` (UF is eliminated before solving, like arrays); the
  SMT-LIB writer emits `declare-fun` and selects `QF_UFBV`/`QF_AUFBV`.
- Uninterpreted functions sub-increment 2 (elimination + solving) recorded
  2026-06-13 (ADR-0013): `axeyum_rewrite::eliminate_functions` reduces
  `QF_UFBV` to `QF_BV` by **Ackermann congruence reduction** (each distinct
  application → a fresh scalar symbol; each pair of same-function applications →
  `args_i = args_j → f_i = f_j`) with `FuncValue` model projection, reusing the
  array-elimination shape. `axeyum_solver::check_with_function_elimination` is
  the first-class entry point (eliminate → `SatBvBackend` → projected
  interpretation → original-query evaluator replay), and `Model` now carries
  function interpretations. End-to-end `QF_UFBV` tests pass oracle-free:
  congruence-forced `unsat` (`x = y ∧ f(x) ≠ f(y)`; pinned `f(x)=aa, f(y)=bb`
  with `x=y`), replayed `sat` (`f(x) ≠ f(y)`), and binary-function congruence.
  Remaining EUF work: scenarios, the SMT-LIB parser side, and composing array +
  function elimination for `QF_AUFBV`.
- Uninterpreted functions SMT-LIB I/O recorded 2026-06-13 (ADR-0013): the
  `axeyum-smtlib` parser now accepts n-ary `declare-fun` (scalar signatures) and
  function applications (builtins keep priority over declared names), completing
  a parse → write → parse round-trip for `QF_UFBV` with the existing writer.
  Function parameters over array sorts are still rejected (functions are scalar).
  Remaining EUF work: `QF_UFBV` scenarios and `QF_AUFBV` composition.
- `QF_AUFBV` theory composition recorded 2026-06-13 (ADR-0010 + ADR-0013):
  `axeyum_solver::check_with_arrays_and_functions` solves formulas mixing arrays
  and uninterpreted functions by **composing the two eager passes** — array
  elimination (`QF_AUFBV` → `QF_UFBV`) then function elimination (`QF_UFBV` →
  `QF_BV`) — and projects the `sat` model back through both (functions first,
  since a `select` index may mention a function application), replaying against
  the original mixed query. Oracle-free end-to-end tests: cross-theory
  congruence `unsat` (`mem[i]=v ∧ f(v)=aa ∧ f(mem[i])≠aa`), store-then-apply
  `sat` with replay, distinct outputs over distinct loads. This is the first
  two-theory composition — the eager precursor to a general combination
  framework (Nelson-Oppen / CDCL(T)). Array *equality* remains deferred
  (composition handles mixed formulas, not extensional array equality).
- `QF_UFBV` scenarios recorded 2026-06-13 (ADR-0013): a `Family::Function` in
  `axeyum-scenarios` (`function_chain` nested applications, `function_lookup`
  unary with deliberate argument collisions exercising congruence,
  `function_binary_merge` two-argument map) plus `function_catalog`, all
  satisfiable by construction with the function table carried as the witness
  (verified by the existing SAT self-check). A solver-crate differential test
  decides the whole catalog through `check_with_function_elimination`,
  oracle-free. **The EUF rollout now matches the array track** end to end (IR,
  evaluator, elimination, solver entry point, SMT-LIB I/O, scenarios, `QF_AUFBV`
  composition); array equality is the lone deferred theory feature.
- Arithmetic sub-increment 1 (IR + evaluator) recorded 2026-06-13
  ([ADR-0014](docs/research/09-decisions/adr-0014-first-arithmetic-fragment.md)):
  the IR now has a first-class **`Int` sort** with integer constants and the
  linear operator set (`int_add`/`int_sub`/`int_neg`/`int_mul` and the order
  comparisons `int_lt`/`int_le`/`int_gt`/`int_ge`; `Eq`/`Ite` already
  polymorphic), plus a `Value::Int` and a ground evaluator that interprets `Int`
  as mathematical integers (exact within the `i128` reference range; out-of-range
  intermediates panic as a usage error, the bounded-LIA contract). The
  evaluator semantics are verified exhaustively over a small integer range. The
  `Int` sort rippled across all crates (mirroring the earlier `Value` and
  `Op::Apply` ripples); the pure-Rust BV backend (now via the new
  `first_unsupported_sort` preflight) and the Z3 oracle reject `Int` with a clear
  `Unsupported`, exactly as arrays and EUF were staged before their lowering
  landed. This opens the arithmetic rung of the north-star ladder. Remaining
  `QF_LIA`: the bounded bit-blasting decision procedure (`Int` → `QF_BV` at a
  chosen width, with `sat` replay and out-of-range → `unknown`), then scenarios
  and SMT-LIB I/O.
- `QF_LIA` bounded bit-blasting decision procedure recorded 2026-06-13
  (ADR-0014): `axeyum_rewrite::blast_integers` maps integers to signed width-`B`
  bit-vectors (`int_add/sub/neg/mul` → `bvadd/bvsub/bvneg/bvmul`,
  `int_lt/le/gt/ge` → `bvslt/bvsle/bvsgt/bvsge`), and
  `axeyum_solver::check_with_int_blasting` solves with `SatBvBackend`, **reads
  the model back as exact integers, and replays the original integer assertions**
  with the ground evaluator. Soundness contract enforced end to end: BV `sat` +
  exact replay → `sat`; replay failure from width-`B` wraparound → `unknown`; BV
  `unsat` → `unknown` (never `unsat`, since an unbounded model may exist);
  out-of-range constant → `unknown`. Oracle-free end-to-end tests cover
  satisfiable linear equations (incl. negative solutions, two-variable
  relations), contradictory bounds → `unknown`, and out-of-range → `unknown`.
  This is the first **decision procedure for a new theory built by reduction to
  the trusted core** — `QF_LIA` `sat` is now checkable end to end. Remaining
  `QF_LIA`: scenarios and SMT-LIB I/O.
- `QF_LIA` scenarios + SMT-LIB I/O recorded 2026-06-13 (ADR-0014): a
  `Family::Integer` in `axeyum-scenarios` (`integer_system` boxed/ordered/
  sum-pinned systems, `integer_equation` boxed linear equations) with
  `integer_catalog`, all satisfiable by construction and decided through
  `check_with_int_blasting` in a solver differential test (the boxing keeps the
  only in-range models near the witness, so no spurious overflow `unknown`). The
  SMT-LIB parser/writer now handle the `Int` sort, integer literals, `(- n)`
  negation, `+`/`-`/`*`, and chainable `<`/`<=`/`>`/`>=`, with a `QF_LIA`
  round-trip. **The `QF_LIA` rollout now matches the array/EUF tracks** end to
  end (IR, evaluator, decision procedure, solver entry point, scenarios, SMT-LIB
  I/O).
- Full theory composition (`QF_AUFLIA`) recorded 2026-06-13 (ADR-0010 + 0013 +
  0014): `axeyum_solver::check_with_all_theories` runs all three eager
  reductions in dependency order — array elimination (`QF_AUFLIA` → `QF_UFLIA`),
  function elimination (`QF_UFLIA` → `QF_LIA`), integer bit-blasting (`QF_LIA` →
  `QF_BV`) — solves the pure-`QF_BV` result, and projects the model back in
  reverse (integer read-back → function interpretations → array values) before
  replaying against the original mixed query. It subsumes every single-theory
  entry point (unused reductions act as the identity). The soundness contract is
  branch-correct: array/function elimination are exact, so an **integer-free**
  `unsat` is reported as `unsat` and a replay failure is a soundness alarm; an
  **integer-bearing** `unsat` or overflowing replay is `unknown`. Oracle-free
  end-to-end tests: full arrays+functions+integers `sat` with replay,
  integer-free congruence → exact `unsat`, mixed integer contradiction →
  `unknown`, pure-BV pass-through. This is the **eager precursor to a general
  theory-combination framework** (Nelson-Oppen / CDCL(T)).
- Linear real arithmetic sub-increment 1 (IR + evaluator) recorded 2026-06-13
  ([ADR-0015](docs/research/09-decisions/adr-0015-linear-real-arithmetic.md)):
  the project's **first non-`QF_BV` theory**. A pure-Rust exact `Rational`
  (`i128` numerator/denominator, normalized, `Neg`/`Add`/`Sub`/`Mul`/`Ord`,
  overflow-checked) backs a first-class **`Real` sort** with rational constants
  and the linear operator set (`real_add`/`real_sub`/`real_neg`/`real_mul` and
  order comparisons; `Eq`/`Ite` polymorphic), plus a `Value::Real` and a ground
  evaluator doing **exact rational arithmetic** (the semantic reference; checked
  against an exact reference over a grid of fractions). No floats — the model
  must stay exactly checkable. The `Real` sort rippled across all crates;
  backends reject `Real` via `first_unsupported_sort`/the oracle, as integers
  were before bit-blasting. Remaining `QF_LRA`: the **exact-rational simplex**
  decision procedure (reals do **not** bit-blast — this is the first procedure
  not reducible to the trusted `QF_BV` kernel, guarded by `sat` model replay),
  then scenarios and SMT-LIB I/O.
- `QF_LRA` decision procedure recorded 2026-06-13 (ADR-0015):
  `axeyum_solver::check_with_lra` decides **conjunctive** `QF_LRA` by
  **exact-rational Fourier–Motzkin elimination** — the project's first decision
  procedure not reducible to the `QF_BV` kernel. It parses assertions into linear
  atoms (`and`/`not` pushed in, equality → two inequalities; `or`/disequality →
  `Unsupported`, needing DPLL(T)), eliminates variables over exact `Rational`s,
  and reconstructs a rational model by forward substitution. **Every `sat` model
  is replayed through the ground evaluator** (the trust anchor — a
  Fourier–Motzkin bug cannot yield an unsound `sat`); `unsat` is lower-assurance
  pending a Farkas certificate. Oracle-free end-to-end tests: strict interval
  with a fractional witness (`x ∈ (1/2,1)`), empty interval → `unsat`,
  two-variable system, `3x = 1` pinning `x = 1/3`, strict cycle → `unsat`,
  disjunction → `Unsupported`. Remaining `QF_LRA`: scenarios + SMT-LIB I/O, and
  later DPLL(T) + δ-rational simplex for full Boolean structure and scale.
- `QF_LRA` scenarios + SMT-LIB I/O recorded 2026-06-13 (ADR-0015): a
  `Family::Real` in `axeyum-scenarios` (`real_system` boxed/ordered/sum-pinned
  rational systems, `real_ratio_equation` pinning fractional witnesses) with
  `real_catalog`, decided through `check_with_lra` in a solver differential test.
  The SMT-LIB parser/writer now handle the `Real` sort, decimal literals
  (`n.ddd`), `(/ a b)` rational division, `(- n)` negation, and **sort-directed
  `+`/`-`/`*`/comparisons** that coerce integer numerals to `Real` in real
  contexts (the standard SMT-LIB numeral coercion), with a `QF_LRA` round-trip
  (integer-valued reals render as `n.0`). **The `QF_LRA` rollout now matches the
  other theories** end to end, modulo the deferred DPLL(T) Boolean structure and
  a δ-rational simplex for scale. **All five core theories (`QF_BV`, arrays,
  EUF, `QF_LIA`, `QF_LRA`) now span IR → evaluator → procedure → solver entry
  point → scenarios → SMT-LIB I/O.**
- Lazy SMT / DPLL(T) over `QF_LRA` recorded 2026-06-13 (ADR-0015 follow-on):
  `axeyum_solver::check_with_lra_dpll` is the **first theory-combination
  engine** — it lifts the conjunction-only limit by Boolean-abstracting each real
  order atom to a fresh proposition, solving the propositional skeleton with
  `SatBvBackend`, checking the chosen atom literals with the conjunctive
  `check_with_lra`, and learning a blocking clause on each theory conflict until
  SAT and theory agree (or the skeleton is exhausted → `unsat`). Termination is
  by finitely many atom assignments; **every `sat` is replayed against the
  original assertions** (trust anchor). Oracle-free end-to-end tests: a
  disjunction of real constraints (previously `Unsupported`) now decides, a
  feasible-branch case split, a Boolean-unsatisfiable combination → `unsat`,
  mixed Boolean variables + theory atoms, and pure conjunctions. A subtle
  invariant was caught and fixed (the SAT backend completes all declared symbols
  to defaults, so only Boolean values are taken from the propositional model —
  the theory owns the real assignment). This is the architecture for full
  theory combination; next is generalizing it across theories (Nelson-Oppen) and
  adding equality/disequality.
- Unified quantifier-free dispatcher recorded 2026-06-13:
  `axeyum_solver::check_auto` is the **single front door** for any supported
  quantifier-free query — it scans the theory features and routes: anything over
  bit-vectors/arrays/uninterpreted-functions/bounded-integers (with arbitrary
  Boolean structure, handled natively by the bit-blaster) goes to
  `check_with_all_theories`; anything over reals goes to the lazy-SMT
  `check_with_lra_dpll`. A query mixing reals with the bit-blasted theories is
  reported `Unsupported` (true Nelson-Oppen real+other combination is future
  work) rather than answered unsoundly. Tests route a pure-BV query, a full
  `QF_AUFLIA` array+function+integer query, and a real disjunction to the right
  engines, and reject a mixed real+BV query. This ties the whole solver together
  for the downstream consumer: one call decides any supported logic.
- Quantifiers sub-increment 1 (IR + evaluator) recorded 2026-06-13
  ([ADR-0016](docs/research/09-decisions/adr-0016-quantifiers-binder-representation.md)):
  the **jump from decision procedures toward general reasoning**. Quantifiers use
  **named binders** (`Op::Forall(SymbolId)`/`Op::Exists(SymbolId)` over a `Bool`
  body, reusing the symbol/`Assignment` machinery), with `TermArena::forall`/
  `exists` builders and a ground evaluator that **enumerates the bound variable's
  finite domain** (`Bool`, `BitVec(w)` up to `2^16`) with short-circuiting;
  infinite domains (`Int`/`Real`/arrays) are an `UnsupportedQuantifierDomain`
  error. Tested: Boolean tautology/contradiction quantifiers, bit-vector
  `forall`/`exists` over all values, nested `forall x. exists y. x = y`, and a
  real-domain `forall` correctly erroring. The `Op` encoding localized the
  cross-crate ripple; backends reject quantified (non-QF) formulas, and the
  SMT-LIB writer renders binder form. Remaining: quantifier **solving**
  (instantiation / E-matching on the DPLL(T) core) and the SMT-LIB parser side.
- Quantifier solving by finite-domain expansion recorded 2026-06-13 (ADR-0016):
  `axeyum_rewrite::expand_quantifiers` rewrites each finite-domain quantifier to
  the conjunction/disjunction of its instances (`BitVec` capped at `2^10`), and
  `axeyum_solver::check_with_quantifiers` expands → dispatches via `check_auto` →
  **replays the original quantified formula through the enumerating evaluator**
  (trust anchor). Complete for finite domains. Oracle-free end-to-end tests: a
  universal tautology → `sat`, a false universal → `unsat`, an existential
  constraining a free variable, nested `forall x. exists y. x = y` → `sat`, and
  an infinite domain → `Unsupported`. **Quantified finite-domain formulas now
  decide end to end.** Remaining: E-matching for infinite-domain quantifiers and
  the SMT-LIB parser side.
- WebAssembly support recorded 2026-06-13
  ([ADR-0017](docs/research/09-decisions/adr-0017-wasm-target-support.md)): the
  default library stack — IR, AIG, BV, CNF, query, rewrite, SMT-LIB, and the
  pure-Rust SAT solver — **builds and runs on WebAssembly** (browser and WASI),
  enabling a sandboxed "untrusted fast search, trusted small checking"
  deployment. This is a direct payoff of the no-C/C++-default-dep Hard Rule (the
  `z3` C++ backend stays feature-gated off). The only change needed was a
  target-conditional monotonic clock: on `wasm32` the timing/timeout code uses
  `web-time`'s drop-in `Instant` (the browser has no `std` clock), via a
  `cfg(target_arch = "wasm32")` dependency and import in `axeyum-cnf` and
  `axeyum-solver`; native builds are untouched. Verified both
  `cargo build --target wasm32-unknown-unknown` (all default crates) and the full
  native gate. Determinism is unaffected (the clock only bounds timeouts/
  telemetry, never results).
- SMT-LIB quantifier parsing recorded 2026-06-13 (ADR-0016): the parser accepts
  `(forall ((x T) ..) body)` / `(exists ..)` — each bound variable becomes a
  **uniquely-named fresh symbol** (no capture of free symbols or sibling
  binders), scoped to the body via the `let`-style scope stack, then wrapped in
  nested `forall`/`exists`. With the existing writer this gives a quantifier
  parse → write → parse round-trip; a nested-binding test confirms two separate
  `x` binders do not collide. **The quantifier rollout now matches the other
  theories end to end** (IR, evaluator, expansion solving, SMT-LIB I/O);
  E-matching for infinite-domain quantifiers is the remaining piece.
- Exportable `unsat` proof artifacts recorded 2026-06-13 (ADR-0011/0012
  follow-on): `axeyum_cnf::write_drat` serializes a DRAT proof to the standard
  textual format (inverse of `parse_drat`, accepted by `drat-trim`), and
  `axeyum_solver::export_qf_bv_unsat_proof` bit-blasts a `QF_BV` query, runs the
  proof-producing core, and on `unsat` returns an `UnsatProof { dimacs, drat }` —
  the CNF in DIMACS and the refutation in DRAT, **self-verified by the in-tree
  `check_drat` and independently re-checkable**. Tests: an unsat query exports a
  certificate whose DRAT re-parses and refutes the re-parsed DIMACS (checked
  independently of the producing solver); a sat query yields no proof; a
  non-bit-blastable query is `Unsupported`. This is the first **exportable,
  externally-auditable evidence artifact** — the "proving" arm of the north
  star at the clausal layer. Certifying the bit-blast reduction itself (term →
  AIG → CNF) is the future full SMT-level proof step.
- Real equality/disequality in lazy SMT recorded 2026-06-13 (ADR-0015): the
  DPLL(T) path now handles real `(= a b)` atoms by abstracting them to
  `(a <= b) and (a >= b)`, so equality **and disequality** (`a < b or a > b`,
  the negation) flow through the order-atom machinery and the SAT case split —
  no special disequality reasoning in the Fourier–Motzkin solver. `check_auto`
  thus decides arbitrary Boolean combinations of real equalities/inequalities.
  Tests: a disjunction of real equalities, `x != 0 ∧ x <= 0 ∧ x >= 0` → `unsat`,
  and a satisfiable disequality. Remaining `QF_LRA`: δ-rational simplex for scale
  and Nelson-Oppen with the bit-blasted theories.
- Self-checking evidence envelope recorded 2026-06-13 (ADR-0005 follow-through):
  `axeyum_solver::Evidence` makes the "trusted small checking" identity
  consumer-facing — a result paired with the artifact that justifies it and a
  single `Evidence::check(arena, assertions)` that **re-validates it
  independently**: a `sat` model is replayed through the ground evaluator; an
  `unsat` DRAT certificate (DIMACS + DRAT) is re-parsed and re-run through the
  trusted `check_drat` kernel; `unknown`/uncertified-`unsat` check vacuously.
  `produce_qf_bv_evidence` runs the pure-Rust `QF_BV` pipeline and packages the
  outcome (with a soundness alarm if backend and proof core disagree). Tests:
  sat evidence replays, unsat evidence re-checks via DRAT, and a **tampered
  (wrong) sat model fails its own `check`** — the replay guard catching a bogus
  certificate. This concretizes ADR-0005's long-recorded "layered, checkable
  evidence envelope" as a real type. `produce_qf_bv_evidence` now returns an
  `EvidenceReport` pairing the evidence with **versioned `Provenance`**
  (semantics version, backend identity, assertion count, and the resource-budget
  config) so a run is reproducible and the evidence interpretable later.
- Term-level `unsat` certification by enumeration recorded 2026-06-13:
  `axeyum_solver::certify_qf_bv_by_enumeration` is the **trust dual of model
  replay** — for small `QF_BV`/Boolean instances it enumerates every assignment
  over the finite symbol domain and evaluates the original assertions with the
  ground evaluator alone; if none satisfies them, that is an **oracle-free,
  term-level `unsat` certificate independent of the bit-blaster, CNF encoder, and
  SAT solver** (it uses only `axeyum-ir`). It returns a model when satisfiable
  and `DomainTooLarge` above the bit budget. Tests: `x&1=1 ∧ x&1=0` → certified
  unsat (16 cases), a sat model found, an oversized 64-bit domain reported, and
  the xor-commutativity identity certified. This complements the scalable DRAT
  proof (which certifies only the clausal layer) with a small-instance check at
  the term level — closing the "certify beyond the clausal layer" gap for small
  queries using the most-trusted component.
- Disjoint theory combination recorded 2026-06-13: `check_auto` now decides a
  query mixing reals with the bit-blasted theories when the two parts are
  **variable-disjoint** (Nelson-Oppen's base case) — it partitions assertions
  into a real group and a bit-blasted group, confirms no assertion is itself
  entangled and the groups share no symbols, solves each with its engine
  (`check_with_lra_dpll` / `check_with_all_theories`), merges the models (taking
  each symbol from its owning group to avoid the backends' default-completion
  overwriting the other engine's assignment), and replays the whole original
  query. Genuinely entangled queries (a single mixed formula, or a shared
  Boolean/variable link) stay `Unsupported`. Tests: disjoint real+BV → `sat`
  combined, one part unsat → `unsat`, shared-Bool link → `Unsupported`, entangled
  single assertion → `Unsupported`. This is the first **theory-combination across
  the bit-blast/exact-arithmetic boundary** (general Nelson-Oppen with shared
  equalities remains future work).
- Quantifier instantiation for infinite domains recorded 2026-06-13 (ADR-0016):
  `axeyum_rewrite::instantiate_universals` performs **enumerative ground
  instantiation** — each top-level `forall x. body` becomes the conjunction of
  `body[x := t]` over the formula's ground terms of `x`'s sort — and
  `axeyum_solver::prove_unsat_by_instantiation` solves the result via
  `check_auto`. Instantiation only weakens, so a returned `unsat` transfers
  soundly to the original (a satisfiable instantiation is honest `unknown`; a
  quantifier-free query decides exactly). This **refutes infinite-domain `Real`
  universals that finite-domain expansion cannot enumerate**; integer universals
  degrade to `unknown` (bounded blasting's unsat-in-range is `unknown`, ADR-0014).
  Tests: a real universal refuted (`∀r. r<1` with ground `1`), integer-universal
  bounded-`unknown`, satisfiable instantiation → `unknown`, and QF decided
  exactly. Trigger-based E-matching is the scalable successor.
- General real + bit-blasted theory combination recorded 2026-06-13: the
  lazy-SMT loop `check_with_lra_dpll` is **generalized into a complete
  combination of `QF_LRA` with the bit-blasted theories** (BV/arrays/EUF/bounded
  integers). Key observation: reals share **no sort** with those theories, so
  there are no interface equalities to propagate — the only coupling is
  propositional, and a SAT-driven case split over the shared Boolean structure is
  a complete Nelson-Oppen combination. Implementation: the abstractor now
  abstracts **only real atoms** to fresh propositions and leaves every non-real
  subterm intact, and the loop decides the skeleton with
  `check_with_all_theories` (which handles bv/array/func/int natively) instead of
  the bare SAT backend; the LRA theory solver checks the real-atom literals and
  learns blocking clauses on conflict; the combined model (reals from LRA, the
  rest from the bit-blaster) is replayed against the original query. This
  **subsumes the earlier disjoint-only handler** — `check_auto` now decides
  *any* mixed real + bit-blasted query (since real↔bit-vector atoms can't share a
  term, every mix is decidable). Tests updated: a real+BV formula and a
  Boolean-linked `(p ∨ r>0) ∧ (¬p ∨ b=1)` now both decide `sat`.
- Unified `solve` front door recorded 2026-06-13: `axeyum_solver::solve` is the
  **single entry point for any supported query** — quantifier-free or quantified,
  over any theory combination. It routes: quantifier-free → `check_auto`
  (lazy-SMT when reals present, bit-blasting composition otherwise); quantified →
  `check_with_quantifiers` (finite-domain expansion, complete for Bool/BV), with
  a sound `prove_unsat_by_instantiation` fallback when a quantifier ranges over an
  infinite domain. One call now decides `QF_BV`, mixed real+BV, finite-domain
  quantifiers, and infinite-domain refutation — tested across all four. This is
  the consumer-facing capstone: "one call decides anything supported," with model
  replay as the universal trust anchor.
- SMT-LIB text front door recorded 2026-06-13 (ADR-0018): `axeyum_solver::solve_smtlib`
  closes the real-world end-to-end path — **SMT-LIB 2 text in, a checked
  `sat`/`unsat`/`unknown` out**. It parses with `axeyum-smtlib` (now a production
  dependency of the solver crate, acyclic + wasm-clean) and decides with `solve`,
  returning `SmtLibOutcome { result, logic, expected_status }` so a caller can
  cross-check against the script's own `(set-info :status ...)`. New
  `SolverError::Parse` variant keeps the whole text→answer path under one error
  type. Integration tests (`tests/smtlib.rs`) drive real SMT-LIB text for QF_BV
  sat, QF_BV unsat, a quantified script, and a malformed-input parse error.
  Foundational DAG + support matrix updated to record the new edge and row.
- CDCL-priority gate (a) made falsifiable 2026-06-13: `axeyum-bench` artifact
  bumped to version 14 with a corpus-level `summary.layer_attribution` block —
  per-stage seconds and shares (bit-blast / CNF encode / SAT solve / model lift)
  over decided pure-Rust (`sat-bv`) instances, plus an explicit `sat_dominates`
  boolean vs a documented 0.5 threshold. The four stages are non-overlapping and
  sum to the pipeline wall time (`translate` = `bit_blast + cnf_encode`, not
  double-counted); the block is `null` when no `sat-bv` instance decided.
  **Measured on the micro corpus: SAT share ≈0.31, encoding stages ≈0.57 →
  `sat_dominates: false`.** This is the methodology-required evidence for the
  CDCL track: the micro tier (3 trivial instances) shows encoding-dominated
  time, but a **public QF_BV slice now reverses that**: on
  `20190311-bv-term-small-rw-Noetzli` (1416 decided `sat-bv` instances, full
  ground-truth agreement, 0 replay failures) the SAT-solve share is **~0.95**
  (bit-blast ~1.6%, CNF encode ~3.1%) → `sat_dominates: true`. So gate (a) holds
  on realistic decided QF_BV; the "encodings first" priority is now an open,
  data-driven question, not settled. Remaining before acting on CDCL: (i) breadth
  — confirm the share across more public/client families; (ii) gate (b) — a
  CaDiCaL/Kissat gap on Axeyum CNF, not yet measured. Core tuning still does NOT
  jump the queue on one family alone. Methodology doc updated (artifact v14 +
  micro-vs-public findings + a resource-governance note: relaxed CNF budgets ×
  high `--jobs` OOM-killed the host once; keep budgets and jobs bounded
  together).
- `QF_LRA` Farkas `unsat` certificates recorded 2026-06-13 (ADR-0015
  follow-through): `check_with_lra` now threads nonnegative Farkas multipliers
  through Fourier–Motzkin elimination, so every `unsat` carries a
  `FarkasCertificate` — a nonnegative combination of the original linear
  constraints that collapses to a constant contradiction (`0 < 0` or
  `0 <= -c`, `c > 0`). The certificate is rebuilt independently of the
  elimination (depending only on the collected atoms and the multipliers) and
  **self-checked via `FarkasCertificate::verify` before `unsat` is returned**;
  a failed check is a `SolverError::Backend` soundness alarm. This is the
  exact-arithmetic dual of DRAT for `QF_BV`: a Fourier–Motzkin bug can no more
  produce an unsound `unsat` than it can an unsound `sat`. Because the whole
  lazy-SMT/DPLL(T) real path routes theory checks through `check_with_lra`,
  every real-theory conflict is now certificate-checked automatically. The
  DPLL(T) loop also uses the certificate for **theory-conflict minimization**:
  the atoms with a nonzero Farkas multiplier are exactly the infeasible core, so
  it learns a blocking clause over just that core (a sound, strictly stronger
  lemma that prunes every assignment sharing the core, not only the current one)
  instead of negating the whole atom assignment — faster convergence at no
  soundness cost. `lra_farkas_certificate` exposes the certificate for external
  auditing.
  Oracle-free tests: empty interval / strict cycle / conflicting equalities
  each yield a verifying certificate, a `sat` query yields none, and a tampered
  certificate (dropped/negative/zeroed multiplier, or a hand-made
  non-refutation) is rejected by the independent checker. **This closes the
  last lower-assurance result type — all of `sat` (model replay), `QF_BV`
  `unsat` (DRAT + checker), and now `QF_LRA` `unsat` (Farkas + checker) are
  independently checkable.** The certificate is also wired into the
  consumer-facing `Evidence` envelope: a new `Evidence::UnsatFarkas` variant and
  `produce_lra_evidence` give a `QF_LRA` result whose single `Evidence::check`
  re-runs the independent Farkas verifier (the exact-arithmetic dual of the
  envelope's DRAT route), with tamper-rejection tests. `lra_unsat_core` also
  reads the Farkas support — the assertions whose constraints have a nonzero
  multiplier — to seed a deletion-minimized, re-verified **minimal
  unsatisfiable core** (a recognized SMT capability, useful for explaining
  infeasible symbolic-execution paths). A
  δ-rational simplex for scale remains the open `QF_LRA` follow-up.
- DPLL(T) `unsat` refutation certificates (pure-real) recorded 2026-06-13
  (ADR-0015): `certify_lra_dpll_unsat` generalizes the conjunctive Farkas
  certificate to **arbitrary Boolean structure over real atoms**. On `unsat` it
  returns a self-checked `LraDpllRefutation` — the Boolean skeleton plus the
  lazy-SMT loop's learned theory lemmas (infeasible real-atom cores).
  `LraDpllRefutation::verify` re-checks it independently: every lemma's core is
  re-decided `unsat` by `check_with_lra` (Farkas-self-checked), and the skeleton
  with all lemma clauses is shown propositionally unsatisfiable by enumerating
  the Boolean symbols (capped at 22 → otherwise classified `unknown`, never an
  unverified certificate). The abstraction is the trusted reduction, exactly as
  bit-blasting is on the DRAT route; the refutation is self-verified before
  return (failure → soundness alarm). Tests cover a verifying certificate, a
  replaying `sat` model, rejection of bit-vector content, and a tampered
  (lemma-stripped) refutation. Remaining: certify lazy-SMT `unsat` when the
  skeleton also carries bit-blasted theories (the propositional half then needs
  a DRAT proof rather than enumeration).
- Unified checkable-evidence front door recorded 2026-06-13:
  `axeyum_solver::produce_evidence` is the evidence analogue of the `solve`
  front door — one call routes any supported query to the producer with the
  strongest available certificate: pure `QF_BV`/Boolean → DRAT
  (`produce_qf_bv_evidence`), pure linear real → Farkas/lazy-SMT refutation
  (`produce_lra_dpll_evidence`), and everything else supported (arrays, EUF,
  bounded integers, mixed real+bit-blasted, quantifiers) → the unified `solve`
  engine, whose `sat` is replay-certified and whose `unsat` is recorded as a
  bare (honest, documented) `Evidence::Unsat(None)` pending a transferable proof
  artifact for those reductions (the open bit-blast-reduction certification
  track). Every branch's result re-validates through the single
  `Evidence::check`. Tests route a QF_BV query to a DRAT certificate, a
  pure-real query to a refutation, and an integer query to the replay-certified
  fallback.
- Theory-agnostic unsat cores recorded 2026-06-13: `axeyum_solver::unsat_core`
  generalizes `lra_unsat_core` to **any query `solve` can decide** — a
  deletion-based minimal unsatisfiable core over the unified front door. Starting
  from the full (unsat) set it drops each assertion whose removal leaves the rest
  *definitively* `unsat` (an `unknown` remainder is conservatively kept, so the
  result is always a genuine core), then re-decides the final core as a defensive
  self-check. `O(n)` solver calls, no corpus (memory-safe). Directly serves the
  symbolic-execution use case (explain infeasible paths across bit-vectors,
  arrays, EUF, integers, and reals). Tests isolate a conflicting bit-vector pair
  (excluding a tautology), a real conflict (excluding an irrelevant bound), and
  return `None` for satisfiable queries.
- Proving front door recorded 2026-06-13: `axeyum_solver::prove` is the
  consumer-facing **theorem-proving interface** over the checkable-`unsat`
  machinery — it proves `goal` follows from `hypotheses` by refuting the negation
  (`hypotheses ∧ ¬goal`) via `produce_evidence`. `ProofOutcome::Proved` carries
  the refutation's `EvidenceReport` (re-checked before return, so `Proved` is a
  verified proof), `Disproved` carries a replay-checked countermodel, and
  `Unknown` is inconclusive. This realizes the **proving arm of the north star**:
  proving a theorem = a checkable refutation of its negation (untrusted search,
  trusted small checking). Tests prove a real implication (`x>0 ⊨ x≥0`) and a
  bit-vector tautology (`(x|x)=x`) with re-checked certificates, and disprove a
  non-implication and a non-theorem with countermodels.
- Trigger-based E-matching recorded 2026-06-13 (ADR-0016, opens R&D track b):
  `axeyum_rewrite::instantiate_with_triggers` + `axeyum_solver::prove_unsat_by_ematching`
  refine quantifier instantiation — for each top-level `forall x. body` they pick
  the body's `apply`/`select` subterms mentioning `x` as triggers, match them
  against the assertions' ground subterms, and bind `x` to the matches, including
  **compound** ground terms (`f(a)`, `select(m,i)`) that the leaves-only
  enumeration of `instantiate_universals` never tries. Bindings union with the
  enumerative leaves (strictly at least as capable); soundness is unchanged
  (every ground instance follows from the universal — trigger choice only affects
  *which* sound instances are produced). `solve`'s quantifier fallback now uses
  it. A test demonstrates the capability gain: `forall x:BV16. g(x)=0 ∧ g(f(a))≠0`
  stays `unknown` under leaves-only enumeration but is refuted (`unsat`) by
  E-matching binding `x:=f(a)`. Remaining for track b: multi-trigger /
  multi-variable matching and an E-graph match index for scale.
- Nested universal chain instantiation recorded 2026-06-13 (ADR-0016): both
  `instantiate_universals` and `instantiate_with_triggers` now peel a prenex
  chain `forall x1. … forall xk. body` and instantiate over the **cartesian
  product** of each variable's bindings (capped at `CHAIN_INSTANCE_CAP`; over the
  cap the chain stays a sound residual `unknown`). Previously a multi-variable
  universal was skipped entirely (always `unknown`); now e.g.
  `forall x y:Real. x+y≥0` with `a<0` is refuted by the `x:=a, y:=a` instance.
  Soundness unchanged (every tuple instance follows from the chain).
- Multi-variable trigger matching recorded 2026-06-13 (ADR-0016, track b):
  `match_multi` binds several chain variables from a single trigger (`g(x,y)`
  against `g(f(c),h(c))` → `x:=f(c), y:=h(c)`), which single-variable matching
  could not (the other bound var blocked the match). Bound values join each
  variable's candidate set, so the cartesian product includes the coupled
  compound tuple. A test shows `forall x y:BV16. g(x,y)=0 ∧ g(f(c),h(c))≠0`:
  leaf enumeration stays `unknown` but multi-variable E-matching refutes it.
  Soundness unchanged (per-variable union over-approximates the coupled tuples).
  Remaining for track b: an E-graph match index for scale and matching modulo
  the current equalities.
- Exact-rational general simplex recorded 2026-06-13 (ADR-0015, the δ-simplex
  roadmap item): `axeyum_solver::check_with_lra_simplex` decides conjunctive
  `QF_LRA` by the Dutertre–de Moura "simplex with bounds" over exact δ-rationals
  (δ encodes strict inequalities; the witness is de-infinitesimalized to a
  concrete rational). It is a **second, independent** LRA engine — every `sat`
  model is replayed through the evaluator, every `unsat` is cross-checked against
  the Fourier–Motzkin Farkas certificate (disagreement → soundness alarm), and a
  2000-case differential fuzz confirms the two engines agree on every verdict.
  Two independent exact procedures validating each other (the project's
  characteristic move). **Native Farkas extraction** now lets the simplex certify
  its own `unsat` from the final tableau (multipliers `1` on the violating
  slack's constraint, `−c_n` on each blocking slack's), self-checked via
  `FarkasCertificate::verify` and exercised by the differential fuzz on every
  `unsat`; Fourier–Motzkin only backs up the unreachable iteration cap. The scale
  win over Fourier–Motzkin shows only on large systems not yet in the corpus.
- Congruence-closure E-matching recorded 2026-06-13 (ADR-0016, completes track
  b): trigger matching now runs **modulo the asserted ground equalities** (proper
  E-matching). An `EGraph` builds the congruence closure over ground subterms
  (union–find seeded by top-level ground `=` conjuncts, closed under same-head /
  pairwise-equal-args), and `ematch` matches a trigger against an equivalence
  class, trying every class member at each position — so `g(x)` matches `g(c)`
  given `a=c` even when only `g(a)` is present. Sound (every ground instance is
  valid; congruence only guides which sound instances are produced); with no
  equalities classes are singletons and it reduces to syntactic matching
  (existing tests unchanged). A test refutes `forall x. f(g(x))=0 ∧ g(h(a))=c ∧
  f(c)≠0` via `x:=h(a)`, which leaf enumeration and syntactic matching both miss.
  **Track b is now complete** end to end (single/multi-var matching, nested
  chains, match index, congruence closure); a persistent incremental E-graph for
  scale is the only remaining performance refinement.
- CDCL gate (a) breadth measured 2026-06-13 (track c): a second public family
  attribution settles the breadth caveat and **reverses** the Noetzli picture. On
  `bench_ab` (285 decided `sat-bv` instances, `--jobs 1`, guarded budgets — node
  5000 / CNF 7000-var / 20000-clause; all agree, 0 replay failures) the SAT-solve
  share is **0.243** with bit-blast ~0.32 + CNF ~0.35 → `sat_dominates: false`,
  **encoding dominates**. So gate (a) is **family-dependent** (SAT-dominated on
  Noetzli ≈0.95; encoding-dominated on `bench_ab` ≈0.24 and micro ≈0.31). Per the
  methodology the custom-CDCL/VSIDS track therefore stays **deprioritized** —
  encoding reduction is the higher-value lever where SAT does not dominate, and
  CDCL tuning is justified only once gate (a) holds *and* gate (b) (a
  CaDiCaL/Kissat gap on Axeyum CNF) is measured, on SAT-dominated families. The
  measurement was run OOM-safely at `--jobs 1` with guarded budgets (the node
  guard refuses large instances before bit-blasting, so peak memory is one small
  instance — memory stayed flat); baseline
  `bench-results/baselines/qf-bv-bench_ab-sat-bv-layerattr-1s-n5000-cnf7k-20k-j1.json`.
  **This is the measure-then-decide resolution of track (c): the data says do not
  build VSIDS now.**
- Term-level `unsat` certification wired into the evidence envelope recorded
  2026-06-13 (track a, bounded slice): `produce_qf_bv_evidence` now prefers a
  **reduction-free term-level certificate** for small `QF_BV` `unsat` instances
  (combined symbol width ≤ 20 bits) — `Evidence::UnsatTermLevel { cases,
  max_total_bits }` from exhaustive evaluation over the finite symbol domain,
  trusting **only the `axeyum-ir` evaluator** (not the bit-blaster, CNF encoder,
  or SAT solver); `Evidence::check` re-enumerates to re-validate. Larger
  instances fall back to the DRAT clausal proof. This closes the term↔CNF trust
  gap **entirely** for the tractable case (the "certify beyond the clausal layer"
  goal of track a), and a backend/enumeration disagreement is a soundness alarm.
  Tests: a 4-bit `unsat` is term-level certified (16 cases) and re-checks, a
  24-bit `unsat` takes the DRAT route, and a satisfiable query fails the
  term-level evidence's `check`. The *scalable* form (a verified bit-blaster so
  large-instance `unsat` is term-level-certified) remains the lone open research
  program — there is no sound bounded slice for it short of a verified reduction.
- Scalable bit-blast **faithfulness checking** recorded 2026-06-13 (track a, the
  differential assurance layer): `axeyum_solver::check_qf_bv_faithfulness` samples
  random assignments and confirms the bit-blasted AIG (`axeyum-bv` `evaluate_roots`)
  evaluates to the **same value** as the original term (the `axeyum-ir`
  evaluator). It is the differential complement of model replay — replay checks
  the reduction for the found `sat` model; this checks faithful term computation
  on independent random inputs, the regime that matters for `unsat` (no model to
  replay). A disagreement is a *definitive* faithfulness bug with a counterexample
  (sound bug-detection); agreement across many samples is scalable evidence the
  term→AIG reduction did not distort the term. Deterministic (seeded → exactly
  reproducible); memory-safe (no corpus). Tests: faithful arithmetic/bitwise and
  division/shift terms agree over 500–1000 samples; integer terms report
  `Unsupported`. This is **not** a proof (sampling), so it does not close the
  certification gap — it is the cheap scalable assurance below the staged path
  (B trusted-reference + miter → A verified bit-blaster) in
  [scalable bit-blast certification](docs/research/07-verification/scalable-bitblast-certification.md).
- Certified bit-blasting by independent-reference miter recorded 2026-06-13
  (track a, **path B delivered** for the bitwise/Boolean/`eq`/`ite` fragment):
  `axeyum_solver::certify_bitblast_by_miter` builds one AIG holding both the
  production bit-blasting (`axeyum-bv`, copied over shared symbol-bit inputs) and
  a **separately coded reference** bit-blaster, miters their output bits
  (`OR (fast XOR ref)`), Tseitin-encodes, and refutes with
  `solve_with_drat_proof` + `check_drat`. An `unsat` miter is an **exhaustive,
  DRAT-checked** proof the two agree on *every* input — a real faithfulness
  *certificate* (not sampling), carrying the auditable `(dimacs, drat)`; a `sat`
  miter is a faithfulness bug with a witness. Sound modulo trust in the
  independent reference (so a production bug surfaces as miter `sat` — the
  two-independent-procedures pattern applied to bit-blasting). The covered
  fragment now spans bitwise/Boolean/`eq`/`bvcomp`/`ite` **plus arithmetic**
  (`bvadd`/`bvsub`/`bvneg`/`bvmul`), **all 8 comparisons** (unsigned/signed), and
  **shifts** (`bvshl`/`bvlshr`/`bvashr`) — each reference gadget textbook and
  independent of `axeyum-bv`; the width-4 miter is DRAT-`unsat`, confirming
  exhaustive agreement. Coverage then grew to the **structural** ops
  (concat/extract/zero+sign extend/rotate), **unsigned** division/remainder (a
  restoring divider with SMT-LIB divide-by-zero totality), and the **signed**
  div/rem/mod sign wrappers — so **path (B) is now complete**: any pure-`QF_BV`
  query's production bit-blasting is certifiable faithful by a DRAT-checked miter
  against the independent reference (only uninterpreted-function `apply` and
  quantifiers, which are not bit-blasted, fall outside). Tests certify
  arithmetic/comparison/shift, structural, and unsigned **and** signed div/rem/mod
  queries. This is a sound, exhaustive faithfulness certificate for the full
  `QF_BV` reduction *modulo trust in the independent reference*.
  `certify_qf_bv_unsat_end_to_end` then composes the miter (term↔AIG faithful)
  with the CNF-`unsat` DRAT (AIG/CNF unsat; Tseitin equisat by construction) into
  a single **scalable, machine-checked, end-to-end `QF_BV` `unsat` certificate** —
  the goal of track (a), realized via path (B) (a production/reference divergence
  is a soundness alarm). The independent reference is itself **grounded in the
  trusted ground evaluator**: exhaustively checked against it at width 3 over all
  inputs for every covered operator (`reference_grounding` tests), so the trust
  chain is reference ≡ evaluator (exhaustive, small width) ∧ reference ≡ production
  (miter, any width) ⟹ production faithful. **This reaches trust parity** — the
  reference, the evaluator, and `check_drat` are all exhaustively-tested-trusted,
  none formally proven, the project's uniform standard. The lone remaining item,
  path (A) — a width-parametric **verified** bit-blaster — would make the
  bit-blaster *more* trusted than the evaluator/DRAT kernel, exceeding that bar;
  it is a distinct proof-assistant-scale research item (Lean/Coq), the genuine
  fully-trusted frontier, not a bounded code increment. See
  [scalable bit-blast certification](docs/research/07-verification/scalable-bitblast-certification.md).
- Phase: **Phase 5 first pure-Rust backend slice.** M0, Phase 1, SMT-LIB
  ingestion/export, the micro-corpus benchmark harness, the public QF_BV
  baseline, and the Phase 3 query/rewrite/evidence entry contracts are
  implemented/recorded. The first default denotation-preserving canonicalizer
  is implemented in `axeyum-rewrite`, wired through the rewrite manifest, and
  checked against focused examples, deterministic generated evaluator
  equivalence, and the Z3 oracle path. Query planning has structural cache
  keys, replay-checked target-support slicing, and query-plan telemetry in
  benchmark artifacts. ADR-0006 records the Phase 4 bit-order convention and
  circuit/CNF entry contracts. The first Phase 4 code slice adds shared
  LSB-first value-to-bits helpers in `axeyum-ir` and an `axeyum-aig`
  graph/evaluator with deterministic structural hashing. The initial
  bit-lowering slice adds `axeyum-bv` for constants, symbols, Boolean
  connectives, BV bitwise operators, equality, `ite`, `bvcomp`,
  concat/extract, zero/sign extension, `bvneg`, `bvadd`, `bvsub`, and
  unsigned/signed comparisons, `bvshl`, `bvlshr`, `bvashr`, and constant
  rotates, with explicit term-bit and symbol-input maps. The CNF layer adds
  `axeyum-cnf` for simple Tseitin encoding from AIG, DIMACS I/O, CNF
  evaluation, and lift maps from CNF variables back through AIG literals. AIGER
  debug export is implemented as deterministic ASCII `aag`. The SAT adapter path
  chooses `rustsat-batsat` through RustSAT (ADR-0007), exposes a small Axeyum CNF
  SAT trait/result/assignment surface, solves raw CNF and the committed DIMACS
  micro corpus through BatSat, and replay-checks satisfying assignments through
  CNF variables, AIG node values, reconstructed symbol models, and original-term
  evaluator replay. The Phase 4 exit audit records completed gates and explicit
  deferrals: multiplication/division/remainder lowering, pure-Rust benchmark
  artifact telemetry until Phase 5, binary AIGER import/export, and proof-backed
  UNSAT. The first Phase 5 slice adds `SatBvBackend` in `axeyum-solver`: a
  native-free `SolverBackend` implementation for the supported QF_BV subset
  that composes query terms, `axeyum-bv` lowering, `axeyum-cnf` Tseitin
  encoding, `rustsat-batsat`, model reconstruction, deterministic model
  completion for unconstrained symbols, and evaluator replay before accepting
  `sat`. Unsupported lowering operators return structured
  `SolverError::Unsupported` with no oracle fallback. `axeyum-bench` now
  selects `--backend sat-bv|z3`; artifact version 11 records backend kind,
  node and CNF admission budgets, submitted query-plan mode, replay policy,
  replay-refinement round and batch limits, adaptive-batch policy/backoffs,
  refinement selection policy, optional Z3 oracle comparison, harness jobs,
  and per-instance backend stats including bit-blast/CNF timing, AIG
  nodes/inputs, and CNF variables/clauses.
  The Phase 5 public supported-slice
  differential
  baseline is recorded: under a
  1000-node admission budget, the current pure Rust path proves one public
  `sat` instance, classifies 112 larger instances as structured `unknown`, has
  zero unsupported/errors/soundness alarms, and agrees with Z3 on the one
  compared decision. A guarded-admission rerun raises the node budget to 5000
  only with explicit CNF variable/clause caps; it preserves the same one public
  decision and cleanly exposes the next candidate's CNF blow-up as
  `EncodingBudget`, so this is a diagnostics/safety improvement rather than a
  support expansion. A replay-refinement query-plan mode now solves sliced
  plans, replays models against the full query, adds failed assertions' support
  sets, and accepts `sat` only after full replay; on the public slice it
  recovers the same one decision but does not expand decisions. A
  legacy-guided encoding pass added directional signed comparisons plus sparse
  CNF encoding for private XOR and mux AIG shapes, following the same broad
  idea as Bitwuzla's AIG-to-CNF ITE recognition while keeping Axeyum's lift maps
  explicit. A follow-up sparse-CNF pass now encodes private AND trees and
  OR-of-private-AND shapes directly, tracks generated clause duplicates
  deterministically, encodes only the root-reachable AIG subgraph while still
  replaying all AIG nodes, and uses root-only polarity to omit redundant
  Tseitin directions where replay remains checkable. The next sparse-CNF pass
  now recognizes positive root-only AND trees whose leaves are private XOR
  helpers, emits bounded direct parity/equality clauses for those leaves, and
  replays the skipped XOR AIG nodes from their children. The immediate
  MobileDevice replay-refine target now advances through six replay failures
  to a seventh support set and stays below the variable cap at 5,353 variables,
  but still stops at 20,784 clauses against the committed 20,000-clause cap. A
  single-target relaxed-cap diagnostic shows this is close enough that
  admission can be raised deliberately: at 30,000 clauses and a 10s timeout,
  the MobileDevice target reaches a replayed `sat` result and agrees with Z3.
  The full public relaxed-admission artifact now expands the supported slice to
  two public `sat` decisions with no soundness alarms, but BatSat takes about
  6.4s on the MobileDevice SAT call in the 8-worker public run versus about
  0.9s for Z3. A follow-up exact-target relaxed replay-refinement diagnostic
  keeps the same two public decisions, records artifact version 9, eliminates
  node-budget unknowns in that profile, and leaves all 111 remaining unknowns
  as `EncodingBudget`; it improves the diagnostic surface but confirms the
  next work is still reducing clause/SAT cost so support expansion is not only
  bought with timeout and admission increases. An artifact version 10 adaptive
  exact-target diagnostic backs off the refinement batch when the added block
  exceeds encoding budgets; it keeps the same two public decisions and zero
  soundness alarms, but moves all remaining unknowns to precise near-cap
  `EncodingBudget` frontiers. A measured 8,500-variable sweep still leaves all
  111 remaining unknowns as `EncodingBudget`, so cap increases alone are now
  known to chase the frontier rather than expand support on this slice. A
  follow-up artifact version 11 selector diagnostic chooses failed replay
  assertions by smallest individual DAG shape instead of source order; it
  materially reduces several frontiers but still leaves the public slice at two
  decisions. Artifact version 12 now records the bounded plan-aware selection
  option and current root-direct assertion CNF encoder behavior. The
  root-direct pass removes assertion-only root variables, but same-cap and
  8,500-variable public sweeps still leave the public slice at two decisions,
  so the next support expansion still needs deeper encoding reduction, SAT cost
  reduction, or a stronger refinement-selection policy. A follow-up
  singleton budget-skip experiment was rejected: the close
  `StringMatching/string1x16.3._bit8_na6_nr3_paired.smt2` profile returned to
  the honest v12 frontier at 8,001 CNF variables after removing the skip loop,
  and a 12,000-variable/60,000-clause diagnostic still chased the frontier to
  12,063 variables rather than completing replay. Replay-refinement now maps
  full-query replay failures back to the corresponding rewritten assertion
  target, so `--rewrite default` can be combined with replay-refine planning
  without false replay-cycle soundness alarms; on the same close
  `StringMatching` diagnostic this is soundness-clean but still stops at the
  same 8,001-variable frontier. An AIG-local cleanup pass now simplifies
  absorption/consensus patterns and condition-aware mux branches before CNF
  encoding. It reduces some exposed pressure -- for example the MobileDevice
  decided target falls from 6,065 variables/24,631 clauses to 6,015
  variables/24,405 clauses, and `StringMatching/string1x16.3` advances from
  16 to 18 replay-refinement rounds before budget -- but the full public
  same-cap diagnostic remains at 2 `sat` decisions and 111
  `EncodingBudget` unknowns. A bounded CNF subsumption experiment was rejected
  after it failed to reduce the near-miss clause frontier and significantly
  increased CNF encoding time. Artifact version 13 now adds
  `--refine-select smallest-plan-greedy`, a bounded replay-refinement selector
  that rescans candidate failed assertions after each selected target so the
  adaptive-backoff prefix is planned as a growing batch. The exact-target
  scoring path now avoids rebuilding full `QueryPlan`s and uses direct target
  term statistics, which also keeps the existing plan-aware selector cheaper.
  Focused `StringMatching/string1x16.3` diagnostics show modest frontier
  pressure reduction (`8005` variables / `25518` clauses after 20 rounds vs.
  `8013` / `25958` for `smallest-plan-dag` and `8017` / `25687` for
  `smallest-dag` under the same 1s focused profile), but this is not yet a
  public support expansion.
- Git: work is on `main`. Check live cleanliness with
  `git status --branch --short` when resuming; the last packaged hardening
  commit before this planning pass was `49c3a83`.
- Supporting scaffold: corpus tier directories (`corpus/micro|client`
  committed, `corpus/public` gitignored), dependabot (cargo + actions
  weekly), CHANGELOG, .editorconfig, CITATION.cff, PR template, justfile
  (`just check`), docs link checker (`scripts/check-links.sh`, also a CI
  job); 23 reference repos cloned locally (incl. proving horizon: cvc5,
  vampire, eprover, lean4, ethos, lean-smt, nanoda_lib).
- Public corpus fetcher works: `scripts/fetch-corpus.sh` (verified Zenodo
  sources — SMT-LIB 2024 QF_BV/QF_ABV, HWMCC'24 BTOR2, SAT Comp 2024 main);
  QF_ABV fetched and extracted locally (3.4 GB under `corpus/public/`).
- Phase 2 public baseline recorded 2026-06-11:
  [bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json](bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json)
  over SMT-LIB 2024 non-incremental `QF_BV/20221214-p4dfa-XiaoqiChen`
  (113 files, timeout 1000 ms, Z3 4.13.3.0, corpus hash
  `021a6a885828fd6e`, config hash `149d3992edbc7617`, artifact version 3):
  3 sat, 0 unsat,
  110 unknown/timeouts, 0 unsupported, 0 errors, 3 status agreements,
  0 disagreements, 0 model replay failures, PAR-2 mean 1.960 s. The
  artifact includes source provenance, selected family list, shape metrics,
  query-plan telemetry, and empty unsupported/error triage lists. Its
  first-assertion slice probe records 113 sliced instances, 755,480 dropped
  terms, DAG nodes from 8,706,521 to 336,691, and tree nodes from 58,335,915
  to 2,307,699. Reproduce with `just bench-public-qfbv-baseline` after
  fetching `qf_bv`.
- Phase 3 rewrite baseline recorded 2026-06-11:
  [bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json](bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json)
  over the same public QF_BV slice with `--rewrite default` (artifact version
  3, config hash `017207bdf942f35b`): 113 files, 3 sat, 110 unknown/timeouts,
  0 unsupported, 0 errors, 3 status agreements, 0 disagreements,
  0 model replay failures, 0 rewrite decision changes, 0 sat/unsat conflicts,
  PAR-2 mean 1.961 s. The default canonicalizer changed all 113 instances,
  applied 255,551 `bool.and_identity.v1` rules, reduced total DAG nodes from
  8,706,521 to 8,450,857 (2.94%), and reduced total tree nodes from
  58,335,915 to 57,824,813 (0.88%). The artifact also carries the same
  query-plan telemetry as the no-rewrite baseline: 113 sliced first-assertion
  probes and 755,480 dropped terms. Reproduce with `just
  bench-public-qfbv-rewrite` after fetching `qf_bv`.
- Phase 5 public `sat-bv` differential baseline recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 5, backend
  `sat-bv`, Z3 comparison enabled, timeout 1000 ms, node budget 1000, corpus
  hash `021a6a885828fd6e`, config hash `de49a48fe0141b11`): 113 files, 1 sat,
  0 unsat, 112 structured unknowns from node-budget admission, 0 unsupported,
  0 errors, 0 status disagreements, 0 model replay failures, 1 Z3 oracle
  decision agreement, 0 oracle disagreements, 112 oracle skips, PAR-2 mean
  1.983 s. The decided instance is
  `Composition/simple_bit8_na1_nr1_twocond.smt2`, with 310 AIG inputs,
  6,761 AIG nodes, 6,760 CNF variables, 19,421 CNF clauses, 7.1 ms
  bit-blasting, and 2.2 ms CNF encoding. The first unknown is
  `Composition/compose.p2._bit8_na6_nr3_paired.smt2` with
  `NodeBudget: query has 22012 DAG nodes, budget 1000`. Reproduce with
  `just bench-public-qfbv-sat-bv-compare` after fetching `qf_bv`.
- Phase 5 guarded-admission `sat-bv` differential run recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 7, backend
  `sat-bv`, Z3 comparison enabled, timeout 1000 ms, full query plan, node
  budget 5000, CNF variable budget 7000, CNF clause budget 20000, corpus hash
  `021a6a885828fd6e`, config hash `bce5c5f92923baf7`): 113 files, 1 sat,
  0 unsat, 112 structured unknowns (111 `NodeBudget`, 1 `EncodingBudget`),
  0 unsupported, 0 errors, 0 status disagreements, 0 model replay failures,
  1 Z3 oracle decision agreement, 0 oracle disagreements, 112 oracle skips,
  PAR-2 mean 1.983 s. The decided instance remains
  `Composition/simple_bit8_na1_nr1_twocond.smt2`, with 310 AIG inputs,
  6,539 AIG nodes, 3,904 CNF variables, 12,170 CNF clauses, 6.8 ms
  bit-blasting, and 2.6 ms CNF encoding. The newly admitted next candidate is
  safely refused before SAT solve:
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` reports
  `EncodingBudget: CNF has 11906 variables, budget 7000` after 773 AIG
  inputs, 20,431 AIG nodes, 11,906 CNF variables, and 37,865 CNF clauses.
  Reproduce with `just bench-public-qfbv-sat-bv-guarded` after fetching
  `qf_bv`.
- Phase 5 replay-refinement diagnostic run recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 7, backend
  `sat-bv`, Z3 comparison enabled, timeout 1000 ms, query plan
  `replay-refine`, 16 refinement rounds, node budget 5000, CNF variable budget
  7000, CNF clause budget 20000, corpus hash `021a6a885828fd6e`, config hash
  `cfb590ef5acd7763`): 113 files, 1 sat, 0 unsat, 112 structured unknowns
  (95 `EncodingBudget`, 17 `NodeBudget`), 0 unsupported, 0 errors, 0 status
  disagreements, 0 model replay failures, 1 Z3 oracle decision agreement, 0
  oracle disagreements, 112 oracle skips, PAR-2 mean 1.984 s. The mode
  recovers the known `Composition/simple_bit8_na1_nr1_twocond.smt2` decision
  after 11 refinement rounds and full replay. It reduces submitted query shape
  substantially across the public slice (8,706,521 original DAG nodes to
  364,804 submitted DAG nodes; 753,562 dropped terms) but still does not decide
  the MobileDevice targets under the current CNF caps. On the immediate
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` target, sparse CNF
  lets replay-refinement expose a fourth support set before budget refusal:
  83 submitted terms, 881 DAG nodes, 374 AIG inputs, 13,033 AIG nodes, 7,888
  CNF variables, and 25,197 CNF clauses. A relaxed diagnostic at CNF caps
  9000/30000 exposes a fifth support set and still refuses at 9,414 variables,
  so the next bottleneck remains encoding growth rather than a SAT timeout.
  This closes the "replayable query-planning/model-extension" hypothesis for
  the immediate Phase 5 gate unless paired with additional encoding/SAT
  improvements.
  Reproduce with `just bench-public-qfbv-sat-bv-replay-refine` after fetching
  `qf_bv`.
- Phase 5 exact-target relaxed replay-refinement diagnostic run recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 9, backend
  `sat-bv`, Z3 comparison enabled, timeout 10000 ms, query plan
  `replay-refine-exact`, 64 refinement rounds, batch size 64, node budget
  5000, CNF variable budget 8000, CNF clause budget 30000, 8 corpus workers,
  corpus hash `021a6a885828fd6e`, config hash `51c2fa6f2d4029b2`): 113 files,
  2 sat, 0 unsat, 111 structured unknowns (all `EncodingBudget`), 0
  unsupported, 0 errors, 0 status disagreements, 0 model replay failures, 2
  Z3 oracle decision agreements, 0 oracle disagreements, 111 oracle skips, and
  PAR-2 mean 19.680 s. The mode reduces submitted public query shape from
  8,706,521 original DAG nodes to 237,924 submitted DAG nodes and removes
  `NodeBudget` unknowns from this diagnostic profile, but it does not expand
  the public decision count beyond the relaxed support-slice artifact. The
  MobileDevice decision reaches full replay with 6,302 CNF variables, 25,020
  clauses, 8 refinement rounds, 3,301 ms BatSat solve time, and 1,097 ms Z3
  oracle solve time. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact` after fetching `qf_bv`.
- Phase 5 adaptive exact-target replay-refinement diagnostic run recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  over the same SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` slice (artifact version 10, backend
  `sat-bv`, Z3 comparison enabled, timeout 10000 ms, query plan
  `replay-refine-exact`, adaptive batch enabled, 64 refinement rounds, maximum
  batch size 64, node budget 5000, CNF variable budget 8000, CNF clause budget
  30000, 8 corpus workers, corpus hash `021a6a885828fd6e`, config hash
  `a55c720512d0570b`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, 111 oracle skips, and PAR-2 mean 19.680 s. The run does not
  expand the public decision count, but all 111 remaining unknowns perform
  adaptive backoff (661 total backoffs, max 6 per instance) and end at precise
  near-cap encodings instead of coarse batch cliffs: the largest final unknown
  is `TCP/tcp_full_bit16_na13_nr4_paired.smt2` at 8,495 CNF variables and
  29,059 clauses. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive` after fetching
  `qf_bv`.
- Phase 5 adaptive exact-target 8,500-variable admission sweep recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k5-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-10s-n5000-cnf8k5-30k-r64-b64-j8.json)
  over the same public slice (artifact version 10, config hash
  `987a97e59bb26f91`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, and PAR-2 mean 19.680 s. Raising the variable cap from 8000
  to 8500 under adaptive batching did not move the bottleneck to BatSat
  timeouts or expand public decisions; the remaining cases again stop just past
  the new cap (for example `compose.p3` at 8,506 variables and `string1x16.3`
  at 8,501 variables), with one clause-cap near miss
  (`mobiledevice_bit8_na6_nr3_twocond.smt2` at 8,422 variables and 30,193
  clauses). This confirms that cap increases alone are now chasing the
  replay-refinement frontier and the next support expansion needs encoding
  reduction or a better refinement-selection policy. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-cnf8k5` after
  fetching `qf_bv`.
- Phase 5 root-direct/smallest-DAG adaptive exact-target replay-refinement
  diagnostic run
  recorded 2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  over the same public slice (artifact version 12, backend `sat-bv`, Z3
  comparison enabled, timeout 10000 ms, query plan `replay-refine-exact`,
  adaptive batch enabled, refinement selection `smallest-dag`, 64 refinement
  rounds, maximum batch size 64, node budget 5000, CNF variable budget 8000,
  CNF clause budget 30000, 8 corpus workers, config hash
  `7a3d9688adaa7703`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, and PAR-2 mean 19.734 s. Version 12 removes dedicated CNF
  variables for assertion-only AIG roots and records the bounded
  `smallest-plan-dag` selector option; the public run remains
  soundness-clean but still does not expand support. Final unknowns range from
  8,001 to 8,491 CNF variables; the largest same-cap frontier is
  `StringMatching/string4x16.4._bit16_na6_nr4_paired.smt2` at 8,491
  variables/29,191 clauses. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest` after
  fetching `qf_bv`.
- Phase 5 root-direct/smallest-DAG adaptive 8,500-variable admission sweep
  recorded
  2026-06-12:
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k5-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-adaptive-smallest-10s-n5000-cnf8k5-30k-r64-b64-j8.json)
  over the same public slice (artifact version 12, config hash
  `ae175e9a94773059`): 113 files, 2 sat, 0 unsat, 111 structured unknowns
  (all `EncodingBudget`), 0 unsupported, 0 errors, 0 status disagreements,
  0 model replay failures, 2 Z3 oracle decision agreements, 0 oracle
  disagreements, and PAR-2 mean 19.736 s. With root-direct encoding and the
  selector enabled, raising the variable cap to 8,500 again moves rather than
  removes the frontier: the remaining unknowns range from 8,144 to 8,827
  variables, and no instance moves to `Timeout` or replayed `sat`. This keeps
  the next work centered on encoding reduction and stronger refinement
  selection rather than broader cap increases. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact-adaptive-smallest-cnf8k5`
  after fetching `qf_bv`.
- Phase 3 exit audit recorded 2026-06-11:
  [phase3-exit-audit](docs/research/08-planning/phase3-exit-audit.md)
  ties the roadmap exit criteria to concrete evidence: generated rewrite
  equivalence coverage, manifest guards against default non-denotational
  rewrites, Z3 rewrite differential tests, public rewrite measurement, query
  structural-cache/slicing replay tests, and micro/public query-plan artifact
  telemetry.
- North star recorded 2026-06-10: complete framework for general
  reasoning/logic/proving — see
  [north-star](docs/research/00-orientation/north-star.md), the horizon
  ladder in logics-and-decidability, the roadmap's "Beyond Phase 7"
  markers, and the horizon section of the research-questions register.
  Key landscape facts: Vampire (BSD-3) swept CASC-30 2025; cvc5
  CPC/Eunoia/Ethos is the proof-production leader; nanoda is the Rust
  Lean-kernel precedent; no Rust superposition prover or general proof
  kernel exists — that gap is the opportunity.
- Foundational planning refinement recorded 2026-06-11: the roadmap is now
  subordinate to a step-by-step
  [foundational logic and math DAG](docs/research/08-planning/foundational-dag.md)
  from semantics to typed IR, evaluator, import/export, oracle baseline,
  rewrites, bit lowering, CNF, SAT, pure Rust BV, evidence, and later
  theories. Use that note before adding public operators, rewrites,
  encodings, backends, proof artifacts, or logic fragments.
- Workspace: `axeyum-ir`, `axeyum-aig`, `axeyum-bv`, `axeyum-cnf`,
  `axeyum-query`, `axeyum-rewrite`, `axeyum-scenarios`, `axeyum-solver`,
  `axeyum-smtlib`, and
  `axeyum-bench`, edition 2024, MSRV 1.85, workspace lints (`unsafe_code`
  denied, clippy pedantic). CI workflow covers fmt, clippy, tests,
  micro-corpus benchmark smoke, MSRV check, rustdoc, cargo-deny, and docs
  links.
- Project metadata: README, CONTRIBUTING, CLAUDE.md, dual MIT/Apache-2.0
  licenses, deny.toml, rustfmt.toml.
- References: 23 solver/checker repos shallow-cloned into `references/`
  (gitignored; reproducible via `scripts/fetch-references.sh`).
- Decisions: [ADR-0001 vertical slice first](docs/research/09-decisions/adr-0001-vertical-slice-first.md),
  [ADR-0002 ground-up identity, oracle as bootstrap](docs/research/09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md),
  [ADR-0003 M0 IR representation](docs/research/09-decisions/adr-0003-m0-ir-representation.md),
  [ADR-0004 defer the second native backend](docs/research/09-decisions/adr-0004-defer-second-native-backend.md),
  [ADR-0005 Phase 3 query/evidence/rewrite contracts](docs/research/09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md),
  [ADR-0006 Phase 4 bit-order/lowering entry contract](docs/research/09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md),
  and [ADR-0007 first pure Rust SAT adapter](docs/research/09-decisions/adr-0007-first-pure-rust-sat-adapter.md)
  are **accepted**. ADR-0002 settles the Z3 question: the pure Rust stack
  (including a custom SAT core) is the product; the linked oracle is
  scaffolding with a planned demotion path (backend → differential oracle →
  CI cross-check). ADR-0004 keeps Z3 as the only Phase 2/3 native oracle and
  defers Bitwuzla/other linked backends until Phase 5 needs concrete
  differential or trait-shape pressure. ADR-0005 makes `axeyum-query` the
  assertions/assumptions/scope boundary and `axeyum-rewrite` the manifest
  boundary; default rewrites must remain denotation-preserving until model
  projection is implemented and replay-tested. ADR-0006 makes BV wire vectors
  LSB-first, requires shared value/model conversion helpers, chooses AIG before
  simple Tseitin CNF, and requires explicit lift maps back to original-query
  replay. ADR-0007 chooses `rustsat-batsat` through RustSAT as the first
  pure-Rust CNF/SAT adapter and keeps UNSAT lower-assurance until proof output
  and checking exist.
- Ecosystem facts checked 2026-06-10: stable Rust 1.96; z3 crate 0.20
  removed the `'ctx` lifetime API; varisat unmaintained since 2019 (splr and
  rustsat are the maintained Rust SAT options).
- SAT adapter refresh checked 2026-06-11: `rustsat` 0.7.5 and
  `rustsat-batsat` 0.7.5 declare Rust 1.76 MSRV and fit Axeyum's Rust 1.85
  MSRV; `rustsat-batsat` is pure Rust and is now the first adapter
  (ADR-0007). `splr` and `varisat` remain benchmark/proof-path candidates, not
  the default adapter.
- Local verification for the 2026-06-11 Phase 3 exit hardening pass:
  `cargo fmt --all --check`, `cargo clippy --workspace --all-targets
  --all-features -- -D warnings`, `cargo test --workspace --all-features`,
  `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features
  --no-deps`, `./scripts/check-links.sh`, `git diff --check`, `cargo run -p
  axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite
  default --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The micro
  query-plan summary records 3 files, 1 sliced instance, 1 dropped term, and
  original-to-sliced DAG/tree totals of 14→12 and 15→12. The public QF_BV
  baseline and rewrite artifacts above were regenerated with the current
  schema and both pass with 0 disagreements and 0 model replay failures.
  `cargo deny check` was not run locally because `cargo-deny` is not
  installed; `just --list` was not run because `just` is not installed in this
  environment.
- Local verification for the 2026-06-11 Phase 4 entry-contract pass:
  `./scripts/check-links.sh` and `git diff --check` pass. No Rust code changed
  in this pass.
- Local verification for the 2026-06-11 Phase 4 first implementation slice:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro query-plan summaries remain stable: 3 files, 1 sliced
  instance, 1 dropped term, and original-to-sliced DAG/tree totals of 14→12
  and 15→12. `cargo deny check` was not run locally because `cargo-deny` is
  not installed; `just --list` was not run because `just` is not installed in
  this environment.
- Local verification for the 2026-06-11 Phase 4 structural bit-lowering pass:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro artifacts record 3 files, 2 sat, 1 unsat, 3 status
  agreements, 0 disagreements, 0 model replay failures, 1 sliced instance, 1
  dropped term, and original-to-sliced DAG/tree totals of 14→12 and 15→12.
  The rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 arithmetic/comparison
  bit-lowering pass: `cargo fmt --all --check`, `cargo check --workspace`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro artifacts record 3 files, 2 sat, 1 unsat, 3 status
  agreements, 0 disagreements, 0 model replay failures, 1 sliced instance, 1
  dropped term, and original-to-sliced DAG/tree totals of 14→12 and 15→12.
  The rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 shift/rotate bit-lowering
  pass: `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo run -p axeyum-bench --features z3 -- corpus/micro
  --timeout-ms 1000 --out /tmp/axeyum-bench-micro.json`, and the same micro
  run with `--rewrite default --out /tmp/axeyum-bench-micro-rewrite.json`,
  all pass. The micro artifacts record 3 files, 2 sat, 1 unsat, 3 status
  agreements, 0 disagreements, 0 model replay failures, 1 sliced instance, 1
  dropped term, and original-to-sliced DAG/tree totals of 14→12 and 15→12.
  The rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 CNF layer pass: `cargo fmt
  --all --check`, `cargo check --workspace`, `cargo clippy --workspace
  --all-targets --all-features -- -D warnings`, `cargo test --workspace
  --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
  --all-features --no-deps`, `./scripts/check-links.sh`, `git diff --check`,
  `cargo run -p axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000
  --out /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite
  default --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The micro
  artifacts record 3 files, 2 sat, 1 unsat, 3 status agreements,
  0 disagreements, 0 model replay failures, 1 sliced instance, 1 dropped term,
  and original-to-sliced DAG/tree totals of 14→12 and 15→12. The
  rewrite-default micro artifact records 1 changed instance, 1 rewrite
  application, 0 decision changes, and 0 sat/unsat conflicts. `cargo deny
  check` was not run locally because `cargo-deny` is not installed; `just
  --list` was not run because `just` is not installed in this environment.
- Local verification for the 2026-06-11 Phase 4 SAT adapter pass: `cargo fmt
  --all --check`, `cargo check --workspace`, `cargo clippy --workspace
  --all-targets --all-features -- -D warnings`, `cargo test --workspace
  --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
  --all-features --no-deps`, `./scripts/check-links.sh`, `git diff --check`,
  `cargo tree -p axeyum-cnf --edges normal`, `cargo run -p axeyum-bench
  --features z3 -- corpus/micro --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite default
  --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The `axeyum-cnf`
  dependency tree contains `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and
  `batsat` 0.6.0 with no native solver or C/C++ build-tool dependency in that
  crate's default tree. The micro artifacts record 3 files, 2 sat, 1 unsat,
  3 status agreements, 0 disagreements, 0 model replay failures, 1 sliced
  instance, and 1 dropped term. The rewrite-default micro artifact records
  1 changed instance, 1 rewrite application, 0 decision changes, and 0 sat/unsat
  conflicts. `cargo deny check` was not run locally because `cargo-deny` is not
  installed; `just --list` was not run because `just` is not installed in this
  environment.
- Local verification for the 2026-06-11 Phase 4 exit hardening/audit pass:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, `cargo tree -p axeyum-cnf --edges normal`, `cargo run -p
  axeyum-bench --features z3 -- corpus/micro --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro.json`, and the same micro run with `--rewrite
  default --out /tmp/axeyum-bench-micro-rewrite.json`, all pass. The
  `axeyum-aig` suite has 6 tests including deterministic ASCII AIGER export;
  `axeyum-cnf` has 9 tests including the committed DIMACS micro-corpus
  SAT-trait pass and full SAT-to-original-term replay. The `axeyum-cnf`
  dependency tree contains `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and
  `batsat` 0.6.0 with no native solver or C/C++ build-tool dependency in that
  crate's default tree. The micro artifacts record 3 files, 2 sat, 1 unsat, 3
  status agreements, 0 disagreements, 0 model replay failures, 1 sliced
  instance, and 1 dropped term. The rewrite-default micro artifact records 1
  changed instance, 1 rewrite application, 0 decision changes, and 0 sat/unsat
  conflicts. `cargo deny check` was not run locally because `cargo-deny` is not
  installed; `just --list` was not run because `just` is not installed in this
  environment.
- Local verification for the 2026-06-11 Phase 5 first pure-Rust backend slice:
  `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, `git
  diff --check`, and `cargo tree -p axeyum-solver --edges normal` all pass.
  The default `axeyum-solver` dependency tree includes `axeyum-bv`,
  `axeyum-cnf`, `rustsat` 0.7.5, `rustsat-batsat` 0.7.5, and `batsat` 0.6.0
  with no Z3/native SMT dependency. The new `sat_bv` solver test target has 8
  all-feature tests covering supported SAT/UNSAT, query assertions plus
  assumptions, deterministic model completion, explicit unsupported `BvMul`
  errors, node-budget admission control, layer stats, and Z3 decision
  differential checks. `cargo run -p axeyum-bench -- corpus/micro --backend
  sat-bv --timeout-ms 1000 --out /tmp/axeyum-bench-micro-sat-bv.json`,
  the same run with `--rewrite default --out
  /tmp/axeyum-bench-micro-sat-bv-rewrite.json`, `cargo run -p axeyum-bench
  --features z3 -- corpus/micro --backend z3 --timeout-ms 1000 --out
  /tmp/axeyum-bench-micro-z3.json`, and the same Z3 run with `--rewrite
  default --out /tmp/axeyum-bench-micro-z3-rewrite.json` all pass. Each micro
  run records 3 files, 2 sat, 1 unsat, 3 status agreements, 0 disagreements,
  and 0 model replay failures; rewrite-default runs record 1 changed instance,
  1 rewrite application, 0 decision changes, and 0 sat/unsat conflicts. The
  `sat-bv` artifact is version 4 and includes backend stats such as
  `bit_blast_ms`, `cnf_encode_ms`, `aig_nodes`, `aig_inputs`, `cnf_variables`,
  and `cnf_clauses`; that schema later became version 5 with node-budget
  provenance and optional Z3 oracle comparison, and version 6 with CNF-budget
  and query-plan provenance. `cargo deny check` was not run locally because
  `cargo-deny` is not installed; `just --list` was not run because `just` is
  not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 public supported-slice
  differential baseline: `cargo fmt --all --check`, `cargo check
  --workspace`, `cargo clippy --workspace --all-targets --all-features` with
  `-D warnings`, `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The micro `sat-bv` run with `--compare-z3`,
  `--timeout-ms 1000`, and `--node-budget 1000` passes with 3 files, 2 sat,
  1 unsat, 0 unknown, 0 unsupported/errors, 3 Z3 oracle agreements, 0 oracle
  disagreements, and 0 model replay failures. The public baseline artifact
  above was generated with the new `just bench-public-qfbv-sat-bv-compare`
  command body and passed with 113 files, 1 sat, 112 unknown, 0
  unsupported/errors, 1 Z3 oracle agreement, 0 oracle disagreements, and 0
  model replay failures. `cargo deny check` was not run locally because
  `cargo-deny` is not installed; `just --list` was not run because `just` is
  not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 guarded-admission/CNF-budget
  diagnostics pass: `cargo fmt --all --check`, `cargo check --workspace`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. Focused `cargo check -p axeyum-bench --features
  z3` and `cargo test -p axeyum-solver --test sat_bv --features z3` pass; the
  `sat_bv` target has 11 tests including timeout classification and CNF-budget
  refusal before SAT solve. The micro v6 `sat-bv` run with `--compare-z3`,
  `--timeout-ms 1000`, `--node-budget 1000`, `--cnf-var-budget 7000`, and
  `--cnf-clause-budget 20000` passes with 3 files, 2 sat, 1 unsat, 0 unknown,
  0 unsupported/errors, 3 Z3 oracle agreements, 0 oracle disagreements, and 0
  model replay failures. The guarded public artifact above was regenerated with
  the current version 6 schema and passed with 113 files, 1 sat, 112 unknown
  (111 `NodeBudget`, 1 `EncodingBudget`), 0 unsupported/errors, 1 Z3 oracle
  agreement, 0 oracle disagreements, and 0 model replay failures. `cargo deny
  check` and the `just` wrapper targets were not run locally because
  `cargo-deny` and `just` are not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 replay-refinement diagnostic
  pass: `cargo fmt --all --check`, `cargo check --workspace`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The micro v7 full-plan `sat-bv` run with
  `--compare-z3`, `--timeout-ms 1000`, `--node-budget 1000`,
  `--cnf-var-budget 7000`, and `--cnf-clause-budget 20000` passes with
  3 files, 2 sat, 1 unsat, 0 unknown, 0 unsupported/errors, 3 Z3 oracle
  agreements, 0 oracle disagreements, and 0 model replay failures. The same
  micro run with `--query-plan replay-refine --refine-rounds 16` also passes
  with 3 files, 2 sat, 1 unsat, 3 Z3 oracle agreements, 0 disagreements, and
  0 model replay failures, while exercising one sliced/refined instance. The
  guarded full public artifact was regenerated under artifact version 7 and
  still records 113 files, 1 sat, 112 unknown (111 `NodeBudget`, 1
  `EncodingBudget`), 0 unsupported/errors, 1 Z3 oracle agreement, 0 oracle
  disagreements, and 0 model replay failures. The replay-refine public
  diagnostic artifact records 113 files, 1 sat, 112 unknown (95
  `EncodingBudget`, 17 `NodeBudget`), 0 unsupported/errors, 1 Z3 oracle
  agreement, 0 oracle disagreements, and 0 model replay failures. `cargo deny
  check` and the `just` wrapper targets were not run locally because
  `cargo-deny` and `just` are not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 legacy-guided sparse-CNF pass:
  reviewed cvc5's ITE simplification/removal path and Bitwuzla's AIG-to-CNF
  ITE detection, added directional signed-comparison lowering, a developer
  replay-refinement profile example, and sparse CNF encoding for private
  XOR/mux AIG helper nodes. `cargo fmt --all --check`, `cargo check
  --workspace`, workspace clippy with all targets/all features and
  `-D warnings`, `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"` and `--workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` all pass. Focused
  `cargo test -p axeyum-bv`, `cargo test -p axeyum-cnf`, `cargo test -p
  axeyum-solver --test sat_bv --features z3`, and `cargo check -p
  axeyum-bench --examples --features z3` also pass. The micro full-plan
  `sat-bv` vs Z3 run and the micro replay-refine `sat-bv` vs Z3 run pass. The
  guarded and replay-refine public artifacts above were regenerated and remain
  soundness-clean: 113 files, 1 `sat`, 112 `unknown`, 0
  unsupported/errors/model replay failures/oracle disagreements. The immediate
  MobileDevice replay-refine target improved to 7,888 CNF variables and 25,197
  clauses at the fourth support set, but still exceeds the committed CNF caps.
  `cargo deny check` and the `just` wrapper targets were not run locally because
  `cargo-deny` and `just` are not installed in this environment.
- Local verification for the 2026-06-12 Phase 5 reachable/sparse-CNF follow-up:
  added private AND-tree flattening, direct OR-of-private-AND encoding,
  deterministic generated-clause normalization/deduplication, root-reachable
  CNF planning/allocation/encoding, full-AIG replay for unencoded dead nodes,
  root-only polarity clause trimming, and constant-sign signed-comparison
  simplification. `cargo fmt --all --check`, `cargo check --workspace`,
  workspace clippy with all targets/all features and `-D warnings`,
  `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"` and `--workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` pass. Focused
  `cargo test -p axeyum-bv`, `cargo test -p axeyum-cnf`, and
  `cargo test -p axeyum-solver --test sat_bv --features z3` also pass. The
  immediate MobileDevice replay-refine profile now advances through four
  replay failures to a fifth support set: 141 planned terms, 1,026 submitted
  DAG nodes, 677 AIG inputs, 14,845 AIG nodes, 5,727 CNF variables, and 21,637
  clauses. A single-target benchmark with the committed
  7000-variable/20000-clause caps remains soundness-clean but still returns
  structured `EncodingBudget`, now on the clause cap rather than the variable cap:
  1 file, 0 sat, 1 unknown, 0 unsupported/errors/model replay failures/oracle
  disagreements. Full public artifact regeneration remains pending until the
  next reduction can plausibly expand the public decision count.
- Local verification for the 2026-06-12 Phase 5 positive-root equality CNF
  pass: added direct bounded parity/equality clauses for positive root-only
  AND-tree leaves backed by private XOR helpers, while keeping skipped XOR AIG
  nodes replayable from their children. `cargo fmt --all --check`, `cargo
  check --workspace`, workspace clippy with all targets/all features and
  `-D warnings`, `cargo test --workspace --all-features`, rustdoc with
  `RUSTDOCFLAGS="-D warnings"` and `--workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` pass. Focused `cargo
  test -p axeyum-bv`, `cargo test -p axeyum-cnf`, and `cargo test -p
  axeyum-solver --test sat_bv --features z3` also pass. The micro
  replay-refine `sat-bv` vs Z3 run passes with 3 files, 2 `sat`, 1 `unsat`, 3
  oracle agreements, 0 disagreements, and 0 model replay failures. The full
  public replay-refine run remains soundness-clean but does not expand the
  public decision count: 113 files, 1 `sat`, 112 `unknown` (95
  `EncodingBudget`, 17 `NodeBudget`), 0 unsupported/errors/model replay
  failures/oracle disagreements, and 1 Z3 oracle agreement. The immediate
  MobileDevice target now advances through six replay failures to a seventh
  support set before the committed clause cap stops it: 175 planned terms,
  1,084 submitted DAG nodes, 773 AIG inputs, 16,341 AIG nodes, 5,353 CNF
  variables, and 20,784 clauses. This is encoding progress and better
  diagnostics, not a public support expansion yet.
- Local diagnostic for the 2026-06-12 Phase 5 relaxed-cap check: the immediate
  MobileDevice replay-refine target was rerun as a one-file corpus with node
  budget 5000, CNF variable budget 7000, Z3 comparison enabled, and unchanged
  replay checking. At 25,000 clauses and a 1s timeout it builds a
  6,292-variable/24,963-clause SAT instance but returns structured `Timeout`.
  At 25,000 clauses and a 10s timeout it advances one more replay failure and
  then hits `EncodingBudget` at 25,046 clauses. At 30,000 clauses and a 10s
  timeout it reaches checked `sat` after 9 replay failures/10 rounds with
  6,312 CNF variables, 25,054 clauses, 19,351 AIG nodes, 47 ms model lift,
  5,295 ms BatSat solve time, full replay, and Z3 agreement. This proves
  raising the clause cap is a viable admission lever, but does not by itself
  close the performance gap.
- Local diagnostic for the 2026-06-12 Phase 5 benchmark parallelism and
  relaxed public run: `axeyum-bench` now has an explicit `--jobs N` corpus
  worker knob. `--jobs 1` remains the default; `--jobs 2` on the committed
  micro corpus preserved sorted file order, outcomes, oracle agreements, and
  replay cleanliness compared with `--jobs 1` apart from expected timing/hash
  changes. The committed artifact
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json)
  records the full public relaxed-admission profile: artifact version 8,
  113 files, 2 `sat`, 111 `unknown` (94 `EncodingBudget`, 17 `NodeBudget`),
  0 unsupported/errors/model replay failures/oracle disagreements, 2 Z3 oracle
  agreements, 8 corpus workers, 10s timeout, node budget 5000, CNF variable
  budget 7000, and CNF clause budget 30000. The newly decided public instance
  is `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2`, with 6,312 CNF
  variables, 25,054 clauses, 10 replay-refinement rounds, 6,429 ms BatSat
  solve time in the contended public run, and 923 ms Z3 oracle solve time.
  Local validation for this pass: `cargo fmt --all --check`, `cargo check -p
  axeyum-bench --examples --features z3`, `cargo clippy -p axeyum-bench
  --all-targets --features z3 -- -D warnings`, micro `sat-bv` vs Z3 runs with
  `--jobs 1` and `--jobs 2`, `cargo clippy --workspace --all-targets
  --all-features -- -D warnings`, `cargo test --workspace --all-features`,
  `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps`,
  `./scripts/check-links.sh`, and `git diff --check` all pass. `cargo deny
  check` was not run locally because `cargo-deny` is not installed.
- Local diagnostic for the 2026-06-12 Phase 5 exact-target relaxed
  replay-refinement run: `axeyum-bench` now supports
  `--query-plan replay-refine-exact`, which submits only exact target
  assertions per refinement round and relies on full original-query replay
  before accepting `sat`. `--refine-batch N` can add multiple failed original
  assertions from the same candidate model to the next round. The committed
  artifact
  [bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json](bench-results/baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json)
  records the full public exact-target relaxed profile: artifact version 9,
  113 files, 2 `sat`, 111 `unknown` (all `EncodingBudget`), 0
  unsupported/errors/model replay failures/oracle disagreements, 2 Z3 oracle
  agreements, 8 corpus workers, 10s timeout, node budget 5000, CNF variable
  budget 8000, CNF clause budget 30000, 64 refinement rounds, and batch size
  64. The run reduces submitted public query shape to 237,924 DAG nodes and
  removes the node-budget unknown class for this diagnostic profile, but does
  not expand decisions beyond the version 8 relaxed support-slice artifact.
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` reaches full replay
  with 6,302 CNF variables, 25,020 clauses, 8 refinement rounds, 3,301 ms
  BatSat solve time, and 1,097 ms Z3 oracle solve time. Local validation for
  this pass: `cargo fmt --all --check`, `cargo check -p axeyum-bench
  --examples --features z3`, `cargo test -p axeyum-query`, `cargo clippy -p
  axeyum-bench --all-targets --features z3 -- -D warnings`, micro
  `replay-refine-exact` `sat-bv` vs Z3 with `--jobs 2`, `cargo clippy
  --workspace --all-targets --all-features -- -D warnings`, `cargo test
  --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc
  --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The exact public artifact was regenerated with
  the current harness and remains soundness-clean with the same config hash and
  outcome profile. `cargo deny check` and `just` wrapper targets were not run
  locally because `cargo-deny` and `just` are not installed in this
  environment.
- Local diagnostic for the 2026-06-12 Phase 5 adaptive exact-target
  replay-refinement pass: `axeyum-bench` now supports
  `--refine-adaptive-batch` for replay-refinement modes. The policy is purely
  an admission/refinement heuristic: after a newly added failed-assertion batch
  trips `EncodingBudget`, the harness halves that last addition and retries,
  while still accepting `sat` only after full original-query replay. Artifact
  version 10 records the adaptive flag and per-instance `adaptive_backoffs`;
  the config hash includes the flag. The developer profile helper gained the
  matching `AXEYUM_PROFILE_ADAPTIVE_BATCH=1` mode. Focused diagnostics on
  `StringMatching/string4x16.3._bit16_na6_nr4_paired.smt2` show the static
  batch-64 exact plan jumps to 32,133 CNF variables/74,010 clauses, while
  adaptive batch-64 under the same 8000-variable/30000-clause caps ends at a
  precise 8,147-variable/26,723-clause `EncodingBudget`. The full public
  same-cap adaptive artifact remains soundness-clean but does not expand the
  supported slice: 113 files, 2 `sat`, 111 `unknown`, all unknowns
  `EncodingBudget`, 2 Z3 agreements, 0 model replay failures/oracle
  disagreements. The full public 8,500-variable sweep likewise remains
  soundness-clean with 2 `sat` and 111 `EncodingBudget` unknowns, proving this
  cap increase is not enough to expand support. Local validation for this
  pass: `cargo fmt --all --check`, `cargo check -p axeyum-bench --examples
  --features z3`, `cargo clippy -p axeyum-bench --all-targets --features z3
  -- -D warnings`, adaptive exact micro `sat-bv` vs Z3 with `--jobs 2`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. The one-file StringMatching adaptive run and
  both full public adaptive sweeps above pass with zero unsupported/errors,
  model replay failures, or oracle disagreements.
- Local diagnostic for the 2026-06-12 Phase 5 root-direct CNF and
  refinement-selection pass: `axeyum-bench` now supports
  `--refine-select first|smallest-dag|smallest-plan-dag`.
  `first` preserves the artifact version 10 source-order behavior; the new
  `smallest-dag` mode scans replay-failed original assertions, scores them by
  individual `TermStats` (`dag_nodes`, then `tree_nodes`, then `ite_count`,
  then term ID), and chooses the cheapest failed assertions for the next
  refinement batch. The new bounded `smallest-plan-dag` diagnostic first keeps
  a deterministic 64-candidate cheap-score frontier, then re-scores those
  candidates by the resulting sliced plan shape. It is heavier and did not
  diverge usefully from `smallest-dag` through the first eight rounds of the
  close `StringMatching/string2x16.6._bit8_na6_nr3_paired.smt2` diagnostic, so
  it is not the current public default. The config hash includes the selector
  and artifact version 12 records it. The developer profile helper gained
  matching `AXEYUM_PROFILE_REFINE_SELECT` support. Focused profiles show real
  frontier reduction on expensive source-order choices: TCP full falls from
  8,495 variables/29,059 clauses to 8,095 variables/21,622 clauses under the
  same caps, and `compose.p2` falls from 8,068 variables/18,814 clauses to
  8,029 variables/18,632 clauses before the root-direct pass. The root-direct
  CNF encoder removes dedicated variables for assertion-only roots and keeps
  AIG replay intact; focused unit tests cover positive and negative direct
  roots. The full public same-cap v12 artifact remains soundness-clean but
  still records 2 `sat` and 111 `EncodingBudget` unknowns, with remaining
  unknowns from 8,001 to 8,491 variables. The full public 8,500-variable v12
  sweep likewise leaves 2 `sat` and 111 `EncodingBudget` unknowns, with
  remaining unknowns from 8,144 to 8,827 variables and no SAT timeouts. This
  confirms root-direct encoding, smallest-DAG selection, and a moderate cap
  increase are useful diagnostics/pressure reductions but not a support
  expansion. Local validation for this pass: `cargo test -p axeyum-aig -p
  axeyum-cnf`, `cargo check -p axeyum-bench --examples --features z3`,
  micro `sat-bv` vs Z3 replay-refine-exact with
  `--refine-select smallest-plan-dag`, `cargo clippy --workspace
  --all-targets --all-features -- -D warnings`, `cargo test --workspace
  --all-features`, `RUSTDOCFLAGS="-D warnings" cargo doc --workspace
  --all-features --no-deps`, `./scripts/check-links.sh`, and
  `git diff --check` all pass. `cargo deny check` was attempted but
  `cargo-deny` is not installed in this environment.
- Local verification for the 2026-06-12 replay-refinement rewrite-target fix
  and singleton budget-skip rejection: `cargo fmt --all`,
  `cargo check -p axeyum-bench --examples --features z3`, `cargo test -p
  axeyum-cnf`, `cargo test -p axeyum-bench --features z3`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`, and
  `cargo test --workspace --all-features` all pass. The micro
  replay-refine-exact `sat-bv` vs Z3 run passes both with rewrite off and
  with `--rewrite default`, and the one-file rewritten
  `StringMatching/string1x16.3._bit8_na6_nr3_paired.smt2` diagnostic now ends
  as a structured `EncodingBudget` unknown with 0 model replay failures instead
  of a false replay-cycle alarm.
- Local diagnostic for the 2026-06-12 AIG simplification pass: `axeyum-aig`
  now simplifies AND absorption, OR-consensus, and condition-aware mux branches
  while preserving deterministic structural hashing and AIG replay. Focused
  tests cover the new Boolean identities. The final full public
  smallest-DAG/adaptive/exact-target diagnostic at 10s / 5000 nodes /
  8000 CNF variables / 30000 CNF clauses / 8 jobs remains soundness-clean:
  113 files, 2 `sat`, 111 `EncodingBudget` unknowns, 0 unsupported, 0 errors,
  0 model replay failures, and 2 Z3 agreements. Notable frontier changes:
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` is still `sat` with
  6,015 variables and 24,405 clauses; `StringMatching/string1x16.3` reaches
  18 replay-refinement rounds before stopping at 8,017 variables; and
  `StringMatching/string4x8.7._bit8_na6_nr3_paired.smt2` remains a clause
  near-miss at 7,990 variables and 30,003 clauses. The rejected bounded CNF
  subsumption experiment left this clause frontier unchanged while raising
  CNF encode time, so it was removed. Local validation: `just check` could
  not run because `just` is not installed; the underlying gates
  `cargo fmt --all --check`, `cargo clippy --workspace --all-targets
  --all-features -- -D warnings`, `cargo test --workspace --all-features`,
  `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps`,
  and `./scripts/check-links.sh` all pass.
- Local diagnostic for the 2026-06-12 greedy refinement-selector pass:
  `axeyum-bench` now accepts `--refine-select smallest-plan-greedy`, the
  replay-refine profile accepts
  `AXEYUM_PROFILE_REFINE_SELECT=smallest-plan-greedy`, and artifact version 13
  records the new selection policy. A regression test proves the greedy
  selector rescans after each selected failed assertion and can prefer a larger
  individual assertion when it reuses the already-selected subgraph. Focused
  `StringMatching/string1x16.3._bit8_na6_nr3_paired.smt2` diagnostics at
  exact/adaptive/batch-64, 1s timeout, node budget 5000, and CNF caps
  8000/30000 completed quickly after the exact-target scoring shortcut:
  `smallest-plan-greedy` stops at 8,005 variables / 25,518 clauses after 20
  rounds, compared with 8,013 / 25,958 for `smallest-plan-dag` and
  8,017 / 25,687 for `smallest-dag`. The user requested commit/push before a
  full public v13 artifact run, so this remains focused evidence only. Local
  validation after the final selector cleanup: `cargo fmt --all --check`,
  `cargo clippy --workspace --all-targets --all-features -- -D warnings`,
  `cargo test --workspace --all-features`, `RUSTDOCFLAGS="-D warnings" cargo
  doc --workspace --all-features --no-deps`, and `./scripts/check-links.sh`
  all pass.

## Next Actions

In order; check off and date as completed.

### The road ahead (re-anchored on the real north star, 2026-06-13)

Destination (1) **foundation** is built. The remaining destinations, in order:

- [ ] **Destination 2 — complete solver replacement (the next big goal).**
      The binding constraint is **performance on real corpora**, not theory
      breadth. Concretely, in rough order:
  - [ ] **Honest baseline first.** Write `docs` capability-and-performance gap
        assessment vs an angr+Z3 baseline on a fixed public set; pick the
        decided-instance count + PAR-2 as the headline metric. (Do NOT hand-wave
        progress without this number.)
  - [ ] **A real CDCL(T) loop** (theory propagation + cross-theory conflict
        learning) replacing the current eager-eliminate-then-bit-blast
        composition where it pays; plus the encoding/preprocessing and SAT-core
        work the methodology gates on. Goal: decide *most* of a public QF_BV
        family, not ~2 instances.
  - [ ] **Theory breadth to SMT-LIB parity:** unbounded `LIA`/`LRA` (real
        simplex + branch-and-bound, retiring bounded bit-blasting as the only
        path), floating point, strings/sequences, datatypes, nonlinear; and
        production quantifier instantiation (E-matching + MBQI).
  - [ ] **Surface + validation:** full SMT-LIB 2 command set, scale incremental,
        run SMT-COMP corpora (OOM-safely: `--jobs 1`, guarded budgets — see
        memory `avoid-public-benchmark-runs`).
- [ ] **Destination 3 — Lean / angr as first-class functionality.** After (2):
  - [ ] **angr/unicorn class:** a binary/IR frontend (lift + CFG), a real memory
        model, and symbolic execution + concrete emulation as first-class APIs
        for constrained program optimization and verification (the current
        register-VM consumer test is the *shape*, not the product).
  - [ ] **Lean class:** grow the evidence envelope into kernel-checkable proof
        terms + an independent Rust kernel; proof-assistant interop
        (export obligations / import checked rules); then dependent-type proving.

Everything below `### Foundation work (destination 1)` is the completed/ongoing
foundation; the items above are the actual product trajectory.

### Foundation work (destination 1)

- [x] Review and accept (or amend) ADR-0001 — accepted 2026-06-10.
- [x] Initial commit of `docs/` + `PLAN.md` — 2026-06-10.
- [x] Phase 0: Cargo workspace skeleton (`axeyum-ir`, `axeyum-solver`),
      licenses, CI — 2026-06-10.
- [x] Push `main` to GitHub and confirm CI is green there — 2026-06-10.
- [x] Scaffolding complete — 2026-06-10. All pre-code work is done:
      infrastructure, metadata, documentation, ADRs,
      north-star, LLM integration points), Cargo workspace, CI green,
      CLAUDE.md, corpus skeleton, 20 reference clones. **Everything below
      this line is implementation, not scaffolding** — deliberately deferred
      to the next working session.
- [x] **Milestone M0 (vertical slice) — 2026-06-10.** The ADR-0001 doctest
      passes: `x + 1 == 5` over `BV(8)` solves via `Z3Backend` and the
      ground evaluator confirms the lifted model. `axeyum-ir` has the M0
      operator subset, hash-consed arena, sort-checked builders, and the
      evaluator with exhaustive small-width tests; `axeyum-solver` has the
      trait, symbol-keyed models, and the feature-gated Z3 backend
      (`z3` = system libz3 via pkg-config, `z3-static` = hermetic prebuilt).
      Representation decisions in ADR-0003. All sat results in the test
      harness replay through the evaluator.
- [x] **Phase 1 (typed term core broadened) — 2026-06-10.** Full scalar
      QF_BV operator set (40 operators: arithmetic incl. sdiv/srem/smod,
      shifts, all 8 comparisons, nand/nor/xnor/comp, extensions, rotates,
      implies) with SMT-LIB edge-case semantics; SMT-LIB-style pretty
      printer (`render`); exhaustive small-width evaluator tests (22 IR
      tests); and a differential suite where Z3 confirms the evaluator on
      *every* input at width 3 for every operator — three independent
      implementations (evaluator, i64 test reference, Z3) agree.
- [x] **Observability & resource governance — 2026-06-11.** Per the
      query-cost-control and observability notes: `TermStats` sharing
      metrics in `axeyum-ir` (DAG vs saturating tree size — the 2^k blowup
      detector — depth, support, ite/mul-div counts); structured
      `Unknown(UnknownReason{kind, detail})` so budget exhaustion can never
      read as unsat; `SolverConfig` budgets (timeout, deterministic
      `resource_limit`→Z3 rlimit, `memory_limit_mb`, `node_budget`
      admission control); `SolveStats` layer-attributed telemetry via
      `last_stats()` incl. Z3 statistics. Tested: 2^200 chain saturates,
      node budget refuses with diagnosis, rlimit yields classified Unknown.
- [x] **Phase 2, SMT-LIB leg — 2026-06-11.** New `axeyum-smtlib` crate:
      iterative QF_BV-slice parser (declare/define-fun, let scoping, n-ary
      and indexed operators, hex/bin/indexed literals, `:status` ground
      truth, clear Unsupported errors for arrays/UF/incremental) and
      sharing-preserving writer (shared nodes as 0-ary define-funs; the
      2^100 bomb exports linearly — tested). Parse→Z3→evaluator-replay and
      export round-trip conformance tests; corpus smoke test ingests real
      local SMT-LIB files (runtime-skipped on CI).
- [x] **Phase 2 benchmark harness and hardening pass — 2026-06-11.**
      `axeyum-bench` runs `.smt2` corpora through `Z3Backend`, replays every
      `sat` model through the evaluator, checks `:status` agreement, reports
      PAR-2, emits versioned JSON artifacts with config/corpus hashes,
      backend version, hardware note, seed, shape metrics, and layer timings.
      Committed `corpus/micro/*.smt2` fixtures now run in CI. Review fixes
      also made SMT-LIB parsing stricter, escaped writer identifiers, avoided
      generated-name collisions, made extension-width arithmetic overflow-safe,
      scoped Z3 memory limits, and added model-lift telemetry.
- [x] **Planning refinement: foundational DAG — 2026-06-11.** Added the
      logic/math dependency DAG, support matrix, phase gates, web/reference
      refresh gates, and Z3-demotion criteria to make future work proceed from
      semantics and evidence obligations rather than broad milestones alone.
- [x] **Phase 2 public baseline — 2026-06-11.** Recorded
      `bench-results/baselines/qf-bv-20221214-p4dfa-z3-1s.json` for the
      SMT-LIB 2024 non-incremental QF_BV `20221214-p4dfa-XiaoqiChen` family:
      113 parsed/solved-through-trait files, 0 unsupported, 0 errors,
      0 status disagreements, 0 model replay failures. Timeouts are classified
      as structured `unknown`, not failures. State-retention conformance stays
      deferred until the incremental/query lifecycle API exists.
- [x] **Phase 3 entry contracts — 2026-06-11.** Added `axeyum-query` for
      assertions, assumptions, and scopes; added `axeyum-rewrite` for the
      stable manifest contract; added `SolverBackend::check_query`; accepted
      ADR-0005 for the layered evidence envelope and the rule that
      equisatisfiability-only rewrites remain disabled until model projection is
      implemented and replay-tested.
- [x] **Phase 3 first canonicalizer — 2026-06-11:** implemented the first
      denotation-preserving rewrite rules in `axeyum-rewrite` (start with
      simple Boolean/BV identities and constant folds), registered them in the
      manifest, proved evaluator equivalence with focused tests, and added a
      Z3 oracle differential check for rewritten queries.
- [x] **Phase 3 rewrite measurement and corpus gate — 2026-06-11:** run the default
      canonicalizer through benchmark/corpus plumbing, record nodes-in/out and
      rule-application counts in artifacts, compare Z3 answers and model replay
      against original assertions on the public QF_BV baseline slice, and
      record measured rewrite effect before assuming a win.
- [x] **Phase 3 query planning — 2026-06-11:** add structural cache keys and
      constraint slicing against `axeyum-query`, with projection/replay tests
      proving planned models satisfy the original query contract.
- [x] **Phase 3 exit hardening — 2026-06-11:** added deterministic generated
      rewriter equivalence coverage, exercised query-planner cache/slice
      metrics on micro and public corpus artifacts, and recorded the Phase 3
      exit audit before starting Phase 4 bit-order/circuit work.
- [x] **Phase 4 entry contract — 2026-06-11:** recorded the bit-order convention,
      shared value-to-wires conversion plan, circuit/AIG entry shape, and
      CNF/lift-map evidence obligations before implementing public
      bit-lowering APIs in
      [ADR-0006](docs/research/09-decisions/adr-0006-phase4-bit-order-and-lowering-entry-contract.md).
- [x] **Phase 4 first implementation slice — 2026-06-11:** added shared LSB-first
      value-to-bits/bits-to-value helpers, an AIG graph skeleton with
      deterministic structural hashing, and evaluator tests before adding
      public bit-lowering APIs.
- [x] **Phase 4 initial bit lowering — 2026-06-11:** added the first term-to-AIG
      lowering module for Bool/BV constants, symbols, and cheap bitwise
      operators, with evaluator-vs-AIG tests and explicit term-bit lift-map
      data.
- [x] **Phase 4 structural bit lowering — 2026-06-11:** added `eq`, `ite`,
      concat/extract, zero/sign extension, and `bvcomp` lowering with
      evaluator-vs-AIG tests and lift-map replay.
- [x] **Phase 4 arithmetic/comparison bit lowering — 2026-06-11:** added `bvneg`,
      `bvadd`, `bvsub`, and the unsigned/signed comparison operators with
      evaluator-vs-AIG tests and lift-map replay.
- [x] **Phase 4 shift/rotate bit lowering — 2026-06-11:** added `bvshl`, `bvlshr`,
      `bvashr`, `rotate_left`, and `rotate_right` lowering with
      evaluator-vs-AIG tests and lift-map replay; keep multiplication,
      division, and remainder deferred until their encoding gate is explicit.
- [x] **Phase 4 CNF layer — 2026-06-11:** added `axeyum-cnf` with simple Tseitin
      encoding from AIG, DIMACS I/O, CNF evaluation, and lift maps from CNF
      variables back through AIG literals to original term bits.
- [x] **Phase 4 SAT adapter path — 2026-06-11:** refreshed/evaluated RustSAT,
      `rustsat-batsat`, direct BatSat, splr, and varisat; accepted ADR-0007 for
      `rustsat-batsat` through RustSAT as the first pure-Rust adapter; added a
      CNF SAT trait/result/assignment surface; solved raw DIMACS/CNF through the
      adapter; and replayed satisfying assignments through CNF variables, AIG
      node values, reconstructed symbol models, and original terms.
- [x] **Phase 4 exit hardening and audit — 2026-06-11:** added deterministic
      ASCII AIGER debug export and smoke tests, added a committed DIMACS micro
      corpus solved through the SAT trait, recorded default dependency evidence
      for the pure-Rust SAT path, explicitly deferred benchmark artifact layer
      telemetry to Phase 5 where real pure-Rust backend timings exist, and wrote
      the Phase 4 exit audit.
- [x] **Phase 5 first SAT-backed BV backend slice — 2026-06-11:** added
      `SatBvBackend` in `axeyum-solver`, composing supported term-to-AIG
      lowering, Tseitin CNF, the BatSat adapter, model reconstruction,
      deterministic model completion, evaluator replay, structured unsupported
      errors for unsupported lowering operators, Z3 differential tests for
      supported decisions, and `axeyum-bench --backend sat-bv|z3` artifact
      version 4 backend layer telemetry, later extended by artifact version 5
      oracle-comparison and node-budget provenance.
- [x] **Phase 5 public supported-slice differential baseline — 2026-06-12:**
      ran the pure Rust backend against the public
      `QF_BV/20221214-p4dfa-XiaoqiChen` slice with Z3 comparison, recorded
      unsupported/error triage separately from soundness failures, and wrote
      artifact version 5 evidence with 1 compared-and-agreeing public `sat`
      instance, 112 node-budget `unknown`s, 0 unsupported/errors, 0 oracle
      disagreements, and 0 model replay failures.
- [x] **Phase 5 guarded admission and CNF-budget diagnostics — 2026-06-12:**
      added explicit CNF variable/clause budgets, cooperative BatSat timeout
      classification, artifact version 7 query-plan/replay-policy provenance,
      and regenerated the public `sat-bv` vs Z3 guarded run at node budget 5000
      with CNF caps. The run still decides one public `sat`; it classifies the
      next admitted candidate as `EncodingBudget` before SAT solve and keeps
      unsupported, unknown, and soundness triage distinct.
- [x] **Phase 5 replay-refinement diagnostic — 2026-06-12:** added
      `axeyum-bench --query-plan replay-refine`, which iteratively solves a
      sliced support plan, replays each `sat` model against the full original
      query, adds the failed assertion support, and accepts `sat` only after
      full replay. The public diagnostic artifact still decides one public
      `sat`, but it proves replayable slicing alone is not enough to expand the
      supported public slice under current CNF caps and BatSat timeout.
- [x] **Phase 5 legacy-guided sparse-CNF pass — 2026-06-12:** reviewed cvc5
      ITE simplification/removal and Bitwuzla AIG-to-CNF ITE recognition,
      implemented directional signed comparisons plus sparse CNF for private
      XOR/mux AIG helper nodes, added a replay-refine profiling example, and
      regenerated guarded/replay-refine public artifacts. The pass materially
      reduces CNF size and lets the immediate MobileDevice target refine one
      support round further, but it still does not expand public decisions under
      the committed 7000-variable/20000-clause caps.
- [x] **Phase 5 reachable/sparse-CNF follow-up — 2026-06-12:** added private
      AND-tree flattening, direct OR-of-private-AND encoding, deterministic
      clause normalization/deduplication, root-reachable CNF encoding with
      full-AIG replay for dead nodes, root-only polarity clause trimming, and
      constant-sign signed-comparison simplification. The immediate
      MobileDevice replay-refine target now reaches the fifth support set and
      stays below the variable cap at 5,727 variables, but still stops at
      21,637 clauses against the committed 20,000-clause cap; this is progress
      on encoding growth, not a public support expansion yet.
- [x] **Phase 5 positive-root equality CNF pass — 2026-06-12:** added bounded
      direct parity/equality clauses for positive root-only AND-tree leaves
      backed by private XOR helpers, with skipped XOR AIG nodes reconstructed
      by replay. The immediate MobileDevice replay-refine target now passes the
      fifth and sixth support sets under the committed caps, then stops at the
      seventh support set with 5,353 variables and 20,784 clauses. The full
      public replay-refine run remains soundness-clean but still decides one
      public instance, so this is not a support expansion yet.
- [x] **Phase 5 relaxed-cap diagnostic — 2026-06-12:** verified that simply
      raising the committed clause cap is technically sound on the immediate
      MobileDevice target when paired with replay/model checking: 30,000
      clauses and a 10s timeout reaches `sat` with Z3 agreement. Keep the
      default public caps unchanged until a full public-slice run justifies the
      admission change.
- [x] **Phase 5 relaxed public support-expansion diagnostic — 2026-06-12:**
      added deterministic corpus-level `--jobs` support to `axeyum-bench` and
      recorded the full public replay-refine run at 10s / 5000 nodes /
      7000 CNF variables / 30000 CNF clauses / 8 jobs. The run expands the
      public pure-Rust supported slice to 2 `sat` decisions with Z3 agreement
      and no soundness alarms, while leaving 94 `EncodingBudget` and
      17 `NodeBudget` unknowns.
- [x] **Phase 5 exact-target relaxed replay-refinement diagnostic —
      2026-06-12:** added exact-target replay-refinement planning and
      `--refine-batch`, recorded artifact version 9 at 10s / 5000 nodes /
      8000 CNF variables / 30000 CNF clauses / 64 rounds / batch 64 / 8 jobs,
      and regenerated the public artifact with the current harness. The run
      keeps the supported public slice at 2 `sat` decisions with Z3 agreement
      and no soundness alarms, removes `NodeBudget` unknowns from this
      diagnostic profile, and leaves all 111 remaining unknowns as
      `EncodingBudget`.
- [x] **Phase 5 adaptive exact-target replay-refinement diagnostic —
      2026-06-12:** added explicit `--refine-adaptive-batch`, artifact version
      10 adaptive-policy/backoff telemetry, matching developer profile support,
      and reproducible public just targets. The same-cap public run keeps the
      supported slice at 2 `sat` decisions but converts the remaining
      `EncodingBudget` failures from coarse batch cliffs into near-cap final
      encodings; an 8,500-variable sweep still leaves 111 `EncodingBudget`
      unknowns, so this is diagnostic precision, not support expansion.
- [x] **Phase 5 smallest-DAG refinement-selection diagnostic — 2026-06-12:**
      added explicit `--refine-select first|smallest-dag`, artifact version 11
      selector telemetry, matching developer profile support, and reproducible
      public just targets. The selector reduces several source-order
      `EncodingBudget` frontiers but the same-cap and 8,500-variable public
      runs remain at 2 `sat` decisions and 111 `EncodingBudget` unknowns, so
      this is useful pressure reduction, not support expansion.
- [x] **Phase 5 root-direct assertion CNF and plan-aware selector diagnostic —
      2026-06-12:** removed dedicated CNF variables for assertion-only AIG
      roots while preserving full AIG/original-term replay, added
      `--refine-select smallest-plan-dag` as a bounded 64-candidate
      plan-aware diagnostic, bumped artifacts to version 12, and regenerated
      the public smallest-DAG 8,000- and 8,500-variable sweeps. Both remain
      soundness-clean at 2 `sat` decisions and 111 `EncodingBudget` unknowns,
      so this is not a support expansion.
- [x] **Phase 5 replay-refinement cleanup and rewrite-safe targeting —
      2026-06-12:** rejected the singleton budget-skip experiment after
      focused 8,000- and 12,000-variable diagnostics showed it chases the
      frontier rather than completing replay; kept artifact schema at version
      12; added rewrite-safe replay-refinement target mapping so original
      replay failures refine the corresponding rewritten assertion; and added
      a regression test for that mapping. The close rewritten `StringMatching`
      diagnostic is now soundness-clean but still stops at the same
      `EncodingBudget` frontier, so this is correctness/diagnostic hardening,
      not support expansion.
- [x] **Phase 5 AIG simplification diagnostic — 2026-06-12:** added
      condition-aware mux cleanup plus OR-consensus/absorption simplifications
      in `axeyum-aig`, measured the closest StringMatching frontiers, rejected
      a bounded CNF subsumption experiment that only slowed CNF encoding, and
      reran the full public smallest-DAG adaptive exact-target profile. The
      pass reduces selected AIG/CNF pressure but leaves the public slice at
      2 `sat` decisions and 111 `EncodingBudget` unknowns, so it is not a
      support expansion.
- [x] **Phase 5 greedy selector diagnostic — 2026-06-12:** added
      `--refine-select smallest-plan-greedy` and matching profile support,
      fast-pathed exact-target plan scoring, bumped artifacts to version 13,
      and measured a modest focused `StringMatching/string1x16.3` frontier
      reduction. The user requested commit/push before a full public v13 run,
      so this is focused selector evidence, not a support expansion.
- [x] **Consumer-models iteration 1 — 2026-06-13:** added the
      `axeyum-scenarios` crate (self-checking, oracle-free SAT/UNSAT consumer
      workloads grounded in concrete execution and bounded-verified identities),
      a deterministic `catalog()`, crate self-check tests, and an
      `axeyum-solver` differential test that decides the whole catalog through
      `SatBvBackend` with zero unknowns and zero soundness alarms. Recorded in
      ADR-0008 and the consumer-scenario-models verification note. Establishes
      a realistic, scalable, oracle-free corpus for the interface and
      optimization-architecture iterations.
- [x] **Consumer-models iteration 2 (interfaces) — 2026-06-13:** added the
      high-level incremental `Solver` façade in `axeyum-solver` (assert /
      assert_all / push / pop / check / check_assuming, with `last_stats` and
      capability passthrough) and ergonomic `SolverConfig` builder methods
      (`with_timeout`, `with_node_budget`, CNF budgets, etc.). The façade is
      incremental at the interface level (SMT-LIB push/pop scopes and one-shot
      `check_assuming` assumptions) over the still-one-shot backend, so a future
      incremental backend drops in without changing consumer code. Tests cover
      push/pop scope restoration, assumption non-persistence, and driving the
      whole `axeyum-scenarios` catalog through the façade. A true incremental
      SAT backend (native assumption literals, clause reuse) remains a separate
      ADR-gated step.
- [x] **Consumer-models iteration 3 (abstraction/optimization architecture) —
      2026-06-13:** added the typed `BvLayerStats` view in `axeyum-solver`,
      lifting the previously stringly-typed per-stage counters (bit-blast,
      cnf-encode, solve, model-lift; AIG inputs/nodes, CNF variables/clauses,
      clause density) into a first-class, regression-tested abstraction. Added
      the `scenario_pipeline_report` bench example: a deterministic per-stage,
      per-family report over the `axeyum-scenarios` corpus, so optimization can
      be measured on realistic oracle-free workloads. The report already
      surfaces structure (de-Morgan and two's-complement identities collapse to
      0 CNF variables; mixing scales cleanly with rounds).
- [x] **Consumer-models iteration 4 (integrate + measure) — 2026-06-13:** added
      the `scenario_scaling` bench example, sweeping the `mixing` family's round
      count at widths 16/32/64. It self-checks each workload, then records the
      pipeline scaling profile: AIG/CNF size grows linearly in rounds, clause
      density converges to ~3.5 clauses/variable (plain Tseitin's ~3/AND-node),
      and `sat-bv` solve time scales near-linearly with size on these
      satisfiable instances (e.g. width 64 / 64 rounds: 16,040 AIG nodes, 7,942
      CNF variables, 27,676 clauses, ~29 ms). This gives an oracle-free,
      frontier-scalable empirical baseline for choosing the next deep encoding
      or SAT-cost optimization, instead of tuning the single `p4dfa` slice
      against Z3.
- [x] **Follow-on: `bvmul` lowering — 2026-06-13:** added a truncated
      shift-and-add multiplier in `axeyum-bv` (`Op::BvMul`), verified
      exhaustively against the ground evaluator for widths 1/2/4/5 over all
      input pairs (symbol×symbol, squaring, symbol×constant). Added an
      `Arithmetic` scenario family (`factor_target` satisfiable factoring,
      `distributivity_identity` unsatisfiable), which the pure-Rust backend now
      decides; the pipeline report shows multiplication is the dominant SAT cost
      (~15 ms mean vs <0.5 ms for other families), confirming the measurement
      substrate guides optimization.
- [x] **Follow-on: unsigned division/remainder lowering — 2026-06-13:** added a
      combinational restoring divider in `axeyum-bv` (`Op::BvUdiv`/`Op::BvUrem`)
      that computes quotient and remainder together (the AIG dedups the shared
      circuit) with SMT-LIB divide-by-zero totality (`x udiv 0 = ~0`,
      `x urem 0 = x`), verified exhaustively against the evaluator for widths
      1/2/3/4/5 over all input pairs including the zero-divisor path. Added
      `division_target` (satisfiable, pins `x` by quotient+remainder) and
      `division_roundtrip_identity` (unsatisfiable Euclidean identity) scenarios,
      both decided by the pure-Rust backend. Only signed division/remainder
      (`bvsdiv`/`bvsrem`/`bvsmod`) remain unsupported.
- [x] **Follow-on: incremental SAT (ADR-0009, stage 1) — 2026-06-13:** added
      `IncrementalSat` in `axeyum-cnf`, a warm `rustsat-batsat` wrapper with
      monotone `add_clause`, native one-shot assumptions (`solve_assuming`), a
      stable growing variable namespace, and the same `sat` model self-check as
      the one-shot adapter. Tests cover cross-solve accumulation, one-shot
      assumption non-persistence, selector-literal push/pop emulation, and a
      permanent contradiction. ADR-0009 records the design and the staged plan;
      stage 2 (incremental bit-blasting wiring so the `Solver` façade is
      end-to-end incremental) is the next step.
- [x] **Follow-on: signed division/remainder lowering — 2026-06-13:** added
      `bvsdiv`/`bvsrem`/`bvsmod` in `axeyum-bv` as sign-handling wrappers over
      the unsigned restoring divider (compute on absolute values via shared
      `signed_divrem_abs`, fix signs per the SMT-LIB expansions; the AIG dedups
      the shared divider), verified exhaustively against the evaluator for
      widths 1–5 over all input pairs incl. negatives, the most-negative value,
      and divide-by-zero. This **completes the full scalar QF_BV operator set**;
      the backend's unsupported path now only guards future non-scalar
      constructs. The real-corpus mul/div spot-check is now 0 unsupported.
- [x] **Incremental bit-blasting (ADR-0009 stage 2) — 2026-06-13:** end-to-end
      incremental solving now exists, built as three green sub-increments:
      (2a) `IncrementalLowering` in `axeyum-bv` — a persistent AIG + symbol/term
      memo so a symbol always maps to the same inputs and shared subterms lower
      once (proven structurally identical to batch lowering); (2b)
      `IncrementalCnf` in `axeyum-cnf` — simple per-node Tseitin over the warm
      `IncrementalSat`, with selector-guarded roots and direct AIG-node-value
      lifting; (2c) `IncrementalBvSolver` in `axeyum-solver` — `assert`/`push`/
      `pop`/`check`/`check_assuming` composing 2a+2b, with push/pop compiled to
      selector literals, `check_assuming` to ephemeral selectors, and every
      `sat` model lifted through the shared reconstruction and **replayed against
      the original terms** by the evaluator. It decides the whole oracle-free
      scenario catalog with zero soundness alarms and runs a symbolic-execution-
      style push/pop path-exploration test. Known follow-ups: the incremental
      encoder uses simple per-node Tseitin (not the one-shot path's sparse-CNF
      optimizations), and ephemeral assumption selectors leak clauses
      (ADR-0009-acknowledged).
- [x] **First downstream consumer (symbolic execution) — 2026-06-13:** built a
      register-VM symbolic executor over `IncrementalBvSolver` with branch
      forking (push/pop), feasibility pruning, model extraction, and
      concrete-re-execution cross-check of every found input. CI-covered as
      `axeyum-solver/tests/symbolic_execution.rs`. The first Phase 7
      infosec-workflow client example; validates the incremental stack against
      the real use case.
- [x] **Arrays sub-increment 1 — IR (done, 2026-06-13)**
      ([ADR-0010](docs/research/09-decisions/adr-0010-arrays-via-eager-elimination.md),
      accepted). Added the `Array` sort, `select`/`store` builders (sort/width
      checked), a non-`Copy` `ArrayValue`, and the read-over-write evaluator
      (the semantic reference); moved `axeyum_ir::Value` from `Copy` to `Clone`
      and rippled it across all crates. Exhaustive IR tests cover
      read-over-write, last-write-wins extensional equality, and builder sort
      checks. Arrays are rejected by the bit-blasting and z3 backends (via the
      `first_unsupported_op` preflight) pending elimination.
- [x] **Arrays sub-increment 2 — eager elimination (done, 2026-06-13):** added
      `eliminate_arrays` in `axeyum-rewrite` (read-over-write + Ackermann →
      pure QF_BV) with `ArrayElimination::project_model` for array-model
      reconstruction, reusing `build_app` and the whole BV pipeline. Array
      equality and selects over non-variable/store/ite bases return structured
      `Unsupported`. Oracle-free tests prove the elimination is
      denotation-preserving under consistent models and that Ackermann
      constraints hold (read-over-write and two-select cases).
- [x] **Arrays sub-increment 3 (core) — QF_ABV end to end (done, 2026-06-13):**
      `axeyum-solver/tests/arrays.rs` composes elimination → `SatBvBackend` →
      `project_model` → original-query evaluator replay. Decides distinct-address
      loads (Ackermann aliasing), read-after-write (UNSAT), and aliasing
      load (SAT), each soundness-checked oracle-free. **QF_ABV now solves.**
- [x] **Arrays sub-increment 3 — first-class API + memory consumer (done,
      2026-06-13):** promoted elimination to a first-class entry point
      `axeyum_solver::check_with_array_elimination` (eliminate → backend → project
      → replay; `axeyum-rewrite` is now a normal dep of `axeyum-solver`).
      `axeyum-solver/tests/arrays.rs` uses it, and
      `tests/symbolic_execution_memory.rs` is the memory-using consumer: it
      solves a write-then-probe-load QF_ABV query, extracts the inputs and the
      reconstructed memory array, and **concretely re-executes** the program to
      confirm the target is reached (oracle-free).
- [x] **Arrays — QF_ABV memory scenarios (done, 2026-06-13):** added a `Memory`
      family and `memory_catalog()` in `axeyum-scenarios` (self-checking
      store/load traces, satisfiable by construction), kept separate from the
      scalar `catalog()`. A new `axeyum-solver` differential test runs the whole
      memory catalog through `check_with_array_elimination` (all decided, zero
      soundness alarms), exercising eager elimination + projection + replay on a
      consumer-representative corpus.
- [x] **Arrays — SMT-LIB parsing + corpus blow-up measurement (done,
      2026-06-13):** the SMT-LIB reader now accepts `(Array (_ BitVec n)
      (_ BitVec m))` sorts and `select`/`store` (round-trip tested via the
      writer). A new `axeyum-bench` example `qf_abv_probe` parses real QF_ABV
      files, eagerly eliminates arrays, and reports DAG blow-up. Measured on 20
      small `QF_ABV` corpus files: 19/20 parse (1 needs BV width 1024 >
      `MAX_BV_WIDTH` 128); 14/19 eliminate with blow-up 1.2–4.5× DAG nodes
      (store chains like `memcpy` grow most); the other 5 use **array equality**
      (the deferred extensionality construct, flagged `Unsupported` as designed).
      Eager elimination is not catastrophic on this sample, so a lazy array
      procedure is not yet justified.
- [x] **UNSAT proof checking — DRAT checker (done, 2026-06-13, ADR-0011):**
      added an independent in-tree DRAT checker in `axeyum-cnf`
      (`check_drat`/`parse_drat`, RUP + RAT) — the trusted UNSAT-discharge
      kernel, dependent only on the formula and proof. Tested on RUP chains, a
      blocked (RAT-not-RUP) clause, unjustified-step rejection, no-empty-clause
      (not-unsat), and parse round-trips. This closes the "which proof checker
      discharges UNSAT" question; a DRAT *producer* is the remaining piece.
- [x] **UNSAT proof producer — proof-producing SAT core (done, 2026-06-13,
      ADR-0012):** added `solve_with_drat_proof` in `axeyum-cnf` — DPLL with
      conflict-cube learning that emits DRAT, verified end to end by
      `check_drat`. Tests show unit-contradiction, full-2×2, pigeonhole-like,
      and empty-clause `unsat` all produce checker-accepted DRAT proofs, and SAT
      models satisfy. This realizes "untrusted search, trusted checking" for
      `unsat` in pure Rust (the core is untrusted; the checker is the trust
      anchor). It is a proof/correctness reference, not the perf default
      (`rustsat-batsat` stays the fast path).
- [x] **Proof-checked `unsat` in the BV backend (done, 2026-06-13):** added
      `SolverConfig::prove_unsat`; when set, `SatBvBackend` independently
      re-derives an `unsat` with `solve_with_drat_proof` and verifies its DRAT
      proof via `check_drat` before returning, recording an `unsat_proof_checked`
      stat (a disagreement or failed proof is a `SolverError::Backend` soundness
      alarm). QF_BV `unsat` is now high-assurance end to end through the normal
      solve path (term → AIG → CNF → proof core → DRAT → trusted checker). The
      proof core is a reference, so this is for small/high-assurance instances.
- [x] **Custom CDCL core — 1-UIP + watched literals (done, 2026-06-13):** the
      proof-producing core uses MiniSat-style 1-UIP learning plus
      two-watched-literal propagation, validated by a 400-CNF randomized
      differential test against the BatSat adapter (agree on sat/unsat; `sat`
      models satisfy; `unsat` proofs pass `check_drat`). Solves e.g.
      pigeonhole 3→2 with a DRAT-checked proof; conflict-budget safety valve.
- [x] **Uninterpreted functions sub-increment 1 — IR (done, 2026-06-13,
      ADR-0013):** first-class `declare_fun`/`Op::Apply` with a scalar signature,
      a `FuncValue` model interpretation honored by the evaluator (congruence
      verified exhaustively at width 3), Z3 rejection of `Op::Apply`, and an
      SMT-LIB writer that emits `declare-fun` + `QF_UFBV`/`QF_AUFBV`.
- [x] **Uninterpreted functions sub-increment 2 — elimination + solving (done,
      2026-06-13, ADR-0013):** `eliminate_functions` (Ackermann congruence
      reduction, `QF_UFBV` → `QF_BV`, `FuncValue` model projection) and
      `check_with_function_elimination` (first-class entry point with
      original-query evaluator replay); `Model` carries function interpretations;
      oracle-free end-to-end `QF_UFBV` tests (congruence `unsat`, replayed `sat`,
      binary functions).
- [x] **Uninterpreted functions — SMT-LIB I/O (done, 2026-06-13, ADR-0013):**
      parser accepts n-ary `declare-fun` (scalar signatures) and function
      applications (builtin-priority); parse → write → parse round-trip for
      `QF_UFBV`; obsolete "functions-with-args unsupported" test replaced.
- [x] **`QF_AUFBV` theory composition (done, 2026-06-13, ADR-0010+0013):**
      `check_with_arrays_and_functions` composes array then function elimination
      with combined model projection (functions first) and original-query
      replay; oracle-free end-to-end tests (cross-theory congruence `unsat`,
      store-then-apply `sat`, distinct outputs). First two-theory composition.
- [x] **`QF_UFBV` scenarios (done, 2026-06-13, ADR-0013):** `Family::Function`
      with `function_chain`/`function_lookup`/`function_binary_merge` +
      `function_catalog`; solver-crate differential test decides all through
      `check_with_function_elimination`, oracle-free. EUF rollout complete.
- [x] **Arithmetic fragment chosen + IR sub-increment 1 (done, 2026-06-13,
      ADR-0014):** `QF_LIA` first via bounded bit-blasting; the `Int` sort,
      linear operators, `Value::Int`, and the ground evaluator are in, verified
      exhaustively over a small range; backends reject `Int` cleanly via
      `first_unsupported_sort`.
- [x] **`QF_LIA` bounded bit-blasting decision procedure (done, 2026-06-13,
      ADR-0014):** `blast_integers` + `check_with_int_blasting` with exact-integer
      model read-back and replay; BV `unsat`/overflow/out-of-range → `unknown`,
      never wrong; oracle-free end-to-end tests.
- [x] **`QF_LIA` scenarios + SMT-LIB I/O (done, 2026-06-13, ADR-0014):**
      `Family::Integer` (`integer_system`/`integer_equation` + `integer_catalog`)
      decided through `check_with_int_blasting`; parser/writer for `Int`,
      literals, `+`/`-`/`*`, chainable comparisons, `QF_LIA` round-trip.
- [x] **`QF_AUFLIA` full composition (done, 2026-06-13, ADR-0010+0013+0014):**
      `check_with_all_theories` composes array → function → integer reductions
      with reverse model projection, replay, and a branch-correct `unsat`/
      `unknown` contract; subsumes the single-theory entry points; oracle-free
      end-to-end tests.
- [x] **`QF_LRA` ADR + IR sub-increment 1 (done, 2026-06-13, ADR-0015):**
      exact-rational simplex chosen as the first non-`QF_BV` procedure; the
      `Real` sort, pure-Rust `Rational`, linear operators, `Value::Real`, and
      exact-rational evaluator are in, verified against an exact reference;
      backends reject `Real` cleanly.
- [x] **`QF_LRA` exact-rational decision procedure (done, 2026-06-13, ADR-0015):**
      `check_with_lra` decides conjunctive `QF_LRA` by exact-rational
      Fourier–Motzkin with rational-model replay; `or`/disequality → `Unsupported`;
      oracle-free end-to-end tests (fractional witnesses, unsat cycles).
- [x] **`QF_LRA` scenarios + SMT-LIB I/O (done, 2026-06-13, ADR-0015):**
      `Family::Real` + `real_catalog` decided through `check_with_lra`;
      parser/writer for `Real`, decimal/`(/ ..)` literals, numeral coercion,
      sort-directed operators, `QF_LRA` round-trip.
- [x] **Lazy SMT / DPLL(T) over `QF_LRA` (done, 2026-06-13, ADR-0015 follow-on):**
      `check_with_lra_dpll` — Boolean abstraction → SAT skeleton → theory check →
      blocking-clause refinement, with `sat` replay; lifts the conjunction-only
      limit (disjunctions now decide). The lazy theory-combination architecture.
- [x] **Unified quantifier-free dispatcher (done, 2026-06-13):** `check_auto`
      routes any supported QF query to the bit-blasting composition or the
      lazy-SMT real engine by theory features; mixed real+bit-blast → `Unsupported`.
      One front door for the downstream consumer.
- [x] **Quantifiers — binder ADR + IR sub-increment 1 (done, 2026-06-13,
      ADR-0016):** named binders (`Op::Forall`/`Op::Exists`), `forall`/`exists`
      builders, finite-domain enumerating evaluator; backends reject non-QF
      formulas; writer renders binder form.
- [x] **Quantifier solving by finite-domain expansion (done, 2026-06-13,
      ADR-0016):** `expand_quantifiers` + `check_with_quantifiers` decide
      finite-domain quantified formulas with original-formula replay.
- [x] **WebAssembly target support (done, 2026-06-13, ADR-0017):** default
      library stack builds/runs on wasm (browser + WASI) via a wasm-only
      `web-time` clock shim; native builds untouched; verified both targets.
- [x] **SMT-LIB quantifier parsing (done, 2026-06-13, ADR-0016):**
      `(forall/exists ((x T)..) body)` parses with capture-free fresh-symbol
      scoping; quantifier round-trip; nested-binding non-capture test.
- [x] **Exportable clausal `unsat` proof artifacts (done, 2026-06-13):**
      `write_drat` + `export_qf_bv_unsat_proof` emit a self-verified, externally
      re-checkable DIMACS+DRAT certificate for `QF_BV` `unsat`.
- [x] **Self-checking `Evidence` envelope (done, 2026-06-13, ADR-0005):**
      `Evidence` + `produce_qf_bv_evidence` + `Evidence::check` — a result with
      its justification that independently re-validates (model replay / DRAT
      re-check); tampered models fail their own check.
- [x] **`QF_LRA` Farkas `unsat` certificates (done, 2026-06-13, ADR-0015
      follow-through):** `check_with_lra` threads nonnegative Farkas multipliers
      through Fourier–Motzkin and returns a self-checked `FarkasCertificate` for
      every `unsat` (`FarkasCertificate::verify` rebuilds the refutation
      independently; a failed check is a `SolverError::Backend` soundness
      alarm). `lra_farkas_certificate` exposes it for auditing. Closes the last
      lower-assurance result type; oracle-free tests cover verifying
      certificates, no-certificate `sat`, and tamper rejection. Also wired into
      the `Evidence` envelope (`Evidence::UnsatFarkas` + `produce_lra_evidence`,
      with tamper-rejection tests), used for DPLL(T) theory-conflict
      minimization, and surfaced as `lra_unsat_core` (Farkas-support-seeded,
      deletion-minimized minimal unsat core — the SMT `get-unsat-core`
      capability, re-verified before return). Follow-up: a δ-rational simplex
      for scale.
- [x] **DPLL(T) `unsat` refutation certificates — pure-real (done, 2026-06-13,
      ADR-0015):** `certify_lra_dpll_unsat` decides a **pure-real**
      Boolean-structured `QF_LRA` query and, on `unsat`, returns a self-checked
      `LraDpllRefutation` — the Boolean skeleton plus the lazy-SMT loop's learned
      theory lemmas (each an infeasible real-atom core). `LraDpllRefutation::verify`
      re-checks it independently of the search: (1) every lemma's core is
      re-decided `unsat` by `check_with_lra` (itself Farkas-self-checked), so each
      lemma clause holds in every real model; (2) the skeleton with all lemma
      clauses is propositionally unsatisfiable, confirmed by enumerating every
      truth assignment to the Boolean symbols (capped at 22; above that the
      certificate is a classified `unknown`, never produced unverified). Soundness:
      a real model would induce a truth assignment satisfying the skeleton and
      every lemma clause, which (2) forbids — the abstraction is the trusted
      reduction, exactly as bit-blasting is on the DRAT route. The refutation is
      self-verified before return (failure → `SolverError::Backend` alarm). Tests:
      a case-split conflict certifies and verifies, a `sat` query returns a
      replaying model, bit-vector content is rejected `Unsupported`, and a
      lemma-stripped refutation fails verification. This generalizes the
      conjunctive-LRA Farkas certificate to arbitrary Boolean structure over reals.
      Also wired into the `Evidence` envelope (`Evidence::UnsatLraDpll` +
      `produce_lra_dpll_evidence`) and hardened by a 1500-case deterministic fuzz
      test (intrinsic soundness). Remaining: certify the lazy-SMT `unsat` when the
      skeleton also carries bit-blasted theories (the propositional half then
      needs a DRAT proof, not enumeration).
- **R&D tracks status (all bounded work done; one open research remainder).** The
      supported theories (`QF_BV`, arrays, EUF, `QF_LIA`, `QF_LRA`, their
      composition, finite-domain + instantiation/E-matching quantifiers) are
      complete end to end with checkable evidence and wasm support, behind the
      `solve` / `produce_evidence` / `prove` / `unsat_core` consumer front doors.
      The named tracks:
  - [x] **(b) trigger-based E-matching — done.** Single- and multi-variable
        `apply`/`select` matching binding variables to compound ground terms,
        nested universal-chain instantiation, a head-symbol match index, and
        congruence-closure matching modulo the asserted ground equalities. The
        only remaining refinement is a *persistent incremental* E-graph for scale
        (perf, not capability; current per-call rebuild is fine for present sizes).
  - [x] **(c) CDCL VSIDS / benchmark — resolved by measurement: do not build it
        now.** Gate (a) (SAT-share dominance) is measured across breadth and is
        **family-dependent** (micro ≈0.31, `bench_ab` ≈0.24 encoding-dominated;
        `Noetzli` ≈0.95 SAT-dominated), so it does not uniformly fire, and gate (b)
        (a CaDiCaL/Kissat gap on Axeyum CNF) is unmeasured. Per the methodology the
        custom-CDCL track is correctly deprioritized; encoding reduction is the
        higher-value lever. Revisit only if a SAT-dominated family *also* shows a
        CaDiCaL/Kissat gap. (Benchmark OOM-safely: `--jobs 1` + guarded budgets;
        never sweep the public corpus at high `--jobs`/relaxed budgets — see
        memory `avoid-public-benchmark-runs`.)
  - [~] **(a) bit-blast-reduction certification — bounded slice done; scalable
        form is the lone open research program.** Small `QF_BV` `unsat` now carries
        a reduction-free term-level certificate in the `Evidence` envelope
        (`Evidence::UnsatTermLevel`), closing the term↔CNF trust gap entirely for
        the tractable case. The *scalable* form — machine-checking large-instance
        `unsat` at the term level — requires a **verified bit-blaster** (the
        term→AIG step); there is no sound bounded slice short of that verified
        reduction, so it is a genuine multi-increment research effort (a verified
        compiler in miniature), intrinsically the open frontier of a proof-carrying
        reasoning framework. The precise design, the circularity obstacle, and a
        concrete staged path (a trusted-reference + miter differential step **(B)**,
        then a width-parametric verified bit-blaster **(A)**) are recorded in
        [scalable bit-blast certification](docs/research/07-verification/scalable-bitblast-certification.md).
  - Real + bit-blasted theory combination is complete (reals share no sort with
        those theories, so the lazy-SMT loop suffices); general Nelson-Oppen would
        only be needed to combine two shared-sort theories, which the current set
        does not present.
- [ ] **Incremental performance + parity (parallel R&D):** port the sparse-CNF
      optimizations to the incremental encoder; add a warm-vs-cold benchmark to
      quantify the incrementality win; activation-literal GC for long sessions.
- [ ] **Phase 5 supported-slice expansion (parallel track):** use the version 11
      smallest-DAG selector artifacts, the version 12 root-direct selector
      artifacts, the version 13 greedy selector diagnostic, the version 10
      adaptive exact-target artifacts, the version 9 static exact-target
      artifact, the version 8 relaxed support-slice artifact, and the version 7
      conservative artifacts
      to expand beyond two decided public instances without merely raising
      timeouts or caps. Reduce the remaining AIG/CNF/SAT cost exposed by
      replay-refinement, especially the near-cap `EncodingBudget` frontiers in
      StringMatching, TCP, MobileDevice, VideoConf, and Composition; optimize
      the current lowering/encoding; improve refinement-target selection beyond
      single-assertion shape; or implement the next missing high-value BV
      encoding. Rerun the public `sat-bv` vs Z3 comparison and keep
      unsupported, unknown, performance, and soundness triage distinct.
- [ ] Then follow the roadmap phase by phase; each phase has explicit
      exit criteria.

## How To Resume Work (for a human or an agent)

1. Read **Status** and **Next Actions** above.
2. Read the [roadmap](docs/research/08-planning/roadmap.md) for the current
   phase and its exit criteria.
3. Read the
   [foundational DAG](docs/research/08-planning/foundational-dag.md) before
   adding operators, rewrites, encodings, backends, evidence artifacts, or
   logic fragments.
4. Before changing architecture, check
   [open questions](docs/research/08-planning/research-questions.md) and
   [decision records](docs/research/09-decisions/README.md) — decisions close
   as ADRs, not as silent code choices.
5. New research notes start from
   [templates/research-note.md](docs/research/templates/research-note.md).
6. When a session ends: update **Status**, re-order **Next Actions**, and
   note any new ADRs here.

## Standing Rules

- The pure Rust core builds with no C/C++ dependency; native backends
  (Z3, Bitwuzla) are feature-gated leaf crates.
- Semantics, model/proof lifting, and replay/checker routes must be explicit
  before a new operator, rewrite class, encoding, backend, or logic fragment
  becomes public surface.
- Every transformation layer ships with its check (evaluator equivalence,
  round trips, lift maps) and a differential test once an oracle exists.
- Expensive bets are gated by the
  [benchmarking methodology](docs/research/08-planning/benchmarking-and-performance-methodology.md)
  — no custom CDCL core until its gate fires.
- `unknown` is a first-class result. Determinism (same input, same seed, same
  output) is a public API promise.

## Map

| Where | What |
|---|---|
| [docs/research/README.md](docs/research/README.md) | Research index and reading order. |
| [docs/research/08-planning/roadmap.md](docs/research/08-planning/roadmap.md) | Phased plan with exit criteria and gates. |
| [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md) | Logic/math dependency DAG and layer contracts. |
| [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md) | Open question register. |
| [docs/research/09-decisions/](docs/research/09-decisions/README.md) | ADRs: how questions get closed. |
| `crates/` | Cargo workspace: `axeyum-ir`, `axeyum-aig`, `axeyum-bv`, `axeyum-cnf`, `axeyum-query`, `axeyum-rewrite`, `axeyum-scenarios`, `axeyum-solver`, `axeyum-smtlib`, `axeyum-bench`. |
| [CLAUDE.md](CLAUDE.md) | Agent guidance: session protocol, commands, hard rules. |
| [references/](references/README.md) | Gitignored reference clones; `scripts/fetch-references.sh`. |
