# CNF, SAT, and propositional evidence

`axeyum-cnf` converts AIG roots to conjunctive normal form (CNF), runs pure-Rust
SAT engines, and supplies the propositional proof formats and checkers used by
finite-domain routes.

## Tseitin encoding

[`tseitin_encode`](../../crates/axeyum-cnf/src/lib.rs) assigns a CNF variable to
each relevant AIG node and emits clauses enforcing the node's Boolean meaning.
It returns a `CnfEncoding`, not just a bag of clauses. The encoding retains root
variables, AIG-variable bindings, and statistics so models and diagnostics can
cross the boundary in either direction.

```mermaid
flowchart LR
    aig["AIG + asserted roots"] --> tseitin["Tseitin encoder"]
    tseitin --> formula["CNF clauses"]
    tseitin --> map["AIG ↔ CNF bindings"]
    formula --> sat["SAT engine"]
    sat -->|SAT assignment| map
    map --> inputs["AIG input bits"]
    sat -->|proof-producing UNSAT route| checker["Proof checker"]
```

`CnfFormula` has deterministic variable and clause order, DIMACS I/O, and an
evaluator. Constants and root polarity are handled explicitly rather than
being inferred later from solver state.

## Solving modes

**The in-tree native CDCL core is the SAT engine, on every path**
([ADR-1703](../research/09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)).
It is `crates/axeyum-cnf/src/proof_sat.rs`: a flat clause arena with per-clause
headers, blocking-literal watch lists, VSIDS with geometric decay and rescale,
phase saving plus target rephasing, Luby restarts (EMA-glue implemented and
selectable), LBD glue tiers and `reduce_db`.

Three entry shapes:

| Entry | Use |
|---|---|
| `solve_with_native_core{,_timeout,_limits}` | one-shot, a `SatResult` |
| `solve_with_drat_proof*` | one-shot, and hand back the DRAT proof |
| `NativeIncrementalCdcl` / `IncrementalSat` / `IncrementalCnf` | warm: clauses added between solves, assumptions per solve, learned clauses and heuristics retained |

Deterministic budgets are in **conflicts**; wall-clock deadlines are checked on
a fixed conflict cadence, so the search trajectory up to the stopping point is
identical to an unbounded run and only *whether* it stops is time-dependent.
Neither limit ever produces a verdict — both yield `unknown`.

The generic SAT trait reports capabilities and keeps `sat`, `unsat`, and
`unknown` distinct.

CNF preprocessing includes bounded variable elimination, subsumption,
vivification, and compaction. Any pass that changes variable meaning retains a
mapping or reconstruction object. A smaller formula is useful only if a model
or proof can still be related to its input.

### What that changed about UNSAT assurance

Every `unsat` the native core reports is derived by learning RUP clauses ending
in the empty clause, so a DRAT proof exists **by construction** and is checkable
by `check_drat`, or — with hints — by the linear `check_lrat`. "Proofless
UNSAT" is no longer a category of result this crate can produce; spending or not
spending the checking time is a per-call choice, made by `prove_unsat`.

Two limits, stated rather than smoothed over: proof recording is **off on the
warm path** for speed, so a warm `unsat` is still stamped `Unchecked` unless
recording is requested; and an `unsat` **under assumptions** derives no empty
clause at all, reporting a failed-assumption core instead — that is inherent to
assumption-based solving.

The public contract is unchanged in shape: SAT models must replay, and UNSAT
assurance is stated at the level actually checked — a search verdict is never
relabelled as a checked proof. See the
[`SolverConfig` reference](../reference/solver-config.md) for the exact selection
and fail-closed behavior.

### BatSat

`rustsat-batsat` was the first pure-Rust adapter (ADR-0007) and is retired as an
engine. It survives only behind the non-default `batsat-reference` cargo
feature, as an independent referee for differential testing — the role ADR-0002
gives Z3 — in
`crates/axeyum-cnf/tests/native_vs_batsat_differential.rs`. **The default
dependency graph contains no `batsat`, `rustsat`, or `rustsat-batsat`**; confirm
with `cargo tree -e normal -p axeyum-cnf`. Every suite behind that feature
compiles to zero tests without it and exits 0, so confirm a nonzero test count
before believing one of them passed.

## DRAT, LRAT, Alethe, and XOR

The crate can produce and check DRAT, elaborate supported **RUP-only** DRAT
proofs into LRAT, check that positive-hint LRAT slice, and parse/write/check a
selected Alethe core. RAT additions (negative hints) are outside the current
LRAT checker and elaborator and are rejected rather than silently accepted. It
also includes XOR extraction and GF(2) reasoning; bounded Gaussian conflicts
can emit a propositional justification for the conflict subset.

A checked DRAT or LRAT proof establishes that the encoded **CNF** is
unsatisfiable. It does not by itself prove that every earlier word-level or
theory transformation preserved the original query. End-to-end assurance also
needs checked lowering/normalization bridges recorded by the solver's evidence
route.

See [Proof and evidence routes](proof-stack.md) for that composition and the
[QF_BV proof cookbook recipe](../proof-cookbook/recipes/qf-bv-bitblast.md) for a
concrete artifact flow.
