# Improvement list, 2026-09-16: the solver as a security tool

Written the same afternoon the cindergraph defects example landed
(`python/examples/cindergraph_defects/`, commit `defc4f806`) and the five-worst-
divisions campaign was paused
([stock-take](five-divisions-stock-take-2026-09-16.md), queue item A13). The
sibling lists are `docs/improvement-list-2026-09-16.md` in cindergraph and
`docs/development/improvement-list-2026-09-16.md` in Glaurung. Every item here
names the measurement or the round trip that produced it.

## Fix

1. **The example drives `axeyum_cli` as a subprocess; it should call the
   Python bindings.** The bindings expose the whole SMT-LIB front door
   (`axeyum.smt`: `solve_smtlib_*`, `get_value`, incremental sessions, unsat
   cores); they were simply not built in this checkout, and the guide's
   "install with `uv`" path did not make that obvious. Build the native module
   in the example's setup, switch `check.py` to `axeyum.smt`, and make
   `docs/user-guide/python.md` say in its first screen how to build it.
2. **The lifter re-derives overflow by double-width arithmetic; the parser
   already accepts SMT-LIB 2.7's `bvsaddo`, `bvuaddo`, `bvsmulo`, `bvumulo`,
   `bvnego`** (`crates/axeyum-smtlib/src/parse.rs:20684`). Use them in
   `lift.py`, and list them in `docs/reference/smtlib-support.md`, which is
   where a consumer would have looked.
3. **`cargo build -p axeyum-bench --example axeyum_cli --features full` does
   not exist**; the flag is `--features axeyum-solver/full`, and the failure
   message names the wrong package. Add a `full` feature to `axeyum-bench`
   that forwards, and use it in every doc line that builds a CLI.
4. **A stranger reaches `smtcomp_cli` first and it cannot print a model.** The
   competition interface is right to be single-verdict; the user guide should
   point at `axeyum_cli` before it. One paragraph in `first-smtlib-query.md`.
5. **Property tests whose input box cannot reach the trap.** The wrong-sign
   bug in `RealAlgebraic::sign_at` (ADR-2134) survived a float-oracle property
   test because its coefficient box had no integer solution for the failing
   shape. Audit every property test in `axeyum-ir` and `axeyum-solver` that
   samples from a fixed box, and give each a control that the box can express
   at least one known counterexample of the property's negation.

## Add

6. **A value-selection policy on the incremental engine.** Glaurung measured
   that 79 % of both-sat queries return different valid models and wants
   least-unsigned or prefer-small witnesses; the example spends up to five
   solves per finding to get a witness a human can read. A policy on
   `IncrementalBvSolver` (and a `(set-option :model-preference ...)` in the
   front door) is one mechanism serving both. The SAT core's phase policy
   (`axeyum-cnf/src/phase_policy.rs`) is where a prefer-zero default lands.
7. **A bounded-minimisation helper in the front door.** "Smallest witness
   under a magnitude bound, else the unbounded one" is what the example does
   by re-solving with growing bounds; expose it once, tested, rather than
   having every consumer write the ladder.
8. **The canonical constraint cache (ADR-0303) as a library feature** of the
   incremental engine, keyed on the sorted duplicate-elided assertion set,
   instead of leaving it to each consumer's adapter. Glaurung measured 62 %
   exact reuse across 12,902 checks.
9. **Per-check timing and phase attribution in the Python bindings.**
   `IncrementalBvSolver::stats()` has it; `axeyum.smt` does not surface it,
   and Glaurung wrote its own `check_assuming_measured` for the lack.
10. **Bounded loop unrolling in the lifter.** The classic
    `for (i = 0; i <= n; i++)` off-by-one is refused today; cindergraph marks
    the back edge and exposes `for_cond`/`for_step`, so unrolling to a stated
    bound with the bound in the report is a contained change.
11. **More sinks with a runtime oracle.** `strlen`/`strcpy`/`snprintf` length
    reasoning (the string theory is the strongest on the board: QF_SLIA
    196/200), `malloc` size arithmetic, and use of an uninitialised local
    (`x_uninit` symbols already exist in the lifter and are simply
    unconstrained). Each needs the sanitizer that observes it named in
    `SANITIZER_FOR`, or it is not a finding.
12. **Run the pipeline over real inputs.** cindergraph's own C fixtures, then
    Glaurung's decompiled output. The eight samples are mine; a finding on
    code nobody wrote to be found is the first number worth quoting.
13. **Inventory Python examples.** `docs/reference/examples.md` covers Cargo
    examples only; `python/examples/` has two and nothing lists them.

## Change

14. **Re-measure the Glaurung six-cell campaign at head before any more
    board work.** Glaurung's list, item 3. It is the one number that decides
    whether the pure-Rust solver becomes a default backend somewhere, and it
    has not been produced since July. If Axeyum is still slower one-shot, the
    July profile already says where (97 % in the SAT solve on extract/concat-
    heavy path conditions), and A12's CDCL work should be benchmarked on
    Glaurung's four-driver corpus rather than on SMT-LIB lists.
15. **Resume A13 in its order** when the security work does not need the
    solver's attention: the ADR-2134 held-out draw (~60 min, QF_NRA 126
    expected), the two QF_LRA defects that are mislabelled as a missing
    construct, the NIA lemma-versus-budget separation, then nested-binder
    activation. Each is named at a file and line in the stock-take.
16. **Wire `check.py` into a gate** once cindergraph is a pinned dependency
    (its `__version__` is item 8 on its list). Until then it is a runnable
    example with an exit status, not a check anyone runs.

    **Done 2026-09-17 (lane AX-GATE, see `docs/plan/status/ax-gate.md` for the
    commit).** `cindergraph` is pinned in `pyproject.toml`'s dev group at
    `8bd20512158d19d4cf632caba4bbed629271a3e5` (`uv.lock` updated; `uv sync
    --dev` installs it, `__version__` 0.1.0) and `check.py`'s first line
    prints version, installed commit and pinned commit.
    `scripts/check-cindergraph-defects.sh` is a step of `just py-check` and of
    `scripts/check.sh`'s Python block: it refuses without the native module or
    cindergraph, skips loudly without `clang`, and re-derives the verdict from
    `results.tsv` through `scripts/check-cindergraph-defects.py` —
    `CINDERGRAPH_DEFECTS|rows=33|replayed=18|dead=2|clean=13|bounded=0|no_oracle=0|failures=0|PASS`.
    Three subject mutations (`mutation_controls.py cindergraph-defects`) each
    kill exactly one test. The lifter now reads cindergraph's `line`, `facts`
    (capacity / strlen / unroll) and `loop_kind` with its old readings as the
    fallback; 356 queries and 18 harnesses byte-identical at the pin.
