# Lane `nra-clause-loop` — the clause loop, measured and certified (ADR-2131)

<!-- plan-section: lane-status -->

Status: the certificate for the clause loop's `unsat` is built and gating, the
two false-reject bugs it uncovered in ADR-2126's cell checker are fixed with
regression tests, the A/B arm is rebased so it is no longer confounded, and the
sizing is measured. Ship decision is in ADR-2131.

## What this lane was

[ADR-2126](../../research/09-decisions/adr-2126-exact-delineability-and-the-clause-loop-for-nra.md)
built the Boolean clause loop — CDCL(T) over polynomial sign atoms with
single-cell CAD as the theory — behind its own lever, **OFF and unmeasured**,
and withheld its `unsat` because three obligations had no checker. It named both
gaps as left undone. This lane is both.

## The sizing, and it corrects the premise twice

Re-derived on the current binary, one `--trace` pass per file through
`scripts/ledger-run-one.sh`, s5 cores 1/9/3/11, 24 s / 8 GiB.

- The pinned 200-file QF_NRA draw is **124 decided, 76 undecided** — the
  2026-09-15 board records 122. A board TSV is a snapshot.
- **34** of the 76 decline `non-conjunctive`, which is the loop's population.
- **The ceiling is 16, not 34.** 18 of the 34 are over the 48-atom cap; the one
  file with a Boolean leaf the loop cannot abstract has 321 atoms and is over
  the cap anyway, so it double-counts.
- **The atom cap is not a lever.** `n_atoms` is bimodal — 55 files at 3..12, one
  at 103, then 62 from 125 to 63,180 — and 48 sits in the empty gap. Moving it
  anywhere from 13 to 102 changes nothing.
- **No file in the population uses `ite`, `=>`, `xor` or `distinct`**, and `or`
  is binary in all but one. Those connectives are correctness surface, not reach.

## The certificate

`crates/axeyum-solver/src/nra_clause_cert.rs`. ADR-2126's three obligations, one
kind of evidence each:

| obligation | evidence |
|---|---|
| every blocking clause implied over the reals | the `CellRefutation` per lemma, now KEPT and re-checked by `check_cell_refutation`; plus a walk requiring every cell the covering closes to be closed by an atom the clause CITES |
| the SAT core's refutation | a DRAT proof from `solve_with_drat_proof_within` — a **second, independent solve** — checked by `check_drat`. The solver that found the refutation does not also get to be the evidence for it |
| the Tseitin abstraction equisatisfiable | the certificate carries the GATE TABLE, not the clauses, so the checker derives them; then freshness (the conservative-extension argument), faithfulness (a walk of the original terms against the table), and rooting |

`CadDecline::ClauseLoopUnsatUncertified` is removed — it meant "no checker
exists", which is no longer true, and a cause no code can produce reads as a
live limitation in every table that prints the enum.

## What actually blocked it

Not the clause loop. `check_cell_refutation` **rejected `x > 1 ∧ x < 0`**,
reached by the SHIPPED conjunctive route. Two false-reject bugs in
`has_root_strictly_inside`:

1. a root of the closing atom sitting exactly ON the cell boundary — handled for
   exact endpoints only, and bisection from the Cauchy bracket never marks the
   rational 1 exact;
2. an unbounded cell whose Cauchy bound does not clear its finite endpoint —
   cell `(2, +∞)` with `q = x`, bound exactly 2.

Both fixed by arguments over regions proved root-free. Three regression tests,
beside the checker rather than beside the loop, including a
satisfiable-conjunction control so the fixes cannot be read as the checker
getting looser.

## The A/B arm was confounded

`CadPolicy::CLAUSE_LOOP` sat on `SINGLE_CELL_SAT`, which was the default when
ADR-2126 wrote it — and ADR-2126 then moved the default to `SINGLE_CELL`. The
two arms therefore differed in `emit_unsat` as well as `clause_loop`, so the
treatment arm had the single-cell route's `unsat` half switched OFF and every
verdict it contributes would have read as a loss caused by the loop. Rebased;
the separation test now reads its comparison arm out of `CAD_DEFAULT` rather
than naming it.

## What the references check

Neither reference solver checks a nonlinear lemma. z3's nlsat calls
`fail_if_proof_generation("nlsat", g)` (`nlsat_tactic.cpp:144`) and validates
only by an optional debug re-solve (`nlsat_solver.cpp:1160`); cvc5's covering
steps are `ProofRule::TRUST` (`coverings/proof_generator.cpp:106`, `:139`) and
its rule checker returns `Node::null()` unconditionally
(`coverings/proof_checker.cpp:33`). Our reach on this route is small; the
checked-evidence axis is uncontested.

## Landed changes

| change | where |
|---|---|
| the clause-loop certificate and its checker | `crates/axeyum-solver/src/nra_clause_cert.rs` |
| certified `unsat`, lemmas kept, testing surface | `crates/axeyum-solver/src/nra_clause_loop.rs` |
| two false-reject fixes + three regression tests | `crates/axeyum-solver/src/nra_cell_cert.rs` |
| new decline cause, second decline slot, arm rebase, widened dispatch | `crates/axeyum-solver/src/nra_real_root.rs` |
| the clause-loop cause in the route trace | `crates/axeyum-solver/src/auto.rs` |
| adversarial fixtures (12) | `crates/axeyum-solver/tests/nra_clause_cert_2131.rs` |
| the five NRA route files join `GOVERNED_FILES` | `crates/axeyum-solver/src/config_registry.rs` |
| two mutations replacing a stale anchor, one anchor disambiguated | `scripts/tests/mutation_controls.py` |
| sizing, shape analysis, A/B harness | `bench-results/nra-clause-loop-20260916/` |
