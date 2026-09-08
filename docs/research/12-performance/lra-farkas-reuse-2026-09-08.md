# Half the budget was recomputing a certificate we had just thrown away

**Date:** 2026-09-08 · **Population:** the 22 `QF_LRA` files bound by the
lazy-SMT route (`bench-results/watchdog-blind-files-20260908/qf_lra_blind22/`)
· **Machine:** s5 (idle, 16 cores, `taskset -c 0-7`), 24 s budget, serial
· **Artifacts:** `bench-results/lra-farkas-reuse-20260908/`

## The defect

`crates/axeyum-solver/src/dpll_t.rs`'s refinement loop refuted each cube with
`check_with_lra_within`, whose `CheckResult` **cannot carry evidence**. The
Farkas certificate that `decide_within` had just built and self-checked was
dropped at `lra.rs`'s `Decision::UnsatFarkas { .. } => Ok(CheckResult::Unsat)`,
and `conflict_core` then called `lra_farkas_certificate`, which re-ran `decide`
on the identical literal set to get the multipliers back.

The second call also took **no deadline**, so a loop that checked its budget
once per round could still spend unbounded time inside one round. A call with no
interruption point inside a budgeted search means the budget is not a budget.

## Were the two calls really on the same literal set?

Yes — measured, not assumed. `conflict_core` now counts where each conflict's
certificate came from, and the four provenance counters partition the
blocking-clause total exactly:

| run | blocking clauses | reused | re-derived (absent / stale / unverified) |
|---|---|---|---|
| shipped HEAD over the 22 files | 2,745 | **2,745** | 0 / 0 / 0 |

Not one conflict in the whole population needed the second solve. The re-derivation
paths are kept because `UnsatTrivial` (a literally-`false` literal) carries no
linear refutation, but on this corpus they never fire.

## The share table

Same table the instrumentation lane produced, so the rows compare directly.
`base` is `95c5ed7fa`; `HEAD` is the shipped commit.

| stage | base | HEAD |
|---|---|---|
| skeleton (SAT over the Boolean skeleton) | 4,732 ms · 1.0% | 9,825 ms · 2.1% |
| theory check (deciding the cube) | 244,695 ms · 50.4% | 459,733 ms · 97.9% |
| **Farkas core (RE-deciding it)** | **235,978 ms · 48.6%** | **86 ms · 0.0%** |
| refinement rounds completed | 1,684 | 2,748 |
| wall clock | 492,368 ms | 477,310 ms |

The re-derivation stage is gone: 235,978 ms → 86 ms. The budget it freed goes
straight back into the search — **1.63x the refinement rounds in the same wall
clock**, and the theory check's share rises to 97.9% not because it got slower
(145 ms/round before, 167 ms/round after) but because it is now nearly all of
the loop.

## How many of the 22 now decide

**Three, the same three as before.** Nineteen still exhaust the 24 s budget.
The files that already decided got materially faster:

| file | base | HEAD | |
|---|---|---|---|
| `no_op_accs.base.smt2` | 17,925 ms | 10,617 ms | −41% |
| `frame_prop.base.smt2` | 6,113 ms | 4,011 ms | −34% |
| `fs_not_sc_seen.base.smt2` | 4,310 ms | 3,110 ms | −28% |

So this is a 2x on the loop's throughput and no new decisions at this budget:
19 files need more than 1.63x the search, not a constant factor. What the fix
does buy is that the next improvement to this route is now measured against a
loop that spends 98% of its time on the theory decision, where the remaining
work is — instead of against one where half the answer was "we did it twice".

## Reference frame

Timing on s4 was not trusted; s5 was idle. Two **base-vs-base** control runs
before the A/B:

| run | wall | rounds | theory share | core share |
|---|---|---|---|---|
| base A | 492,368 ms | 1,684 | 50.4% | 48.6% |
| base B | 492,256 ms | 1,717 | 50.4% | 48.7% |

0.02% apart on wall and 2.0% on rounds, with the stage shares identical to
0.1 pp. Two HEAD runs (before and after a behaviour-neutral extraction) came in
at 476,151 / 477,310 ms and 3,028 / 2,748 rounds — so **round count carries
about ±10% run-to-run noise on the HEAD side and wall clock about ±0.3%**. Both
HEAD round counts are far outside both base round counts, and the core-stage
collapse (three orders of magnitude) is not a frame question at all.

Verdicts are identical across all four runs: 3 `unsat`, 19 `unknown`, no file
disagreeing with any other run.

## The correctness bar

A Farkas certificate is what makes an `unsat` checkable, so reusing a stale one
is a **wrong `unsat`**, not a slow one. `FarkasCertificate::verify()` does not
protect against this: it proves the multipliers collapse **its own atoms** to a
contradiction, and that stays true after the surrounding cube has changed.

Reuse is therefore gated on `CarriedCertificate::binds_to` — the certificate
travels with the literal set it refutes, and is admitted only for exactly that
conjunction, in that order (the multipliers are positional). It is **also
re-verified on the consuming path**, not merely where it was built: a check that
only ever runs on the producing path cannot fail on the path that turns
multipliers into a blocking clause.

`dpll_t::tests::a_certificate_from_a_different_literal_set_is_rejected_and_rebuilt`
donates a certificate whose zero multiplier sits on a different literal, at
**equal length** so the existing `multipliers.len() == assignment.len()` shape
check cannot reject it. The core the stale multipliers would name is jointly
**satisfiable**, so a blocking clause built from it would rule out satisfiable
assignments. The test asserts both the identity of the rebuilt core and the
property that the returned core actually refutes the recipient cube.

**Mutation control, run:** making reuse unconditional (deleting the `binds_to`
arm) took the `-p axeyum-solver --lib --features full` sweep from
`1556 passed; 0 failed` to `1555 passed; 1 failed` — exactly one test, and it is
that one.

## Gates run

| gate | result |
|---|---|
| `-p axeyum-solver --lib --features full` | 1556 passed, 0 failed |
| `--features full --test corpus_regression` | 1 passed |
| `--features z3 --test qf_lra_differential_fuzz` | 5 passed |
| `--features z3 --test simplex_lra_fallback_differential` | 1 passed |
| `--features z3 --test qf_uflra_differential_fuzz` | 1 passed |
| `--test progress_frontier --features full` | 12 passed |
| 12 affected integration suites (`dpll_t`, `lra`, `lra_online`, `cdclt_lra_online`, `interpolant`, `evidence`, `route_attribution`, `deadline_honored`, `support_matrix`, `farkas_over_the_integers`, `math_resource_lra_routes`, `auto`) | 376 passed, 0 failed |
| `scripts/check-clippy-complete.sh` | 0 diagnostics, 836 of 836 targets linted |

Every count above is nonzero; the feature-gated suites were confirmed to compile
a real binary rather than exiting 0 on an empty one.

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
AXEYUM_SWEEP_BIN=<binary> scripts/trace-sweep.sh \
  bench-results/watchdog-blind-files-20260908/qf_lra_blind22/files.txt <out-dir> 24
scripts/trace-sweep-report.py <out-dir> "<label>"
```

`AXEYUM_SWEEP_BIN` is what makes a base-vs-HEAD A/B (and the base-vs-base
control that must precede it) run through identical harness code.
