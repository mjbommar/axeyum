# QF_NRA: deriving the bounds the exact deciders were missing — 2026-09-09

Lane `nra-fbbt-bounds`. Acts on the largest single capability finding in
[`qf-nra-loss-attribution-2026-09-09.md`](qf-nra-loss-attribution-2026-09-09.md):
**37 of the 75 `QF_NRA` parity losses have every nonlinear atom in one or two
variables, and every one of them declares more variables than that** — the extras
occur only in *linear* atoms. But `nra_real_root::decide_component` dispatches on
the **connected component's** variable count, and `connected_components` unions
over every atom, the linear ones included, so a query whose nonlinear content
belongs to the 1-variable sign-cell decider or the 2-variable resultant/CAD
decider is handed to the ≥3-variable CAD, which declines.

## What was built

`crates/axeyum-solver/src/nra_fbbt.rs` — feasibility-based bound tightening as a
**refutation-only** producer, with a Farkas checker between the search and the
verdict. `nra_real_root.rs` carries the glue (three conversions and a loop) and
hooks it at the tail of `decide_real_poly_constraint`, so it runs only after the
multivariate decomposition has declined or failed to certify.

The transfer argument is one-directional by construction. The route hands a
decider a **subset** of the query's atoms (the nonlinear component, plus the
linear atoms already inside its variables) together with bounds **implied** by
the query. A refutation of that refutes the whole; a *model* of it need not
satisfy the discarded atoms.

## What makes `sat` structurally impossible, rather than merely absent

Three properties, each of which would have to be *removed* for a `sat` to escape:

1. **The success type has nowhere to put a model.** `nra_fbbt::Refutation` holds
   three `usize` counters — nonlinear atoms, derived bounds, component variables
   — and has no `Sat` or `Unknown` variant. `decide_component` does return
   `ComponentOutcome::Sat(bindings)`; the route's `matches!(…, Unsat)` discards
   it, and even a code change that tried to propagate those bindings would have
   no field to write them into.
2. **`Refutation::new` is the only constructor and takes only counters.** A model
   cannot be smuggled through it.
3. **`Refutation::into_check_result` has a constant body** — `CheckResult::Unsat`,
   no branch, no field read. It is the single bridge from this route to a solver
   verdict. `the_only_verdict_this_route_can_produce_is_unsat` drives it over
   several counter tuples to hold that.

Reporting `sat` from this route therefore requires adding a variant, a field and
a branch. It is not a `return` anyone can forget.

## Untrusted search, trusted checking

The propagation in `derive_bounds` is ordinary interval FBBT and is **not
trusted**. It may compute a wrong value, cite the wrong fact, or overflow; the
worst any of that does is lose a bound. Every proposal goes to `verify`, which
re-derives the claim from the facts the certificate cites:

```text
  target − Σ λⱼ·pⱼ  must be a NONNEGATIVE CONSTANT,   every λⱼ > 0
  ⟹  target ≥ Σ λⱼ·pⱼ ≥ 0
```

where each fact is oriented `p ≥ 0` / `p > 0` and a claimed bound becomes its own
target (`u − x` for `x ≤ u`, `x − l` for `x ≥ l`). Bounds are appended to the fact
pool **only after** the checker accepts, so a citation always names an
already-checked fact and the induction closes. `CertifiedBound` has a private
field and no constructor other than `verify`'s success path, so an unchecked
bound cannot reach a decider from another module.

### The checker's guards, mutation-controlled

Registered as the `nra-fbbt-checker` suite in
`scripts/tests/mutation_controls.py`. Baseline green, 15 tests. Each guard
deleted in turn:

| guard deleted | tests killed |
|---|---|
| residual is nonnegative (a bound tighter than entailed) | 2 — the upper- and lower-side tests |
| multiplier is strictly positive | 2 — the negative and the zero case |
| variables cancel | 1 |
| a strict claim has a strict witness | 1 |
| certificate is non-empty | 1 |
| citation is inside the pool | 1 |
| a fact is cited once | 1 |

**7 of 7 killed, and no guard's deletion killed another guard's test.** The
separability comes from each test asserting the *rejection reason*, not just
`is_err()`: without that, a certificate violating two guards is rejected by
whichever runs first and deleting the second changes nothing observable.

The route has its own suite, `nra-fbbt-route`, over the six front-door tests:

| mutation | tests killed |
|---|---|
| the propagation's bound SENSE reversed | 3 |
| `max_component_vars: 2 → 0` (the route turned off, nothing else changed) | 2 |

Both mutations kill `the_fuzz_seed_class_shape_reaches_the_derived_bound_route`,
which is the point of that test: it is the one that fails when the route stops
being reached, which no verdict assertion can detect.

### Proving the adversarial test can fail

The rule is that a checker which cannot fail is worse than none, so the
adversarial test was made to fail on demand. Two edits at once, in a scratch
copy — the derivation made 20× tighter than entailed **and** the checker's
residual guard deleted, which is exactly what a checker without that guard would
admit:

```
test a_satisfiable_query_with_a_three_variable_transitive_bound_is_not_refuted ... FAILED
  panicked at: x=8, y=5, z=0 satisfies this; got Unsat
test result: FAILED. 4 passed; 1 failed
```

**Exactly one test died, and it died with a wrong `unsat` on a satisfiable
query** — the precise failure mode. With the residual guard left in place and
only the derivation weakened, the checker rejects every proposal, no wrong verdict
appears, and what dies instead is the positive control. Both mutations are
recorded; the second is the one that says the test is not vacuous.

### One negative control was vacuous, and is now labelled

`a_two_variable_satisfiable_query_is_not_refuted` never reaches this route:
`decompose_multivariate`'s two-variable non-strict CAD decides it first. That was
found by the same mutation — it stayed green while the three-variable test
flipped — and it is now documented as a front-door non-regression check rather
than counted as coverage of the derived bounds.

## The differential gate, and the seed class that did not work

The `z3` differentials are the only checks that compare this route's verdicts
against an independent solver, so a new `unsat` producer needs a seed class that
generates its shape. The general `nra_differential_fuzz` generator structurally
cannot: it emits 1..=4 atoms with coefficients in `−3..=3` and a uniform
comparator, and the probability that it produces a nonlinear atom confined to ≤ 2
of its variables *and* a constant bound on another *and* a linear atom carrying
that bound across is negligible — while the last of the three is the whole
mechanism. This is the `a946f925` shape: a corpus sweep plus a fuzz that avoids
the corner is not a soundness gate.

**The first seed class was written, and reached the route zero times.** What
makes this worth recording is that the fuzz's own tally could not say so:

| | route on | `AXEYUM_NRA_FBBT=off` |
|---|---:|---:|
| total instances | 2,000 | 2,000 |
| jointly decided | 1,927 | 1,927 |
| agreements | 1,927 | 1,927 |
| DISAGREEMENTS | 0 | 0 |

Identical. That reading is equally consistent with *the route ran and changed
nothing* and with *the route never ran*, and only the second makes the seed class
decoration. A verdict tally cannot separate them.

So the route grew a funnel counter (`nra_derived_bound_coverage`), and the fuzz's
coverage assertion is on the counter rather than on the tally. It read:

```
NraDerivedBoundCoverage { consulted: 1679, split_ok: 5, bounds_derived: 4,
                          components_offered: 0, refutations: 0 }
```

and the fuzz went red. Two causes, both in the generator and both found by
dumping instances rather than by reasoning about dispatch order:

- **`gap = 0` chain links are linear contradictions.** `x − y − 0 < 0` and
  `x − y + 0 ≥ 0` together are unsatisfiable, and the front door refutes that
  before any nonlinear route runs. Most of the class was that.
- **`!=` on a polynomial is satisfiable almost everywhere**, so those instances
  are decided upstream too.

And a third, found by raising the degree: at degree 2 the N-variable CAD decides
the system outright, so the route — consulted only after that declines — is never
reached. The real population is degree 6. A seed class that stops at degree 2
generates the *shape* and still never exercises the route.

Redesigned (degree 2..=6, `gap ≥ 1`, no `!=` on the nonlinear atom, the anchor
dropped outright 1 time in 5 so a fifth of the class leaves the variable
unbounded), the same 399 instances of the class read:

```
consulted: 570, split_ok: 570, bounds_derived: 564,
components_offered: 564, refutations: 65
```

**65 refutations for Z3 to adjudicate**, where there had been none.

### The gate itself

The full 2,000-instance sweep, one binary, with the redesigned class in place:

| | |
|---|---:|
| total instances | 2,000 |
| jointly decided | 1,799 |
| agreements | 1,799 |
| **DISAGREEMENTS** | **0** |
| axeyum `Unknown` | 4 |
| axeyum timeout (adjudication-neutral) | 197 |
| `Sat` models replayed through the ground evaluator | 1,265 |

and the funnel:

```
consulted: 2263, split_ok: 589, bounds_derived: 579,
components_offered: 575, refutations: 66
```

**66 refutations from this route, every one adjudicated by Z3, zero
disagreements.** That is the sentence the seed class exists to make sayable; the
first version of it could not say anything at all.

The other two `z3`-gated differentials named for this fragment also pass with
nonzero counts: `qf_nia_divmod_const_differential_fuzz` (1 test) and
`qf_nia_divmod_var_differential_fuzz` (1 test).

## The A/B on the loss population

`bench-results/parity-losses-20260908/QF_NRA.txt` (75 files), `smtcomp_cli`, 24 s
wall and 8 GiB via `scripts/mem-run.sh`, `taskset -c 0-7`, arms **interleaved per
file** so ambient load falls on both equally. One binary, sha256
`baf82911718a1d269823bf8722bd2dec1dc8b878a3d4096f1828b493e82d3118`; the arms
differ only in `AXEYUM_NRA_FBBT`. The host was not idle (load 1.5–9.4 across the
sweep, other lanes on the box), which is why the conclusion is stated in decided
counts.

| | `off` | `derived-bounds` |
|---|---:|---:|
| sat | 2 | 2 |
| **unsat** | **0** | **2** |
| unknown | 47 | 46 |
| no answer within 24 s | 26 | 25 |
| verdict regressions | — | **0** |
| total wall | 822 s | 819 s |

Three files changed and only two are verdicts:

| file | `off` | `derived-bounds` |
|---|---|---|
| `sqrt-1mcosq-8-chunk-0014` | unknown (0.1 s) | **unsat** (0.1 s) |
| `sqrt-1mcosq-8-chunk-0485` | unknown (0.1 s) | **unsat** (0.1 s) |
| `sin-cos-346-b-chunk-0543` | no answer (24 s) | unknown (20.4 s) |

The third is a timing artifact under contention, not a verdict change. Both new
results agree with the files' own `:status unsat`.

## What this did not do

- **The gain is 2, not 37.** The other 35 files in the shape class are consulted,
  bounds are derived, and the deciders still do not close them. That is a
  statement about the deciders' reach on those polynomials, not about admission,
  and it is the next question on this route rather than a shortfall of this one.
- **The 14-file atom-capacity class is untouched**, as scoped. Those project
  11,960–36,945 linear-real atoms against `lra_theory::MAX_ONLINE_LRA_ATOMS`'s
  1,024. Deriving bounds does not move a number that is 11–36× out.
- **The cost is not zero on the fuzz population.** With the redesigned seed class
  the sweep's `axeyum timeout` count rises from 66 to 197 of 2,000, because the
  class itself is higher-degree than the general one — a property of the
  population, not a measured cost of the route. On the parity list the total wall
  clock moved by 0.4% in the route's favour.

## Gates

Every count read off the run. `--features full` and `--features z3` where the
suite requires them; a zero count would mean the suite compiled to nothing.

| gate | result |
|---|---|
| `-p axeyum-solver --lib --features full` | **1,653 passed**, 0 failed |
| `--features full --test corpus_regression` | 1 passed |
| `--features full --test nra` / `nra_real_root` / `nra_fbbt_route` | 37 / 86 / 6 passed |
| `--features z3 --test nra_differential_fuzz` | 3 passed, 0 disagreements |
| `--features z3 --test qf_nia_divmod_const_differential_fuzz` | 1 passed |
| `--features z3 --test qf_nia_divmod_var_differential_fuzz` | 1 passed |
| `--test progress_frontier --features full -- --test-threads=1` | 12 passed, no REGRESSION |
| `scripts/check-clippy-complete.sh` | 839 of 839 targets, 0 diagnostics |
| `cargo fmt --all --check` | clean |
| `check-config-registry-staleness.py` | 475 entries, no stale justification |
| `check-admission-limit-basis.py` | 156 declarations, every basis resolves |
| `scripts/check-merge-hygiene.sh` | PASS |
| `scripts/check-links.sh` | all links ok |
| `mutation_controls.py nra-fbbt-checker` | 7 of 7 guards killed |
| `mutation_controls.py nra-fbbt-route` | 2 of 2 mutations killed |

One gate is red and it is **not** this lane's:
`RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver --all-features --no-deps`
reports 11 private-intra-doc-link errors, in `auto.rs`, `euf_egraph.rs`,
`lazy_smt_counters.rs`, `lia_counters.rs`, `memory_budget.rs` and
`qinst_egraph.rs`. This lane touches none of those six files (its diff is
`nra_fbbt.rs`, `nra_real_root.rs`, one `use` line in `lib.rs`, one registry
entry, two test files, `mutation_controls.py` and this document), and none of
the eleven names a symbol it introduced. It is reported rather than fixed
because fixing another lane's doc links inside this diff would make the diff
unreviewable.
