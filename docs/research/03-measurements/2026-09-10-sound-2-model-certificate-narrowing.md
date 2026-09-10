# A `sat` model narrower than the thing it was replayed against

Lane SOUND-2 (`AXEYUM_AGENT=SOUND-2-model`), roadmap items 2.10 and 2.11 in
`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`. Companion to the
pre-change site audit,
[`2026-09-10-narrower-model-than-replayed-site-audit.md`](2026-09-10-narrower-model-than-replayed-site-audit.md),
which was committed before any code changed (`d78a911cf`).

Commits: `d78a911cf` (audit), `f1ebb338e` (2.10), `76f7f54ae` (2.11).

Both items are the SOUND-1 shape — *a certificate must carry every distinction
its producer makes* — and the two of them together say something the individual
rows do not: this defect class is not a bug, it is a **construction**. Every one
of the fourteen sites was a hand-written "build a fresh `Model` and copy the
fields you remember." That construction has now shipped four measured defects
(`c41dd4264`, `9b259f7c2`, and the two below), and it will ship the next one the
day a component is added to `Model`, because nothing in the language or the test
suite makes a forgotten field visible.

---

## Item 2.10 — the status was wrong, and the direction it was wrong in matters

The row records 2.10 as **unexploited**: "SOUND-1 found no exploit — every shape
it built declined soundly upstream — so this is UNEXPLOITED, not a known
defect." That claim was re-verified rather than inherited, and it does not hold.

### The witness

```smt2
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x 3))
(assert (= (div x 0) 5))
(check-sat)
```

Before the fix, both `check_auto` and the public `solve_smtlib` front door
returned:

```
Sat, model = ["x=Int(3)", "!divmod_0=Int(5)"]
replay of assertion #1 against that model -> Ok(Bool(false))
```

Six further shapes were built and all six behaved the same way (the `mod`
variant, a strict inequality, a negation, a disjunction, a two-group version,
and a fully ground `(div 3 0) = 5`).

### Be precise about what is wrong

Three claims that are easy to run together, and are not the same claim:

| claim | true? |
| --- | --- |
| the **verdict** is wrong | **no.** SMT-LIB leaves `div`-by-zero underspecified, so `sat` is correct. |
| the **certificate** is wrong | **yes.** The emitted model does not satisfy the query. |
| **SOUND-1 was wrong** | **no, and this is the interesting part.** |

SOUND-1 looked for a wrong verdict and there is no wrong verdict here. The two
shapes that must be `unsat` by congruence —

```
(div x 0) = 5  AND  (div x 0) = 7
x = y  AND  (div x 0) = 5  AND  (div y 0) = 7
```

— were `unsat` before this lane's change and are `unsat` after it. ADR-1730's
congruence lemmas do their job. What nobody checked was whether the `sat` that
comes back is a certificate, and it is not. "Declined soundly upstream" was a
true observation about the wrong quantity.

The correct status line is therefore **neither** "unexploited" **nor** "a wrong
`sat`". It is: *a reachable, front-door-visible `sat` whose certificate does not
replay, with the verdict correct throughout.*

### Why the certificate cannot be right as things stand

`eliminate_int_divmod` maps each `div a 0` / `mod a 0` to a fresh unconstrained
`!divmod_k` — the SMT-LIB-faithful reading. The ground evaluator does not agree:
`eval` pins `div a 0 = 0` and `mod a 0 = a`
(`crates/axeyum-ir/src/eval.rs:830-846`). `Model` sits between the two with **no
component that can record which**, where the real case has `real_div_zero`.

So the choice that makes the query satisfiable is *structurally
unrepresentable*. This is strictly worse than SOUND-1's instance, where the
component existed and the build simply forgot to copy it.

There is a second, independent defect at the same site: `!divmod_0` — an
internal symbol of the elimination — was emitted to a caller that never declared
it. On two of the seven shapes the model contained the internal symbol and *not*
`x`.

### What was done

`auto::replay_int_linear_sat` wraps the existing ADR-1730 congruence guard at
its existing chokepoint. It strips the elimination's fresh symbols, replays the
**original** assertions against the artifact the caller receives, and declines
to a first-class `unknown` when that fails. This is the row's own first exit
criterion. The three cited line numbers had all drifted by 80-100 lines; the
sites themselves were unchanged in substance.

Capability cost measured at **zero**: 1,689 `--lib --features full` tests, both
`corpus_regression` suites, the 13 divmod tests and both z3 differential fuzzes
are unchanged. That is expected rather than lucky — this pass only eliminates
`div`/`mod` by a **constant**, so the exposure is a literal zero divisor, which
does not occur in the corpora.

### The capability-preserving follow-up, not done here

Give `Model` (and `Assignment`, and `eval`) an integer division-at-zero
component mirroring `real_div_zero`: a `dividend -> value` map for `div`, and a
second for `mod` (whose evaluator convention is `mod a 0 = a`, not a constant,
so it needs its own). `IntDivModElimination::replacements()` already exposes
`(original term, fresh symbol)`, so the solver side is cheap; the cost is that
this changes evaluator semantics across `axeyum-ir`, which per `CLAUDE.md`
wants an ADR before it becomes public surface. With it, all seven witness
shapes go back to `sat` and the tests written for 2.10 pass unchanged — they
assert *"a `sat` replays"*, not *"the answer is `unknown`"*, precisely so this
follow-up needs no test edits.

### Mutation table (2.10)

`auto.rs` mutated five ways, suite re-run each time, file restored byte-for-byte:

| mutation | tests that died |
| --- | --- |
| delete the replay loop in `replay_int_linear_sat` | 5 |
| delete the internal-symbol strip | 1 |
| revert the guard at the `lia-simplex` call site | 4 |
| revert the guard at the `lia-dpll` call site | 1 |
| revert the guard at the fused-group call site | 1 |

**On the first honest run of that table the last two rows were both zero.** One
shared helper, three call sites, and every div-at-zero shape in the file was
answered by `lia-simplex` — so two of the three sites were guarded by nothing
and the suite was green. Reaching `lia-dpll` needs Boolean structure the
conjunctive simplex declines; reaching the group needs that *and* more than one
worker, with `portfolio_groups_run()` as the control that says the group
actually ran rather than the sequential path running twice.

This is the general lesson and it generalizes past this lane: **a mutation
table over the shared helper does not test the call sites.** Mutate the call
sites separately or the count of covered sites is a guess.

---

## Item 2.11 — eleven sites, of which the row describes nine correctly

All eleven exist, all eleven still emit a narrower model than their replay
checked, none had been fixed. Full per-site table in the audit note. Four
corrections:

1. **`incremental.rs:7616` does not drop `real_div_zero`** — it already carried
   it. Cardinalities and quantified certificates were its only losses. The row
   overstates it on one axis and is exactly right on the other.
2. **Five sites drop `functions`, which the row never mentions**: `abv.rs:263`,
   `lia.rs:145`, `datatype_native.rs:665`, `nia_linearize.rs:1837`,
   `pbls.rs:1152`. That is the `9b259f7c2` shape, whose caller-visible symptom
   was `Err(UnboundFunction(..))` on replay — louder and more reachable than the
   `real_div_zero` fallback, not quieter. `nia_linearize::replay_sat` drops
   **all four** non-entry components and is the widest loss on the board.
3. **`pbls.rs:1152` has no assertion replay above it at all.** Its acceptance
   test is `total_cost == 0 && all_satisfied()` over the full assignment — a
   replay in substance, and the emitted model was still narrower than it.
4. **The eleven are a sample, not a population.** Deriving the set from the
   source instead of the row: 96 `Model::new()` sites outside `model.rs`, and
   two more with the identical shape sit inside the same functions as listed
   sites — `abv.rs:6633` and `incremental.rs:7637`. Both fixed here. The
   remaining ~80 were not audited by this lane.

### Two fixes, because one of them provably does not work everywhere

The row's own note is correct and was verified by reading
`Model::to_assignment` rather than assumed: it copies `entries`, `functions`
and `real_div_zero` and **nothing else**. So guard 2 — a re-replay through
`to_assignment` — is structurally blind to `uninterpreted_cardinalities` and to
the quantified sat certificates.

At `lazy_bv.rs:323` and `incremental.rs:7616` those two are the *only* remaining
losses. Guard 2 there would have been a check that cannot fail on the defect the
site has. So:

- **`Model::retain_symbols`** for the three sites whose source is another
  `Model`. Narrowing clones and retains, so no component can be lost — including
  components added to `Model` after today. A **carry**, not a **guard**.
- **`Model::carry_assignment_components`** for the ten sites whose source is an
  `Assignment` (which holds exactly three things). One added line per site; no
  surrounding code touched.

The test that makes `retain_symbols` falsifiable is worth naming, because it is
the one piece here that does not rot: it narrows a fully-populated model, puts
the removed entry back, and asserts `PartialEq` **on the whole `Model`**. A
component added to `Model` later is covered the moment the fixture populates it,
rather than requiring someone to remember to extend a list of accessors. Its
control — `the_fixture_populates_every_component_of_model` — exists because a
component silently arriving empty would make that test pass for the wrong
reason, which is exactly the failure this item is about.

### Per-site mutation table (2.11)

Each of the 13 sites reverted alone, `sound2_narrowing` tests re-run, sources
restored byte-for-byte. Method note: the filter measures *"is this site covered
by a per-site test of this family"*, **not** *"is it covered by any test in the
crate"*.

| site | reverted alone |
| --- | --- |
| `lazy_bv::restrict_model` | died (1) |
| `incremental::filter_internal_model` | died (1) |
| `incremental::complete_model_filtered` | died (1) |
| `nia_linearize::replay_sat` | died (1) |
| `pbls::model_from` | died (1) |
| `abv::model_from_projected_assignment` | died (1) |
| `aufbv.rs:139` | **nothing died** |
| `combined.rs:251` | **nothing died** |
| `abv.rs:275` (`project_replay_model`) | **nothing died** |
| `abv.rs:6648` (lazy-ROW) | **nothing died** |
| `lia.rs:158` | **nothing died** |
| `ufbv_online.rs:3183` | **nothing died** |
| `datatype_native.rs:678` | **nothing died** |

**Six of thirteen sites have a test that dies. Seven do not.** Each of the six
kills exactly one test and no two overlap, so the shared helper has not
collapsed the sites into a single check — but seven sites are carries verified
by review and by the helper's own tests, which is weaker, and saying so is the
point of printing the table.

The seven are exactly the sites whose narrowing is inline in a large function
whose inputs cannot be constructed without extracting it — a refactor this lane
was scoped out of, with other lanes live in `abv.rs` and `auto.rs`. **What would
close them**: extract each inline narrowing into a named function of
`(&TermArena, &Assignment) -> Model`, as `abv::model_from_projected_assignment`
and `incremental::complete_model_filtered` already are. That is a mechanical
change and it is what made those two testable at all.

### What is *not* claimed

- Not claimed: that any of the eleven was exploitable. No witness was built for
  any 2.11 site, and none was attempted end-to-end — the row's "structural, not
  currently exploitable" was not re-tested, only the *structure* was.
- Not claimed: that the seven untested sites are unreachable. The measurement
  says no test of this family covers them. That is a statement about the tests,
  not about the routes.
- Not claimed: that the site set is complete. It is 13 of 96 `Model::new()`
  sites in the crate.

---

## One unrelated finding, reported not fixed

With two workers on a disjunctive integer query, a portfolio arm thread panics:

```
thread 'portfolio-arm-lia-dpll' panicked at crates/axeyum-solver/src/lra.rs:2967:
a deadline-free collection cannot time out
```

Pre-existing and unrelated to this lane's changes — it happens inside the arm's
own solve, before any result reaches the guard added here — and the portfolio
catches it, so no test fails. Reproduce with
`IntLinearPortfolioWorkersGuard::set(2)` and
`(= x 3) ∧ ((div x 0) = 5 ∨ (div x 0) = 6)`.

---

## Gates run

`--lib --features full` 1,689 passed (was 1,678; +11 new, 0 failures) ·
`corpus_regression` 2 · `int_divmod_zero_certificate` 8 ·
`nia_divmod_linearize` 13 · `portfolio_fused_group` 8 ·
`abv_lazy_ext` / `abv_lazy_row` / `aufbv` / `combined` / `datatype_native` ·
`qf_lia_differential_fuzz` 4 and `qf_lra_differential_fuzz` 5 under
`--features z3` (nonzero counts confirmed — without the feature both compile to
zero tests and exit 0) · `cargo clippy -p axeyum-solver --all-targets --features
full -- -D warnings` exit 0, read directly rather than through a pipe.

**Not run**: `just check`, `./scripts/check.sh`, the workspace-wide clippy, and
`progress_frontier`. Reported as *did not run*, not inferred from the above.
