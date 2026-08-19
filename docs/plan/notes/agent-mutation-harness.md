# Notes: mutation harness — a mutation check that cannot report what it did not measure

## The defect

`scripts/tests/mutation_controls.py` scored a mutation by "was the run clean?".
Measured 2026-08-18 against the harness as it stood, with three probe mutations
injected into the `fact-derived-numbers` suite:

```
blindspot: baseline green
  A: real guard (should kill)        killed 1: test_guard_unchecked_ceiling
  B: DOES NOT COMPILE                killed 0: see output
  C: cosmetic (should survive)       MUTATION DID NOT APPLY (guard text moved)
```

`B` replaced `if len(unchecked) > ceiling:` with `if len(unchecked) > > ceiling:`.
The subject does not parse, no test ran, and the harness printed **`killed 0`**
and counted the guard as covered — it is not in the survivor list and it does not
affect the exit status. The same is true of a suite that executes zero tests: on
Python ≥ 3.12 `python -m unittest <empty module>` prints `Ran 0 tests`,
`NO TESTS RAN`, and exits **5**, which the old classifier read as a death.

Both failures push in the *unsafe* direction: they manufacture coverage. Every
"exactly one test died" in this repository's history rests on the mutant having
been built and run, and nothing checked either.

## What the harness already did, that the brief assumed it did not

Three of the four "also worth considering" items were already there, and two are
better than what was suggested:

- **Baseline.** It ran the unmutated suite first and refused on `BASELINE IS RED`.
  It did *not* check that the baseline ran a non-zero number of tests, which is
  the same trap one level up; it does now, and it records the count.
- **The mutation actually changed the file.** `if find not in original:` printed
  `MUTATION DID NOT APPLY`. It did not notice an anchor matching in *more than
  one* place, or a `replace` that is a no-op.
- **Restoring the source with a `trap`** is not needed and never was: the subject
  is only ever mutated inside a `TemporaryDirectory` copy, so a killed process
  cannot leave a mutated tree behind. A `trap` on the shared checkout would be
  strictly worse. What was missing is that the restore was *assumed* — it is now
  written and read back (`_restore`).

## What is new

Outcomes are a closed set, and only two of them are measurements:

| outcome | meaning |
| --- | --- |
| `killed N` | built, ran the baseline's tests, N died |
| `SURVIVED` | built, ran the baseline's tests, none died — the guard is not load-bearing |
| `DID NOT BUILD` | the mutation broke the subject |
| `DID NOT RUN` | zero tests, or a *different* number from the baseline |
| `NOT APPLIED` / `AMBIGUOUS ANCHOR` | the anchor is absent, a no-op, or matches twice |
| `INCONSISTENT` | the two independent kill counts, or the exit status, disagree |

Mechanisms:

- **A build probe before any test count is believed.** `py_compile` on every
  mutated file *and* an import of the control module — the second is this route's
  `cargo test --no-run` and catches a load-time failure `py_compile` cannot see.
  Both halves are independently controlled; deleting either kills a test.
- **Two independent kill counts.** The `FAIL:`/`ERROR:` header lines and the
  `FAILED (failures=…, errors=…)` summary are parsed separately and must agree
  with each other *and* with the exit status. Disagreement is `INCONSISTENT`, not
  a number.
- **Collection must not move.** A mutant that runs a different number of tests
  from the baseline changed *collection*, not behaviour, so nothing is comparable.
- **Survivors and unmeasured mutations are counted separately.** "The guard is not
  tested" and "the harness could not tell" are different failures with different
  fixes, and each fails the run on its own (both directions are controlled).
- **A `cargo` runner**, because the reported incident was Rust. `classify_cargo`
  reads `running N tests` / `test result:` blocks, requires one result per started
  binary, and treats exit 75 from `scripts/cargo-serialized.sh` as a missing lock
  slot rather than a verdict.
- **The scratch copy goes to /data0, not /tmp.** /tmp here is a 62 G tmpfs that
  CLAUDE.md measures at 81% full; each suite copies ~430 MB.

## The four outcomes, demonstrated

`python3 scripts/tests/mutation_controls.py self-demo` — four real mutations of
`scripts/tests/fixtures/mutation_demo/`, one per outcome, and it exits non-zero
unless the harness names each correctly:

```
self-demo: baseline green, 2 tests (python3 -m unittest scripts.tests.fixtures.mutation_demo.suite_tests)
  a guard a control drives           killed 1: test_negative_is_refused
  a guard NO control drives          SURVIVED — 2 tests ran, none depend on this guard
  a mutation that breaks the parse   DID NOT BUILD — ... SyntaxError: expected ':'
  a mutation that empties collection DID NOT RUN — the suite built and then executed zero tests
self-demo: 2 mutation(s) NOT MEASURED — these are not results:
    ...
self-demo: 1 guard(s) not covered by any test
self-demo: all 4 outcomes named correctly
```

Two things that cost a cycle each and are worth recording:

- Renaming a `TestCase` **class** does not empty collection — `unittest` collects
  by base class, not by name. Dropping the base does. The demo used the rename
  first and the harness said `SURVIVED`; it was right.
- The fourth mutation targets the *control* module, not the subject, because
  "the suite executed zero tests" is a property of the suite. Mutations may now
  carry a fourth element naming the file they edit.

### The same four, on the cargo route

`DID NOT BUILD`, reproducing the reported incident (a Rust mutation naming a
method that does not exist, the `str::Lines::rposition` shape):

```
_cargo_nobuild: baseline green, 2 tests (scripts/cargo-serialized.sh test -p axeyum-fp --test width_guard)
  a real guard, for contrast         killed 1: fp_ops_on_over_128_bit_format_error_not_panic
  a method that does not exist       DID NOT BUILD — ... error: could not compile `axeyum-fp` (lib) due to 1 previous error
```

`DID NOT RUN`, on the exact command form CLAUDE.md documents as inert — the
`#![cfg(feature = "full")]` trap, caught at the **baseline**, before a single
mutation is attempted:

```
_cargo_norun: BASELINE IS NOT GREEN — DID NOT RUN — the suite built and then executed zero tests
```

(the runner there is `cargo test -p axeyum-solver --test corpus_regression`,
without `--features full`.)

## The harness, mutation-checked against itself

`python3 scripts/tests/mutation_controls.py mutation-controls` — 24 guards, 31
controls, ~90 s. **First run: 21 killed, 3 SURVIVED.** The three were real:

- the restore was written but never verified;
- an unmeasured mutation alone did not fail the run;
- a survivor alone did not fail the run.

All three are now driven by a control (`_restore` against a symlink to
`/dev/null`, which accepts every write and reads back empty; and two end-to-end
runs of one-mutation suites). Second run: **24 of 24 killed, exit 0.**

Three guards kill more than one control, deliberately and visibly:
`zero tests is not a result` (2) and `a changed test count` share
`_collection_report` between the unittest and cargo routes;
`the import half of the build probe` (2) is driven by a unit control and by the
baseline-build control; `the subject is restored between mutations` (5) is what
every end-to-end control depends on. Duplicating logic to make each number 1
would be the wrong fix.

The self-suite's table lives in `scripts/tests/mutation_controls_self.py`, not in
the file it mutates: an anchor stored beside the guard it names occurs **twice**,
and the harness refuses that (`AMBIGUOUS ANCHOR`). Fifteen of the twenty-four
were in exactly that state when they were first written in one file.

## Two dead controls found in `lra-hypothesis-binding`

The new `AMBIGUOUS ANCHOR` check found both on its first run over the existing
suites — both carrying a comment claiming the find-string had been disambiguated
by trailing context, which it had not:

- `attestation: no axiom beyond the opaque sort` matched **two** of the three
  copies of that guard and so mutated `bind_anchored` — the *same copy* the
  `anchor: no axiom beyond the opaque sort` control already drove, leaving
  `classify_attestation`'s copy untested under a label that said otherwise.
  Re-anchored on the message text; it now kills
  `test_an_extra_axiom_takes_it_out_of_the_class`.
- `structural: a declared constant no rendered term uses is refused` matched two
  copies. It happened to hit the right one (first in file order), but nothing
  said so. Re-anchored on the three preceding lines; unchanged behaviour.

With both repaired the suite is **53/53 killed, exit 0**.

### An uncovered guard, reported not fixed

While disambiguating the above, the third copy of the opaque-sort guard — the one
in **`bind_structural`** (`check-lra-hypothesis-binding.py:1244`, the single-line
`return (False, …)` form) — was measured and **SURVIVES**: no test in
`test_check_lra_hypothesis_binding.py` depends on it. Reproduce with a two-line
probe suite anchoring on

```
            if (name, ty) != ATTESTATION_SORT_AXIOM:
                return (False, f"`{name} : {ty}` is not the opaque sort `α : Sort (1)`", 0)
```

This is the `102-attestation-gap` lane's checker and its control module, so it is
left for that lane rather than edited from here; registering the mutation without
a control would simply red their gate.

## Also measured, not caused here

- `adr-index`'s baseline is red on this checkout:
  `test_same_number_different_content_is_a_collision` asserts `'0468'` and the
  tree now yields `'0483'`. Reproduces outside the harness. The harness refuses to
  report a mutation result against it, which is the point.
- `plan`'s baseline is red *in the scratch copy* whenever any lane has an
  uncommitted `docs/plan/status/` edit that `PLAN.md` does not yet reflect —
  `test_committed_plan_is_exactly_what_the_generator_produces` compares the two.
  It passed in the live tree minutes earlier in the same session. Regenerate
  before running that suite.
