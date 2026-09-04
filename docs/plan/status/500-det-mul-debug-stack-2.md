# Lane: det-mul-debug-stack-2 — the second same-day debug stack overflow the first fix hid, plus its class

<!-- plan-section: lane-status -->

**DONE, det-mul-debug-stack-2, 2026-09-03.** Yesterday's `det-mul-debug-stack`
lane fixed one push-blocking DEBUG stack overflow in `rat_prelude::det_mul_-
tests` and pinned `rat`'s debug envelope row at EXACTLY 2,097,152 -- the 2 MiB
a `#[test]` thread gets by default -- warning that "the next `rat` declaration
of any depth will abort something and will name only the first casualty."
Lane `tactic-list-int` found that casualty the SAME DAY:
`rat_prelude::det_mul_tests::mat_subst_rows_replaces_the_window_by_relative_-
index`, never run before because the first lane's abort had hidden it. Fixed,
then swept the WHOLE `rat_prelude::` filter (265 tests) at the default debug
stack and found THREE MORE aborting tests nobody had seen, plus a FIFTH,
unrelated one (`complex`, not `rat`) surfaced only by the full push-gate run.
All five fixed the same way; `scripts/check-kernel-suites.sh` now exits 0.
`e651052f5` (the four `rat_prelude` fixes), `9b5041a89` (the `complex`
fix), `c21185c6a` (the envelope re-pins).

**The requirement, before/after, for the assigned test.** Measured from
outside the process (an abort cannot be observed in-process): aborts at
2,097,152, checkpointed with `eprintln!` -- the overflow happens INSIDE
`built()`, before the test body's own work even starts. Passes at 4,194,304
and every larger power of two tried. **The cliff is not a numeral.** Every
magnitude `mat_subst_rows_replaces_the_window_by_relative_index` forms is a
single digit (its own doc comment says so). The cliff is the test's OWN bulk:
many locals across the main loop, three negative controls, the empty-window
loop and the one-row-window check all stay live for the whole unoptimized
function body, sitting on top of a `rat` prelude build that already consumes
the full 2,097,152 default with zero margin. Fixed by the second documented
remedy (shrinking magnitudes does not apply -- there is no magnitude to
shrink): split into a `_body` function and run it on `crate::on_a_deep_stack`,
matching the pattern the first lane used for the two `det_mul_tests` it fixed.

**The class: the WHOLE `rat_prelude::` filter, run at the default debug
stack, found three MORE aborting tests.** An overflow aborts the whole
process, so a single `cargo test` run only ever names the FIRST casualty; the
only way to find the rest is to keep skipping the named one and re-running.
Did that three times (single-threaded to get a clean per-test trace, then
threads=4 once the trace confirmed the mechanism, to go faster) until the
full 265-test filter passed twice in a row with the fixes applied:

| test | file | cliff (`RUST_MIN_STACK`) |
| --- | --- | ---: |
| `mat_subst_rows_replaces_the_window_by_relative_index` | `det_mul_tests.rs` | aborts 2,097,152, passes 4,194,304 |
| `echelon_tests::the_row_operations_invert_at_concrete_arguments` | `echelon_tests.rs` | aborts 2,097,152, passes 4,194,304 |
| `rank_tests::rank_is_invariant_under_each_row_operation_at_two_by_two` | `rank_tests.rs` | aborts 2,097,152, passes 4,194,304 |
| `rat_prelude_tests::det_transpose_and_the_column_expansion_evaluate_and_pin_the_sign` | `rat_prelude_tests.rs` | aborts 2,097,152, passes 4,194,304 |

All four share the same shape: a single-digit-magnitude test with several
blocks (row operations, negative controls, boundary cases) whose locals all
stay live for the whole unoptimized function body, on top of the zero-margin
`rat` prelude build. All four fixed identically: split into a `_body`
function, run on `crate::on_a_deep_stack`. None had its assertions weakened;
none lost a negative control. The full 265-test `rat_prelude::` filter then
passed twice at the default 2,097,152 with zero aborts and zero failures
(one single-threaded run, 868.01 s; one four-threaded run, 803.54 s, this one
covering the previously-skipped two as well).

**A fifth casualty, outside `rat`, found only by the required push-gate
run.** `scripts/check-kernel-suites.sh` (`AXEYUM_CARGO=scripts/cargo-serial-
ized.sh`) runs `cargo test -p axeyum-lean-kernel --lib` in ONE process
alongside every non-Lean integration suite -- the actual push form, not a
`rat_prelude::`-filtered one. That run aborted on
`complex::algebra_instance::algebra_instance_tests::complex_comm_ring_s_-
admits`: `complex`'s debug envelope row is 16,777,216 (8x the default), and
every one of the six tests in that module calls `build_complex_prelude`
directly on the default `#[test]` thread with no `on_a_deep_stack`. This one
had NOT been seen before because `prelude_cache` (ADR-0464, process-wide,
in-memory) can make it look free when some OTHER test warms the cache first
in the same run -- so which test (if any) hits the cold build is an accident
of scheduling, and the crash names only whichever one loses that race. All
six tests in `complex/algebra_instance.rs` now run on `on_a_deep_stack`, not
only the one that happened to abort this run, so none of the six depends on
cache-warming luck. This is outside the `rat_prelude` scope this lane was
given, but the brief's required gate (`check-kernel-suites.sh` exit 0)
cannot be met without it, the fix is the identical, already-validated
remedy, and the file is not on the excluded list (`structures_setoid.rs`,
`creal/`, `linarith/generic.rs`). Verified in isolation: all six tests in
`complex::algebra_instance::algebra_instance_tests::` pass at the default
stack, 179.20 s. **This is very likely not the last such casualty outside
`rat`** -- any module that calls `build_complex_prelude` or a similarly
zero-to-low-margin prelude builder directly, without `on_a_deep_stack`, is a
latent, scheduling-dependent abort. A later lane should treat this as a
DISCOVERED SHAPE ("`#[test]` builds a deep prelude directly, no
`on_a_deep_stack`, module's tests never all run in one process before"), not
as "the `complex` algebra_instance file, now closed."

**Envelope re-pins, both profiles, `--check` then `--measure` on what went
red.** `rat`'s debug row was already re-pinned yesterday and stayed exactly
at 2,097,152 (unchanged, still zero margin -- confirmed by `--check`:
"builds at 2097152, aborts at 1048576"). Running the FULL `--check` in both
profiles (not just `rat`) found two more red rows, both re-derived by
`--measure` (so neither is a divergent term):

| profile | prelude | was | now |
| --- | --- | ---: | ---: |
| debug | `nat` | 262,144 | 524,288 |
| release | `rat` | 262,144 | 524,288 |

`--check --profile release` (6/6 ok) and `--check --profile debug` (9/9 ok)
both exit 0 after the re-pin. `artifacts/kernel-stack-envelope.tsv` carries a
new dated entry recording both the four-plus-one aborting tests and this
growth; see the file for the full note.

**The guard: proposed, NOT implemented, and why.** The brief asked for "a
test in `rat_prelude` that asserts the debug requirement stays at least one
power of two BELOW the thread default." That cannot be built as a currently-
green `#[test]`: `rat`'s ACTUAL debug requirement is 2,097,152, exactly equal
to the default, not below it -- shrinking that would mean reducing the `rat`
prelude's real build cost, a much larger, out-of-scope undertaking, not a
test-only change. Worse, the only mechanism available INSIDE a `#[test]`
(spawning a thread of a chosen size and checking whether it succeeds) cannot
observe failure cleanly: a stack overflow calls `process::abort()` for the
WHOLE BINARY regardless of which thread hit it, so a guard built this way
would reproduce the exact defect this lane fixes rather than catching it --
one more test the abort silently prevents from ever reporting red. The only
way to observe a stack overflow is from OUTSIDE the process, which is
exactly what `scripts/check-kernel-stack-envelope.sh` already does via a
separate subprocess (`examples/kernel_stack_envelope`). The gap it names
("nobody runs `--check`") is real and repeats (this is the SECOND time in
two days a red `--check` sat undiscovered), but the fix is operational --
wire `--check --profile debug` (or at least `--prelude rat`, ~1 s once the
probe binary is built) into `check-kernel-suites.sh` or `hooks/pre-push` so
a regression is caught by a named, run-every-time step -- not a new
in-process `#[test]` that cannot safely detect the condition it exists to
catch. Not implemented here because it touches the push-gate scripts
themselves, a larger, riskier change than this lane's five-test fix; flagged
for the next lane or the coordinator.

**Verification.**

| check | result |
| --- | --- |
| `rat_prelude::` DEBUG, `--test-threads=1`, single test, before fix | SIGABRT (signal 6) |
| `rat_prelude::` DEBUG, full filter (265 tests), `--test-threads=1` then `=4` | ok both times, 0 failed, 0 aborts |
| `complex::algebra_instance::algebra_instance_tests::` DEBUG, all 6 | ok, 0 failed, 179.20 s |
| `scripts/check-kernel-stack-envelope.sh --check --profile release` | exit 0, 6/6 ok |
| `scripts/check-kernel-stack-envelope.sh --check --profile debug` | exit 0, 9/9 ok |
| `scripts/check-kernel-suites.sh` (`AXEYUM_CARGO=scripts/cargo-serialized.sh`, `AXEYUM_CARGO_MEM=64G`) | **exit 0** -- 32 suites + `--lib`, 2,027 tests, every one `ok`, none FAILED, none INERT |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | clean |
| `rustfmt --edition 2024 --check` on every touched file | clean |
| projection (`kernel_declaration_projection`) | untouched by construction -- every changed line sits inside a `#[cfg(test)] mod ..._tests;` (confirmed for all five files); a test-only diff cannot move a projection built from non-test code |

**Two things a later lane should know, stated as precisely as the
positives.**

- **`AXEYUM_CARGO_MEM`, not `MEM_LIMIT_GB`, is what `scripts/cargo-serial-
  ized.sh` reads** (default `24G`). The first `check-kernel-suites.sh` run
  here, without an explicit override, reported the `--lib` target as failed
  with NO test-failure detail at all in the captured tail -- consistent with,
  though not confirmed as, the 24G default being tight for one process
  building `rat`/`creal`/`cpoint`/`complex` preludes concurrently across
  ~1,834 lib tests. Re-running with `AXEYUM_CARGO_MEM=64G` surfaced the real,
  reproducible defect (the `complex` abort above) with full detail. Whether
  the plain 24G run was ALSO hitting that same `complex` abort (order-
  dependent) or something memory-related is unresolved; recorded as an open
  question, not asserted as fact either way.
- **`check-kernel-suites.sh`'s per-suite table marks EVERY suite "(group
  FAILED)" when the shared `cargo test` invocation's overall exit is
  nonzero, even suites that individually printed "ok".** Read the script's
  own `printf '%s\n' "$out" | tail -60` for the actual failure -- and if the
  failure is in `--lib` (1,834 tests) and the tail-60 does not reach it (as
  happened here), re-run `cargo test -p axeyum-lean-kernel --lib` alone,
  captured to a file, rather than trusting the table.

<!-- plan-section: landed-changes -->

| 2026-09-03 | det-mul-debug-stack-2 | Fixed the push-blocking DEBUG stack overflow in `rat_prelude::det_mul_tests::mat_subst_rows_replaces_the_window_by_relative_index` (the casualty yesterday's `det-mul-debug-stack` fix hid) by splitting it into a `_body` fn run on `crate::on_a_deep_stack`, same remedy as yesterday -- no magnitude to shrink here, every value formed is a single digit. Then swept the whole `rat_prelude::` filter (265 tests) at the default debug stack and found three MORE aborting tests the same way: `echelon_tests::the_row_operations_invert_at_concrete_arguments`, `rank_tests::rank_is_invariant_under_each_row_operation_at_two_by_two`, `rat_prelude_tests::det_transpose_and_the_column_expansion_evaluate_and_pin_the_sign`; all fixed identically, all measured aborting at 2,097,152 and passing at 4,194,304. No assertion weakened, no negative control removed. |
| 2026-09-03 | det-mul-debug-stack-2 | The required push-gate run (`scripts/check-kernel-suites.sh` with `AXEYUM_CARGO=scripts/cargo-serialized.sh`) surfaced a FIFTH, unrelated casualty outside `rat`: `complex::algebra_instance::algebra_instance_tests::complex_comm_ring_s_admits`, which calls `build_complex_prelude` (debug row 16,777,216, 8x default) directly on the default `#[test]` thread. Not previously seen because `prelude_cache` (ADR-0464) can hide it when another test warms the cache first -- a scheduling accident, not a fix. All six tests in that module now run on `on_a_deep_stack`, not only the one that aborted this run. `scripts/check-kernel-suites.sh` now exits 0: 32 suites + `--lib`, 2,027 tests, all `ok`. |
| 2026-09-03 | det-mul-debug-stack-2 | Re-ran `scripts/check-kernel-stack-envelope.sh --check` in BOTH profiles (not just `rat`) after the fixes; found and re-derived two more red rows by `--measure`: debug `nat` 262,144 -> 524,288, release `rat` 262,144 -> 524,288 (`rat` debug unchanged at 2,097,152, still zero margin). Both `--check` runs now exit 0 (6/6 release, 9/9 debug). Considered and did NOT implement the requested in-process guard for the zero-margin `rat` debug row: a stack overflow aborts the WHOLE PROCESS regardless of which thread hit it, so a `#[test]` that tries to demonstrate the margin by spawning an undersized thread reproduces the exact defect this lane fixes instead of catching it cleanly; recommended wiring `--check --profile debug` into the push gate instead, as an operational (not test-code) follow-up. |
