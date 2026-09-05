# Measurement Hazards — tools that lie

Tools in this repository have lied more often than the solver has been weak. Each
entry below is a command that exited 0 and printed something plausible that was
wrong, and was then reported as fact.

The rule underneath all of them, and the one to apply to any command not listed:
**before believing a result, ask what the command would print if it were broken.
If that is what it just printed, it is not evidence.**

Two structural traps recur and are worth naming up front:

- **A green-looking gate that ran zero tests.** A feature-gated suite compiles to
  an empty binary without its flag, prints `running 0 tests ... ok`, and exits 0.
  Always confirm a NONZERO test count. See the pre-merge gate list in
  [CLAUDE.md](../../CLAUDE.md#commands).
- **A correct empty answer to a question you did not ask.** The tool runs, exits
  0, and reports honestly about a subject that is not yours. Before believing a
  zero, confirm the tool's COVERAGE includes your subject, and pair every
  negative with a positive control **of the same kind** — a theorem is not a
  control for a definition.

## `explain_corpus` is not an oracle

**`explain_corpus` IS NOT AN ORACLE, and it now says so in every line it
prints.** It calls `check_auto_explained` on the *flat* view; the shipped
front door is `solve_smtlib`, which adds the ADR-0052 `StringGate`, the word
/ online / membership routes, and the multi-`check-sat` lifecycle. Measured
2026-08-21 over 397 committed benchmarks, the two disagree on **134** — 71
where this tool ERRORS and the front door decides, 46 bounded-string
refusals (the front door decides three of those `sat`), 17 where it says
unknown and the front door decides.

This entry used to say "it prints `unsat` for `regex-032-…-fuzz`, which is
genuinely `sat`", and a doc line did not stop a whole lever being built on a
fabricated verdict. So the output changed instead: every verdict is prefixed
(`flat-unsat`, `front-door-sat`, `not-attempted`) and **nothing it emits can
be `grep -x`'d as an SMT-LIB answer**; the two structurally divergent shapes
— a multi-`check-sat` script, and a bounded-string `unsat` — are refused with
a reason instead of answered; and every JSONL record carries
`"oracle":false`. Pass `--confirm` to have it re-solve each file through the
real front door and stamp `front_door_verdict` / `agrees`.

Do NOT measure that divergence by diffing against `smtcomp_cli`: SMT-COMP
§7.1.2 makes the CLI print `unknown` for an error, so 59 both-sides-decline
files read as disagreements and the count comes out 193 instead of 134.
`--confirm` compares in-process, which is the difference.

## A test that passes only under an ambient environment variable

**A TEST THAT PASSES ONLY UNDER AN AMBIENT ENVIRONMENT VARIABLE IS A GATE ON
ONE SHELL, AND THE LANE THAT ADDS IT CANNOT SEE THE PROBLEM.** Measured
2026-08-26. A lane added a concrete-instantiation test for
`riemann_sum_reblock_close`, ran `cargo test --lib creal::`, got **93 passed,
0 failed**, and reported -- accurately, from where it stood -- that no
deep-stack wrapper was needed for this step. In a clean shell the same test
SIGABRTs: `has overflowed its stack`, `signal: 6`.

The cause is that the lane had `RUST_MIN_STACK` **exported earlier in its own
run**, while hand-bisecting the stack requirement of the PREVIOUS step's test.
Every later command in that shell inherited it. Real measurement, false
conclusion, and nothing in the output hints at the dependency.

Two rules follow, and the second is the one that generalizes:

- A test needing a deep stack must **carry it explicitly** -- an
  `on_a_deep_stack` wrapper spawning a 256 MiB thread (the pattern in
  `creal_point_tests.rs`, `creal/integral.rs`) -- never rely on the ambient
  `RUST_MIN_STACK`.
- **Verify with `env -u <VAR>` for any variable you have set by hand this
  session.** A coordinator re-running the lane's command in the coordinator's
  own shell reproduces the lane's contamination whenever both shells set the
  same thing. `env -u RUST_MIN_STACK cargo test ...` is what distinguished
  them here.

Note the interaction with the entry below: a stack overflow in this kernel
looks exactly like a broken tool or an absent declaration (`exit 134`,
SIGABRT), which is why `prelude_theorem_inventory` must be run `--release`.
The same symptom, two unrelated causes, and neither one is a proof bug.


## Banned shell idioms

**BANNED SHELL IDIOMS. Every one of these has printed a WRONG ANSWER that was
then reported as fact, and none of them look broken when they fail.** The
shared failure mode: the command exits 0 and prints something plausible.

1. **`echo "exit=$?"` after a pipeline.** `$?` is the LAST stage. Measured
   2026-08-20: `python3 scripts/create-autogenesis-nursery-dispatch-baseline.py
   --check 2>&1 | tail -12; echo "exit=$?"` printed `exit=0` for a script that
   exits **1** — `tail`'s status. Run the command bare, or use
   `${PIPESTATUS[0]}`, or `set -o pipefail`.
2. **`grep -q` as a pipeline consumer under `set -o pipefail`.** `-q` exits at
   the first match and SIGPIPEs the producer, so the pipeline status is 141 —
   which `pipefail` turns into "not found". Measured 2026-08-20 in
   `scripts/check-control-registration.sh`: the same unchanged tree reported
   **7 orphans on one run and 3 on the next**, because whether the producer
   finished writing first depends on buffering. Use `grep -c` and test the
   count; it consumes all input and cannot SIGPIPE.
3. **`grep -B1`/`-A1` to pair a commit subject with its trailer.** With
   `--format=%b` the line before a trailer is BLANK. Measured 2026-08-20:
   reported **1 commit when there were 21**. Use
   `git log --format='%H|%s|%(trailers:key=Agent,valueonly)'`.
4. **Testing a grep PATTERN interactively and trusting it in a script.** On
   this host `grep` is a shell FUNCTION wrapping `ugrep 7.5.0` in an
   interactive shell, and plain `/usr/bin/grep` (GNU grep 3.12) everywhere
   else. They disagree on `\t`: ugrep reads it as a tab in ERE, GNU grep
   reads it as a literal `t`. Measured 2026-08-25, each with its control:

       printf 'a\tb\n' | /usr/bin/grep -cE 'a\tb'   -> 0   # a real tab: NO match
       printf 'atb\n'  | /usr/bin/grep -cE 'a\tb'   -> 1   # literal 't': matches

   **54 facts / 68 `checker_command`s matched the inventory's tab-separated
   output with `\t`**, so each reported a theorem that EXISTS as absent from
   any script or CI run, while passing when a human ran it by hand. It is
   fail-closed, so flakiness rather than unsoundness -- but the evidence
   re-derived nowhere except one interactive shell. Use `[[:space:]]`, and
   **test every pattern with `/usr/bin/grep` explicitly**. `command -v grep`
   prints `/usr/bin/grep` under `bash -c` and `grep is a function`
   interactively, which is the fastest way to tell which one you have.

5. **Reporting an empty `grep` as a negative result.** An empty answer and a
   wrong query are the same observation. This is the grep-shaped case of the
   coverage trap below; pair the negative with a positive control that MUST
   produce output, in the same command.
6. **Fixed-name files in the session scratchpad.** It is per-SESSION, shared by
   every lane (see the multi-agent section). `push.log`, `reg.log`, `audit.log`
   collide; prefix with `$AXEYUM_AGENT`.
7. **A "did it finish?" check that has never been shown to fire.** Measured
   2026-08-20: an end-marker sweep reported `!! NO END MARKER` for two jobs
   that had completed normally — the scripts had never written markers. The
   check was wrong, not the job, and the natural reading was the opposite.

The rule underneath all seven, and the one to apply to any command not on this
list: **before believing a result, ask what the command would print if it were
broken.** If that is what it just printed, it is not evidence.


## A hand-rolled Python mutation loop reports the previous mutant

**A HAND-ROLLED MUTATION LOOP OVER A PYTHON FILE REPORTS THE PREVIOUS MUTANT'S
RESULT.** Python caches compiled modules on `(source mtime in whole SECONDS,
source size in bytes)`. Mutation testing produces equal-size mutants **by
construction** — one fixed string replaced by another fixed string at
different sites — written back to back, well inside one second. So the cache
is not a corner case here; it is the default.

Measured 2026-08-20: three copies of one guard in
`check-lra-hypothesis-binding.py` (`bind_structural`, `bind_anchored`,
`classify_attestation`, all 138,581 bytes when mutated) each reported killing
the *same* test — `AStructuralModule…`. Clearing `__pycache__` between
iterations, each kills its own distinct control, correctly named. The loop was
restoring and re-mutating exactly as intended; only the bytecode was stale, and
`git diff` confirmed the right line changed every time, which is what made the
wrong answer so convincing.

Both directions occur. If the BASELINE is cached, a real kill reports
`SURVIVED` — you go hunting a gap that does not exist. If a KILLED mutant is
cached, a mutation that changes nothing reports `KILLED` — coverage that was
never measured, which is the failure this repository cares most about.

`scripts/tests/mutation_controls.py` is **not** vulnerable: its `Unittest.build`
runs `py_compile` on every target, which rewrites the cache entry. That step
was written to catch a subject that does not parse; its second job is invisible
from its own code. It is now pinned by `StaleBytecodeTests` and by a self-table
entry that keeps the syntax check and drops only the recompile. Use the
harness. If you must loop by hand, `find . -name __pycache__ -exec rm -rf {} +`
between iterations, and never trust two mutants that report the same dead test.

## A background task reported as exited may still be running

**A BACKGROUND TASK REPORTED AS EXITED MAY STILL BE RUNNING, AND IT WILL TAX
EVERY MEASUREMENT YOU TAKE AFTERWARDS.** Found 2026-08-21: a `python3 -` from
a session task started **2026-08-18 03:43**, whose output file recorded
`[exited with code 144]` at 03:49, was still at **99.5% CPU 85 hours later** —
orphaned to `systemd`, parent shell long dead, nothing reading its stdout. The
harness had closed the book on it; the kernel had not.

Cost: a full core of a 16-core box, continuously, for three and a half days.
Reaping it took load from **9.27 to 3.44**. Every wall-clock measurement on
this host in that window — the `progress_frontier` reference frames, the
timing in two capability diagnoses, the competition sweeps — ran ~6% short on
capacity, and some of the ratchet's `NOT COMPARABLE` / `ADVISORY ONLY`
markings were firing partly because of a ghost. Verdict counts are unaffected
(a decided file is decided); anything timing-shaped is not.

So before trusting a load-sensitive number, look for orphans, not just for
your own jobs:

    ps -eo pid,ppid,etimes,pcpu,args --sort=-pcpu --no-headers \
      | awk '$2==1 && $4>50'      # reparented to init AND burning CPU

Kill by **PID**, never `pkill -f <pattern>` — that pattern matches the killing
shell's own command line, and a lane killed its own ratchet launcher that way
the same day. `/proc/<pid>/fd` tells you what a mystery process is writing to,
which is how this one was identified as a session task rather than a user's
job.


## `command -v lean` returns nothing on a host that has Lean

**`command -v lean` RETURNS NOTHING ON A HOST THAT HAS LEAN, and an agent has
already reported a whole capability as impossible because of it.** `elan`
installs toolchains under `~/.elan/toolchains/*/bin/lean` and does **not** put
them on `PATH`. `scripts/check-lean-gate.sh` exists to document exactly this and
resolves the pinned toolchain properly — `scripts/check-lean-gate.sh
--print-toolchain`, or `AXEYUM_LEAN_BIN` to override.

Measured 2026-08-22: `command -v lean` empty on s4, while
`~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean --version` reports
4.30.0 at the pinned commit `d024af09`. A Sonnet lane holding a working
three-fact producer concluded from the empty `command -v` that authoritative
admission "requires a toolchain this environment doesn't have" and declined to
register. Nothing was wrong except the probe.

**The Mathlib and lean4export checkouts are a separate question from whether
Lean is installed**, and neither is answered by `command -v`. As of
2026-08-22 they existed **on s5 only** —
`/home/mjbommar/lean-import-scale/{mathlib4,lean4export}`, reachable by
`ssh s5` with BatchMode, both at exactly the commits the adapter manifests
pin (`c5ea0035…`, `a3e35a58…`), with s2/s6/s7 having neither.

**THAT IS NO LONGER TRUE, AND READING IT AS CURRENT COSTS A THIRD OF A
LANE'S BUDGET.** Measured 2026-08-28: a lane sized the Lean route as
impossible here on exactly this paragraph plus an empty `command -v lean`,
then found **s4 can run the entire import route**.
`scripts/provision-lean-import-toolchain.sh` provisions it in ~5 minutes —
pinned, idempotent, and `--verify` needs no network. A blobless mathlib4 at
the pinned commit is 92 MB and the olean cache is already in
`~/.cache/mathlib`; `lean4export` builds in under a minute. Verified by the
coordinator at `/data0/axeyum/lean-import-toolchain`:

    LEAN_IMPORT_TOOLCHAIN|mathlib=c5ea0035…|lean4export=a3e35a58…|
                          lean=d024af09…|verdict=PASS

So: **run `scripts/provision-lean-import-toolchain.sh --verify` before
concluding a host cannot do Lean work.** Host-capability prose in this file
is a snapshot of the day it was written, and this entry is the second one to
go stale in the direction that says "impossible" about something cheap.


## `cargo test --lib 'filterA filterB'` runs zero tests and exits 0

**`cargo test --lib 'filterA filterB'` RUNS ZERO TESTS AND EXITS 0.** The
second word is parsed as a positional the harness does not use, so nothing
matches. Same green-looking nothing as the feature-gated-suite trap, from a
quoting slip rather than a missing flag. **Confirm a NONZERO count**, always.


## Tools here have lied more often than the solver has been weak

**Tools in this repo have lied more often than the solver has been weak.**
In one session: a corpus gate that ran zero tests for 15 days while exiting 0;
a pre-push hook that had never run because `core.hooksPath` was unset; a
`DIRTY WORKTREE` stamp that fired on the harness's own side effects; a
reference-solver smoke probe blind to a 1000× budget-unit error; an error
message naming a node cap when the real cause was an i128 overflow; and a doc
comment claiming a witness binds "every declared String variable" when it
binds the source problem's private symbol ids. Prefer a measurement over a
message, an exit status, or a comment — including the ones you just wrote.

## An empty result from a tool never pointed at your subject

**An empty result from a tool that was never pointed at your subject is
indistinguishable from a strong negative result.** Distinct from the inert-gate
trap above: the tool runs, exits 0, and prints a correct empty answer to a
question you did not ask. `prelude_axiom_inventory` builds the `real`,
`integer` and `string` preludes and never `nat` or `logic`, so grepping its
output for Nat rows returns nothing — which the coordinator read as "the Nat
prelude is axiom-free" and put into two agent briefs before checking. The
conclusion happened to be true; the evidence for it did not exist. Before
believing a zero, confirm the tool's COVERAGE includes your subject, not just
that it ran. (`nat_axiom_inventory` now covers `nat`/`logic` and the full
trusted surface — `Axiom` alone is not it, since `Opaque` has no proof body and
`Quotient` admits `Quot.sound`.)

## `prelude_theorem_inventory` must be run `--release`

**`prelude_theorem_inventory` MUST BE RUN `--release`. In debug it SIGABRTs,
and that looks like a broken tool or an absent subject.** This is the
repository's primary instrument for reading theorem counts and axiom
footprints, so agents reach for it constantly. Measured 2026-08-24 on the same
tree, same flags, same moment:

    cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory \
      -- --include-constructed   ->  exit 0, 3,924 rows
    cargo run           -p axeyum-lean-kernel --example prelude_theorem_inventory \
      -- --include-constructed   ->  exit 134, "has overflowed its stack"

Building the full constructed environment recurses deeply through
`Kernel::add_declaration`, and the debug build's larger stack frames blow the
default thread stack. **Nothing is wrong with the kernel or with any term** —
it is a resource limit wearing a crash's clothes, the same one that makes
`complex_tests.rs` and `creal_point_tests.rs` carry `on_a_deep_stack` helpers.

A lane hit this and reported the inventory as "stack-overflows unrelated to
this work", which is a reasonable reading and a wrong one: it had simply
omitted `--release`. The failure mode that matters is the quieter one — an
agent runs the debug form, gets no rows, and concludes a declaration is
ABSENT. That is the coverage trap below, with the tool broken rather than
misaimed.


## Two inventory tools silently discard all but one name argument

**TWO INVENTORY TOOLS SILENTLY DISCARD ALL BUT ONE NAME ARGUMENT, AND THEY
KEEP OPPOSITE ENDS — so there is no rule to remember, only a habit: pass ONE
NAME PER INVOCATION.** `theorem_dependency_inventory` keeps the FIRST;
`nat_theorem_inventory` keeps the **LAST**. Measured 2026-08-30, both orders:

    nat_theorem_inventory -- totient_mul_of_coprime dist_comm
      -> 1 row: Nat.dist_comm
    nat_theorem_inventory -- dist_comm totient_mul_of_coprime
      -> 1 row: Nat.totient_mul_of_coprime

Exit 0 either way, one plausible row either way. A lane hit this while
checking several new declarations at once and reported the sweep as clean.


## `theorem_dependency_inventory` consumes only its first name argument

**`theorem_dependency_inventory` CONSUMES ONLY ITS FIRST NAME ARGUMENT AND
SILENTLY IGNORES THE REST — a three-name call reads as success.** Measured
2026-08-29 while checking seven new declarations at once. The run printed one
row and the summary line

    1 theorems, 1 with dependencies, 1 edges

which looks like a clean result rather than a tool that discarded six of the
seven names it was handed. Exit 0 either way. This is the
checker-that-cannot-fail defect in its quietest form: the output is not empty,
not an error, and not obviously about the wrong subject.

For a MULTI-declaration check use `prelude_theorem_inventory` with a **tested
count**, and anchor the match on the prelude column — `complex` and `cpoint`
re-declare every `CReal` name, so an unanchored `grep -c` over a `CReal.*`
pattern comes out **3x** and a count-based guard passes for the wrong reason.


## `prelude_theorem_inventory` lists theorems, NOT definitions

**`prelude_theorem_inventory` LISTS THEOREMS, NOT DEFINITIONS — so `Nat.add`
returns ZERO ROWS, and every construction this project is proudest of is
invisible to it.** Measured 2026-08-27 on one inventory of 5,130 rows, each
name matched against the whole row's second field rather than by substring:

    Nat.add  Nat.mul  Rat.polyEval  CReal.integral  CReal.e  CReal.sqrt
    Complex.conj                                        -> 0 rows EACH
    Nat.add_comm 6,  CReal.integral_const 3,  Rat.sub_mul 4   (control)

Every one of those zeros is a `Definition` that certainly exists. The tool
filters to `Declaration::Theorem`, which is correct for what it was built for
and catastrophic for the question agents actually ask it: *does `X` exist?*

**The prefix grep is what makes it dangerous, because it answers NONZERO.**
`grep -c 'Rat.polyEval'` returns **16** — every hit a `Rat.polyEval_add` /
`_smul` / `_succ` lemma, and not one of them the definition. So the careless
query confirms presence, and the careful anchored query reports absence, and
**both are wrong about the definition itself.** It bit in both directions
within one hour: a lane recorded that no in-tree tool inventories definitions
by name with fail-on-absence semantics (true, and it had to weaken a fact
ledger checker because of it), and separately a coordinator grep for `Nat.max`
came back empty and proved nothing at all, because the control — `Nat.add` —
came back empty too.

This is the coverage trap above with the tool **correctly aimed and answering
a narrower question than the one asked**, which is why the usual remedy
("confirm the tool covers your subject") is not enough on its own. Two rules:

- **Pair every negative with a positive control of the SAME DECLARATION KIND.**
  A theorem is not a control for a definition. `Nat.add` returning zero is the
  fastest way to tell you are asking this tool the wrong question.
- **To ask whether a definition exists, read the environment** —
  `kernel.environment().iter()` — or the source, never a theorem inventory.

Related and load-bearing: a fact-ledger `checker_command` asserting a
CONSTRUCTION (`CReal.integral`, `CReal.e`) cannot use the theorem inventory as
its discriminator; it must either name a theorem whose admission entails the
definition, and say so, or use a checker that fails on absence for the kind it
is actually checking.


## Profiling

**No profiling recipe existed anywhere in this repository before
2026-09-05** — nothing in `scripts/`, the `justfile`, or this guide invoked
`perf`, `samply`, `flamegraph`, `dhat`, or `heaptrack`
([2026-09-05 performance review](../research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
§2.2 item 5). `just profile-samply <path.smt2>` and
`just profile-perf <path.smt2>` close that gap: both build
`target/release/examples/smtcomp_cli` and profile one solve of the given
SMT-LIB file, writing output under `bench-results/local/profiles/`
(gitignored — see `/bench-results/local/` in `.gitignore`, so a profile is
never accidentally committed).

- `just profile-samply <smt2>` runs `samply record --save-only` and saves a
  `.json.gz` you open later with `samply load <file>`.
- `just profile-perf <smt2>` runs `perf record -g` and saves `.perf.data`
  (inspect with `perf report -i <file>`); if `flamegraph` is also on the
  host it renders an SVG alongside it, but a missing `flamegraph` is not
  fatal — the recipe still saves usable `perf.data` and tells you what to
  install.

**Absence on `$PATH` is not absence — check `~/.cargo/bin` too.** The same
trap CLAUDE.md documents for `lean` (`elan` never touches `PATH`) applies to
`samply` and `flamegraph`, which `cargo install` puts in `~/.cargo/bin`. Both
recipes check `command -v` **and** `~/.cargo/bin` directly, print a clear
`install with: cargo install <tool>` (or, for `perf`,
`apt install linux-tools-common linux-tools-$(uname -r)`) line, and **exit
nonzero** when the tool is missing — never silent, zero-exit nothing. Measured
on this host 2026-09-05: `perf` is present at `/usr/bin/perf`; `samply` and
`flamegraph` are absent from both `$PATH` and `~/.cargo/bin`.

**Pin to performance cores.** Both recipes run the profiled solve under
`taskset -c 0-7`. This host's hybrid CPU is measured 1.84x slower on the
E-cores when a benchmark run is left unpinned, and an unpinned run of the
`progress_frontier` capability ratchet once reported a REGRESSION that was
purely the E-cores — see
[frontier-ratchet-reference-frame.md](../research/08-planning/frontier-ratchet-reference-frame.md).
Adjust the core list if your host's P-core count differs; an E-core-only
profile attributes time to the wrong lines.

**`cargo-serialized.sh` takes a HOST-WIDE flock, so a slow profiling run may
be measuring the queue, not the solve.** Both recipes build through
`scripts/cargo-serialized.sh` rather than a bare `cargo build`, per the
multi-agent hygiene rule in [CLAUDE.md](../../CLAUDE.md) (concurrent lane
builds have twice taken a dev box down). That wrapper is the CORRECTNESS
tool, not the MEASUREMENT tool: if another lane's job holds the lock, this
recipe's own wall-clock total inflates by however long it waits, and that
inflation has nothing to do with the profiled binary. Never read a profiling
recipe's own elapsed time as a result — read the `.json.gz`/`.perf.data` it
produces, which only measures the pinned `taskset` invocation after the
build already finished.


