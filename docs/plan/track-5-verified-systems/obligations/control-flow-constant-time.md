# Control-flow constant-time by self-composition

## Claim

For the admitted MIR scalar fragment, Axeyum can prove that two executions with
the same public input and arbitrary, independently chosen secret inputs make the
same recorded branch decisions. The precise claim is **branch-decision
noninterference**. It does not say that outputs are secret-independent or that
machine execution takes identical time.

## Goal shape

For a reflected function `F(public, secret)` whose MIR executor records branch
scrutinees `leak_i`, the proof goal is

```text
forall public, secret_a, secret_b.
  and_i(leak_i(F(public, secret_a)) = leak_i(F(public, secret_b)))
```

Both runs share one public symbol and use distinct secret symbols in one term
arena. A branch-free function has an empty leak vector and satisfies the goal
vacuously. Output equality is a separate relational property and is not folded
into this definition.

## Supported fragment

The accepted T5.3.1 cell uses call-free, acyclic, scalar rustc-MIR-shaped text
with two `u32` inputs and `switchInt` control flow. Its fixtures are committed
MIR strings in the test, not bytes reproduced from a registered owning Cargo
build. The current leak model records control-flow branch scrutinees only.

## Evidence route

[`control_flow_ct_goal`](../../../../crates/axeyum-verify/src/reflect/hyper.rs)
reflects the same MIR twice, shares the public term, separates the two secret
terms, and conjoins equality of corresponding leak decisions. The safe cases
must return `ProofOutcome::Proved`. The leaky control must return
`ProofOutcome::Disproved`; its model is replayed by checking that the two
witnessed secrets fall on opposite sides of the actual branch predicate.

This route checks a term derived from the committed MIR text. It does not carry
the owning-build provenance and raw-artifact authentication used by the other
two catalog families.

## Worked example

The four tests in
[`constant_time.rs`](../../../../crates/axeyum-verify/tests/constant_time.rs),
accepted at commit `ac7494f0`, distinguish three cases:

- `if public > 100 { secret } else { 0 }` is control-flow constant-time because
  both runs branch on the shared public value;
- that same function's output equality is deliberately refuted, demonstrating
  that branch-decision noninterference is not output noninterference;
- `if secret > 100 { 1 } else { 0 }` is refuted with two replayed secret values
  that take different branches; and
- a branch-free function proves the empty leak obligation.

The 2026-07-21 cached-build observation under the command below was four of four
tests passing in 0.10 seconds wall time with 53,604 KiB peak RSS. This is a
reproduction observation, not a performance benchmark.

## Reproduce

```sh
MEM_LIMIT_GB=4 CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 \
RUST_TEST_THREADS=1 scripts/mem-run.sh \
  cargo test -p axeyum-verify --test constant_time --all-features --jobs 1 \
  -- --test-threads=1
```

The command is stable-only with respect to the committed test; it does not
authenticate a fresh compiler capture because this evidence cell has none.

## Boundaries and residuals

- No memory-access-index leakage is recorded, so cache-address behavior is out
  of scope.
- LLVM-side leakage and MIR/LLVM cross-profile 2-safety remain open.
- Compiler-capture authentication remains open for this family.
- Wall-clock timing, instruction timing, cache/TLB state, speculation, power,
  and other side channels are not modeled.
- The accepted example is a two-`u32` scalar shape, not general Rust, calls,
  loops, memory, concurrency, or a cryptographic implementation result.
- Secret-dependent output is allowed by this control-flow claim; users needing
  output noninterference must state and prove that separate goal.

See [ADR-0322](../../../research/09-decisions/adr-0322-preregister-p5.3-obligation-catalog.md)
for the catalog boundary and [P5.3](../P5.3-kernel-theories.md) for the open
residuals.
