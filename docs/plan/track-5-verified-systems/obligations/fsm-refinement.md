# Compiler-reflected FSM refinement

## Claim

For one deterministic scalar handshake step, Axeyum proves that the
compiler-reflected Rust implementation has exactly the same admitted transition
relation as an independently built declarative specification under identity
state refinement. It then proves the reflected implementation's bad state
unreachable with PDR. This is one finite safety refinement cell, not general
protocol correctness.

## Goal shape

State and event are BV8. The admitted states are
`{CLOSED=0, SYN_SENT=1, ESTABLISHED=2, BAD_ESTABLISHED=3}` and the admitted
events are `{SEND_SYN=0, RECV_SYNACK=1, CLOSE=2, DATA=3}`. The good step is

```text
CLOSED + SEND_SYN       -> SYN_SENT
SYN_SENT + RECV_SYNACK  -> ESTABLISHED
any state + CLOSE       -> CLOSED
otherwise               -> unchanged state
```

For each concrete event `e`, the universal obligations are

```text
forall state : BV8. reflected_next(state, e) = spec_next(state, e)
forall state : BV8. reflected_panic(state, e) = false
```

The complete implementation and specification transition disjunctions are then
proved equal. Init and bad predicates are separately identical, so the exact
relation equality transports the safety property under identity state
relation. Inputs outside the four-event alphabet are excluded from the
transition relation.

## Supported fragment

The dependency-free source fixture contains two complete inlined call-free,
loop-free, memory-free `fn(u8, u8) -> u8` functions. The existing
`scalar-contract` profile is used only as a checked scalar capture path; no
function contract is authored or consumed. The registered owning Cargo build
emits one complete 2,691-byte MIR module for both selected functions.

## Evidence route

The fixture's
[`provenance.json`](../../../../crates/axeyum-verify/tests/fixtures/mir-fsm-target/artifacts/provenance.json)
binds source, lockfile, registered Cargo/rustc identities, ordered arguments,
profile, width, selections, and four byte-identical fresh captures.
[`SHA256SUMS`](../../../../crates/axeyum-verify/tests/fixtures/mir-fsm-target/artifacts/SHA256SUMS)
authenticates the exact source/artifact set; the raw MIR hash is
`4fd05de856b6921cd02f0b253119646e9078769cbd21a491fbc6332b2e784f8b`.

[`mir_fsm_refinement.rs`](../../../../crates/axeyum-verify/tests/mir_fsm_refinement.rs)
builds the specification independently, proves eight per-event groups and the
complete relation equality, then runs PDR on both the declarative and reflected
systems. The deliberately buggy reflected function adds
`CLOSED + RECV_SYNACK -> BAD_ESTABLISHED`; PDR and BMC both report it reachable,
and the one-step witness replays through reflected terms, the independent
control, and exact Rust source.

## Worked example

[ADR-0321](../../../research/09-decisions/adr-0321-preregister-reflected-handshake-fsm-refinement.md)
accepts:

- four byte-identical fresh compiler captures of one 2,691-byte module;
- eight universal per-event proof groups plus complete transition-relation
  equality and separately identical init/bad predicates;
- PDR-safe declarative and reflected systems;
- a PDR/BMC/source-replayed blind-injection control;
- exactly 2,048 state/event/function rows with zero disagreement, evaluation
  error, panic, or dropped row; and
- nine semantic mutations with no unexpected survivor.

Recorded wall observations are 382 ms for pinned two-selection capture
reproduction, 100 ms for per-event proofs, 11,896 ms for complete-relation
equality plus the two safe PDR runs, 23 ms for buggy PDR/BMC/source replay, and
67 ms for the sampler.

## Reproduce

The stable artifact/refinement/PDR/replay route is:

```sh
MEM_LIMIT_GB=4 CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 \
RUST_TEST_THREADS=1 scripts/mem-run.sh \
  cargo test -p axeyum-verify --test mir_fsm_refinement --all-features --jobs 1 \
  -- --test-threads=1
```

Authenticate the committed inventory separately:

```sh
(cd crates/axeyum-verify/tests/fixtures/mir-fsm-target && \
  sha256sum -c artifacts/SHA256SUMS)
```

The exact fresh-capture test is
`compiler_fsm_selections_reproduce_the_authenticated_raw_module` in
`cargo_mir_build.rs`. Set `AXEYUM_VERIFY_MIR_CARGO` and
`AXEYUM_VERIFY_MIR_RUSTC` to the registered binaries and
`AXEYUM_VERIFY_MIR_REQUIRE_CARGO_BUILD=1` to make unavailable or wrong tools a
hard failure.

## Boundaries and residuals

- Events outside `{0,1,2,3}` receive no protocol claim.
- The state relation is identity over one BV8 scalar; abstraction, stuttering,
  arrays, buffers, data state, and richer simulations remain open.
- Safety is not liveness, fairness, progress, deadlock freedom, or temporal
  completeness.
- Concurrency, multi-peer scheduling, packet formats, transport behavior, TCP
  compliance, real networking, and external stacks are absent.
- The test-local construction is not a public reusable refinement API.
- Equal safety verdicts alone would be insufficient; this cell's claim rests on
  the stronger per-event and complete-relation equality proofs.

See the [catalog index](README.md) for the evidence-level comparison.
