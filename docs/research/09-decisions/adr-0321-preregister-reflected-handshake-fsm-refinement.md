# ADR-0321: Preregister reflected handshake FSM refinement

Status: accepted
Date: 2026-07-21

## Context

ADR-0320 closes bounded T5.3.2 v1. The next open P5.3 task is T5.3.3:
demonstrate that a reflected implementation step function refines a spec-side
`TransitionSystem`, then transport the spec safety property across that
relation. The repository already ships all semantic pieces independently:

- `protocol_toolkit.rs` defines the declarative four-state handshake `Fsm` and
  proves its bad state unreachable with PDR;
- `protocol_unbounded.rs` defines the same transition relation by hand and
  carries certified unbounded safety; and
- checked MIR scalar reflection accepts call-free acyclic functions with
  multiple scalar parameters and explicit panic terms.

A temporary zero-row probe, retained outside the repository, compiled one
call-free Rust `handshake_step(state: u8, event: u8) -> u8` and one inlined
blind-injection control under the registered nightly. The existing
`scalar-contract` capture profile accepted both without using contracts: the
good selection has ten blocks, the buggy selection thirteen, both have two
`u8` parameters, an eight-bit result, and a false panic term, and both owning
Cargo selections emit the same 2,691-byte raw module. This is sufficient to
select an evidence experiment; it is not refinement evidence.

## Decision

Create a new excluded, dependency-free `mir-fsm-target` fixture so no
authenticated source or raw artifact from ADR-0317 or ADR-0320 changes. Its
good Rust step implements the shipped four-event handshake:

```text
CLOSED + SEND_SYN     -> SYN_SENT
SYN_SENT + RECV_SYNACK -> ESTABLISHED
any state + CLOSE      -> CLOSED
otherwise              -> unchanged state
```

The buggy control additionally maps `CLOSED + RECV_SYNACK` to the distinct
`BAD_ESTABLISHED` state. Both functions inline the complete table and contain
no calls, loops, memory, assertions, or effects.

Capture the complete module through the existing `axeyum-mir-build
--profile scalar-contract` path. Here that profile is used only for its
root-independent call-free scalar capture/check contract; no modular function
contract is authored or consumed. Reflect the selected function into an arena
over symbolic `(state, event)` terms.

Define the spec independently as a deterministic nested-`ite` transition for
each of the four concrete events. Use identity as the simulation relation on
one BV8 state. Prove, separately for every event and all 256 state values, that
the reflected good next state equals the spec next state and cannot panic.
Then construct a test-local implementation `TransitionSystem` whose transition
disjunction is built from the reflected function, with the same init and bad
predicates as the declarative spec. Prove the complete spec and implementation
transition relations equivalent, prove the implementation system safe with
PDR, and retain the spec's independently safe PDR control. This exact relation
equality transports the bad-state safety property; it is stronger than the
one-way simulation needed for this deterministic cell.

## Frozen evidence gates

1. Commit this zero-result ADR before adding the fixture, capture artifact,
   refinement harness, result report, or result prose. The temporary probe is
   shape-selection evidence only and must not enter the committed artifact.
2. The new fixture is dependency-free and outside the root workspace. Existing
   authenticated MIR fixtures, sources, locks, artifacts, and hashes remain
   byte-identical. The good and buggy functions are complete inlined source;
   helper calls, macros, loops, memory, and hidden generated code are rejected.
3. Capture each function twice through fresh locked owning-Cargo builds under
   the registered Cargo/rustc pair, 64-bit target width, and exact call-free
   scalar profile. All four raw modules and the committed raw module are
   byte-identical. Commit source/lock/raw bytes, root-independent provenance,
   both typed summaries, exact SHA-256 inventory, and a measured result report.
4. A stable validator authenticates the exact path/hash set and typed
   projections without the pinned nightly. An opt-in pinned test reproduces
   both selections exactly. Wrong tools, selection, profile, target width,
   tamper, malformed MIR, existing output, or failed capture receives no
   artifact credit and leaves no partial output.
5. Freeze the independent spec alphabet and states exactly as
   `{SEND_SYN=0, RECV_SYNACK=1, CLOSE=2, DATA=3}` and
   `{CLOSED=0, SYN_SENT=1, ESTABLISHED=2, BAD_ESTABLISHED=3}`. The spec builder
   does not call the fixture source or reuse the reflected result. Inputs
   outside the four-event alphabet are excluded from the `TransitionSystem`
   relation and receive no protocol claim.
6. Eight per-event universal proof groups pass: four good reflected result
   equalities plus four good reflected `panic == false` claims, each over every
   BV8 state. A combined proof establishes equality of the complete spec and
   implementation transition disjunctions under identity state relation. Init
   and bad predicates are structurally identical and separately checked.
7. PDR independently reports the declarative spec safe and the
   reflected-implementation system safe. The buggy reflected system is
   reachable under both PDR and bounded model checking. Its one-step
   `CLOSED + RECV_SYNACK -> BAD_ESTABLISHED` witness is replayed against the
   reflected term, independent spec control, and exact Rust source; the good
   neighbor stays out of the bad state.
8. Exhaustively evaluate every 256-valued state for each of four events and
   both good/buggy functions: exactly 2,048 function rows. Record zero
   reflection/spec/Rust disagreement, evaluation error, panic, or dropped row.
   The buggy function is compared to the independently buggy spec, never
   credited as refining the good spec.
9. Mutation teeth flip the CLOSE target, delete the SEND_SYN transition, alter
   the SYNACK source state, add/remove the blind-injection arm, swap event IDs,
   mutate init/bad predicates, alter widths/sorts, and tamper with every
   artifact class. Each semantic mutation is proof-refuted with replay or
   changes the PDR/BMC verdict as preregistered; metadata/config mutations fail
   with stable classes.
10. Record capture, refinement-proof, PDR/BMC, and exhaustive-replay wall times
    separately. Make no liveness, fairness, concurrency, packet-format,
    network-stack, TCP-compliance, unbounded data-state, or external-target
    claim. This cell refines one finite deterministic step relation only.
11. No production reflection, IR, solver, public API, dependency, feature,
    unsafe, MSRV, or WASM change is authorized. The executable-semantics
    inventory remains 81 variants. Focused tests, complete `axeyum-verify` and
    doctests, strict Clippy/rustdoc, reflection semantics gate, scoped
    formatting, links, and the one-job 4 GiB/OOM audit pass.

No gate may be weakened after the first fixture, capture, proof, transition-
system, or replay result is observed. A failed gate records a negative result
and removes/restores uncredited candidate changes.

## Result

Accepted. The new excluded, dependency-free fixture authenticates one
2,691-byte raw compiler MIR module for both `handshake_step` selections. Two
fresh owning-Cargo captures per function (four total) are byte-identical to
the committed module at SHA-256
`4fd05de856b6921cd02f0b253119646e9078769cbd21a491fbc6332b2e784f8b`.
The pinned reproduction gate observes two exact selections and no raw or typed
projection drift. The `scalar-contract` profile is used only as the existing
call-free checked scalar capture path; no function contract is authored or
consumed.

All eight universal per-event proof groups pass. The independently built spec
and reflected implementation have equal complete transition relations under
the identity state relation, with identical init and bad predicates. PDR
reports both systems safe. The deliberately buggy reflected system is
reachable under both PDR and BMC, and its
`CLOSED + RECV_SYNACK -> BAD_ESTABLISHED` witness replays against the reflected
term, independent control, and exact Rust source.

The exhaustive sampler covers exactly 256 states, four events, and two
functions: 2,048 rows with zero reflection/spec/Rust disagreement, evaluation
error, panic, or dropped row. All nine semantic mutations are refuted or alter
the safety result as frozen, and artifact/configuration tampering fails closed.
Observed wall times were 382 ms for pinned two-selection capture reproduction,
100 ms for the eight per-event proofs, 11,896 ms for complete-relation equality
and the two safe PDR runs, 23 ms for buggy PDR/BMC/source replay, and 67 ms for
the exhaustive sampler.

The complete `axeyum-verify` all-feature test and doctest suite, strict Clippy
and rustdoc, the 81-variant reflection-semantics gate, scoped formatting, artifact
hash, link, and one-job 4 GiB/OOM gates pass. No production code, public API,
dependency, feature, executable-semantics variant, or existing authenticated
fixture changed. This closes bounded deterministic scalar T5.3.3 v1 only;
T5.3.4 and every broader protocol/refinement residual remain open.

## Rejected alternatives

- **Refine the bounded four-event driver loop.** Rejected: T5.3.3 asks for the
  reusable one-step transition relation, not another fixed-horizon unroll.
- **Use the test-local concrete closure as the implementation.** Rejected: the
  implementation must be compiler-reflected Rust, not the spec table twice.
- **Modify an authenticated existing fixture.** Rejected: that would invalidate
  ADR-0317 or ADR-0320 evidence for unrelated convenience.
- **Add a production protocol/FSM abstraction first.** Rejected: the existing
  `TransitionSystem` trait and checked scalar reflector are sufficient for the
  first evidence cell. A reusable API requires later demonstrated demand.
- **Claim general protocol refinement from matching safety verdicts.** Rejected:
  verdict agreement alone is weaker than the frozen per-event and full-relation
  equivalence proofs.

## Consequences

- A positive result closes the first T5.3.3 deterministic scalar refinement
  cell and supplies the worked handshake example needed by T5.3.4.
- Array-bearing protocol state, multi-peer synchronization, stuttering/
  abstraction relations, liveness, and a reusable public refinement API remain
  separate, evidence-gated work.

## References

- `crates/axeyum-verify/tests/protocol_toolkit.rs`.
- `crates/axeyum-verify/tests/protocol_unbounded.rs`.
- `crates/axeyum-verify/src/reflect/mir/checked.rs`.
- `docs/plan/track-5-verified-systems/P5.3-kernel-theories.md`.
