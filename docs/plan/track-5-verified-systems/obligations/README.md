# P5.3 obligation catalog

This is the bounded, reviewer-facing answer to **“what can Track 5 prove
today?”** Each row links to a separate page with the exact goal, supported
fragment, evidence route, worked example, reproduction command, and residuals.
The rows are deliberately not presented as one uniform “kernel verification”
capability: their source authenticity and proof scope differ.

| Family | Source form | Authenticity | Proof scope | Accepted positive result | Discriminating control | Principal residual |
|---|---|---|---|---|---|---|
| [Control-flow constant-time](control-flow-constant-time.md) | committed scalar MIR fixture text | repository-controlled text; not owning-build capture | all BV32 public/secret triples for recorded branch decisions | public-predicated and branch-free examples prove branch-decision noninterference | secret-predicated branch is refuted with replayed distinguishing secrets | memory-index and LLVM leakage; authenticated compiler capture; hardware timing |
| [Bounded memory and page-table math](bounded-memory-and-page-table-math.md) | dependency-free Rust fixture plus complete compiler MIR | registered owning-Cargo capture; exact SHA-256 inventory and typed projections | all four-byte tables and BV8 addresses for seven finite claims | panic-free spec equality, frame alignment, and permission monotonicity | unmasked index, unaligned frame, and permission escalation replay in source | real MMU/address translation, aliasing, privilege, concurrency, cache/TLB |
| [FSM refinement](fsm-refinement.md) | dependency-free Rust fixture plus complete compiler MIR | registered owning-Cargo capture; exact SHA-256 inventory and typed projections | all BV8 states over four admitted events, plus unbounded safety of the finite relation | per-event and complete-relation identity refinement; spec and implementation PDR-safe | blind injection is PDR/BMC reachable and replays in source | off-alphabet inputs, richer simulations/state, liveness, concurrency, real protocol stack |

These are P5.3 v1 evidence cells, not a claim of whole-kernel correctness,
general Rust semantics, or external-target validation. The phase definition and
exit criteria remain in [P5.3](../P5.3-kernel-theories.md); the evidence-level
distinctions are frozen by
[ADR-0322](../../../research/09-decisions/adr-0322-preregister-p5.3-obligation-catalog.md).

## Evidence conventions

- A universal claim is solver-discharge over the stated finite symbolic domain,
  not merely a sample.
- A sampler corroborates reflection/spec/source agreement but does not replace a
  universal proof.
- A negative control must produce a proof refutation or reachability witness and
  replay through the closest available concrete source route.
- Artifact authentication establishes which compiler text was checked; it does
  not make the reflector or solver intrinsically trusted.
- “Safe” is always qualified by the modeled transition relation and bad
  predicate. It is not liveness, functional completeness, or environmental
  correctness.
