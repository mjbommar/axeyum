# Track 5 — Verified Systems (IR reflection)

> **Adopted as a first-class goal by
> [ADR-0056](../../research/09-decisions/adr-0056-verified-systems-track.md)
> (2026-07-06).** The application charter — the seL4-inspired end goal, the
> capability ladder, and why systems/protocol code fits this stack — is
> [`docs/consumer-track/verify/verified-systems-and-protocols.md`](../../consumer-track/verify/verified-systems-and-protocols.md).
> This track is the *engineering plan* for it.

## The one-sentence goal

**A push-button, IR-level, certificate-producing verifier for Rust systems
code** — reflect what the compiler actually produced (rustc **MIR** and **LLVM
IR**) into `axeyum-ir`, discharge panic-freedom / memory-safety /
constant-time / equivalence / protocol obligations automatically on the
decidable finite-domain core, and back every verdict with replayable or
independently checkable evidence. Hyperkernel's recipe (finitize, verify at the
IR, push-button) with the two things it lacked: **no trusted external solver**
and **certificates**.

## Definition of done (measurable, per the north star's style)

Track 5 is *done as a v1 trajectory* when:

1. **Front end** — a real crate (not a test scaffold) reflects the MIR and LLVM
   IR of a supported Rust fragment from a normal `cargo` build, with calls
   handled modularly via contracts and loops bridged to the
   `TransitionSystem`/k-induction engines. (P5.1, P5.2)
2. **Obligations** — panic-freedom (overflow/division/bounds), 2-safety
   (constant-time / secret-independence), cross-IR translation-validation, and
   FSM-refinement obligations each have a shipped, documented route with
   examples. (P5.1–P5.3)
3. **Evidence** — every `sat` replays against the real compiled function
   (automated, not hand-written per test); every `unsat` follows the Track 3
   certificate ladder; the fuzz loop consumes `unknown`s. (P5.4)
4. **Measured on a real external target** — at least one module of a real Rust
   OS/systems project verified or a real bug found+reproduced, committed under
   the scoreboard discipline (DISAGREE=0), with wall-times. (P5.5)

We do **not** claim seL4 parity, whole-kernel functional correctness, or
source-level Rust semantics — see ADR-0056 §Decision-3 for the boundaries.

## Where it starts from (2026-07-03, prototype rounds Q–U)

All of this already runs green as `crates/axeyum-verify/tests/` scaffolding
(design log:
[`reflect-common-abstraction.md`](../../consumer-track/verify/reflect-common-abstraction.md)):

- Shared op vocabulary + **symbolic executors over acyclic CFGs for both IRs**
  (`tests/reflect_common/{mod,mir,llvm}.rs`): MIR `switchInt`/`goto`/`assert`/
  checked-arithmetic tuples/casts/unary/bool-ops/`Div-Rem`/array indexing;
  LLVM `br`+`phi`/`switch`/`select`/intrinsics/`unreachable`-as-don't-care/
  panic-call skipping; sign-aware, multi-parameter, byte-array params.
- **Cross-IR equivalence** (16 proofs): MIR ≡ LLVM per function, LLVM O0 ≡ O2,
  if-conversion/strength-reduction/min-idiom validated, hypothesis-gated
  `unreachable` semantics; a **refutation corpus** (5 miscompile shapes) with
  replay-checked countermodels; a 10k-sample-per-pair differential fuzz.
- **Panic-freedom from the compiler's own checks**: exact panic specifications
  (division: `b==0`; signed: `∨ (a==MIN ∧ b==-1)`), bounds-check
  unreachability over all 2^64 indices, witnesses replayed via `catch_unwind`.
- **Module scale**: the checksum pair proved end-to-end on both platforms,
  including the protocol-level receiver property.

Individual proofs are **milliseconds**; suites < 3 s debug. That speed is the
strategic asset: these run as ordinary per-commit tests.

## Phases

The accepted P5.3 families have a bounded reviewer-facing
[obligation catalog](obligations/README.md) that separates their exact goals,
source authenticity, evidence routes, worked examples, and residuals.

| Phase | Title | Size | Depends on |
|---|---|---|---|
| [P5.1](P5.1-reflection-frontend.md) | The reflection front end (crate-ify MIR+LLVM reflection) | L | prototype scaffolds (done); crate split needs its own ADR |
| [P5.2](P5.2-contracts-modular.md) | Contracts & modular verification (`#[requires]`/`#[ensures]`) | L | P5.1; `axeyum-verify` macro surface |
| [P5.3](P5.3-kernel-theories.md) | Kernel-shaped obligations: memory regions/page tables, 2-safety/constant-time, FSM refinement | L | P5.1; arrays (shipped), `TransitionSystem` (shipped) |
| [P5.4](P5.4-fuzz-oracle.md) | The fuzzing loop: reflected terms as oracles, witnesses as seeds, `unknown` handoff | M | P5.1 |
| [P5.5](P5.5-external-target.md) | **DONE (bounded v1)** — authenticated Tock integer-log capture plus eight checked proofs, six replayed controls, UNKNOWN=0, DISAGREE=0, and an honest measured comparison; no target bug found | M–L | P5.1 + at least one of P5.2/P5.3 |

Recommended order: **P5.1 → (P5.2 ∥ P5.4) → P5.3 → P5.5**, with P5.5's target
selection done early (it shapes P5.1's fragment priorities).

## Relationship to the other tracks

- **Track 1/2 (engine/theories):** Track 5 is demand-pull — its obligations are
  QF_BV/QF_ABV-shaped and already decided by the eager pipeline; the CDCL(T)
  keystone and lazy arrays make it faster/warmer but do not gate it.
- **Track 3 (proofs/Lean):** Track 5 is the flagship *consumer* of certificates
  — panic-freedom and equivalence verdicts are exactly the verdicts users need
  independently checkable. The trust ledger covers reflection the same way it
  covers reductions: the reflector is untrusted search; replay/differential
  fuzz/certificates are the checking.
- **Track 4 / consumer track:** `axeyum-verify` (`#[verify]`) remains the UX;
  P4.2's symexec/CFG frontend and Track 5's reflectors converge on the same
  `SymbolicExecutor`/memory substrate over time.

## Standing rules (inherited, non-negotiable)

Measured claims only (no seeded scoreboards); every witness replays; DISAGREE=0
on all differential gates; `unknown` is honest and first-class; pathspec
commits; the UB/poison stance is documented per front end, never silent.
