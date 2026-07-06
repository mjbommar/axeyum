# ADR-0056: The verified-systems trajectory (IR reflection) is a first-class track

Status: accepted
Date: 2026-07-06

## Context

Since 2026-06-29 the consumer track has been working *backwards* from an
ambitious application domain — **Rust systems and network-protocol code carrying
machine-checkable evidence, in the spirit of seL4** — first as a horizon note
([verified-systems-and-protocols.md](../../consumer-track/verify/verified-systems-and-protocols.md)),
then as a fast-moving prototype series (rounds Q–U, 2026-07-02/03) that built,
inside `crates/axeyum-verify/tests/`, working **reflection front ends for both
rustc MIR and LLVM IR** over one shared op vocabulary
([reflect-common-abstraction.md](../../consumer-track/verify/reflect-common-abstraction.md)):
cross-IR equivalence proofs (translation-validation of rustc's MIR→LLVM
lowering, of LLVM O0→O2, and of if-conversion/strength-reduction), a
wrong-transform refutation corpus with replay-checked countermodels,
panic-freedom proofs from the compiler's own debug-profile checks (overflow,
division, array bounds) with witnesses replayed against the real compiled
functions, and a checksum micro-module proved end-to-end on both platforms.

A landscape survey (2026-07-06) placed this against the field: **seL4/CertiKOS**
(interactive proofs; person-decades), **Ironclad/SPARK** (contracts + automated
provers, but you write Ada), **Hyperkernel** (push-button verification of an
xv6-class kernel *at the LLVM IR level with Z3* — the closest blueprint), and
the Rust-native wave (**Asterinas/vostd** verifying its unsafe TCB with Verus;
**Kani** via CBMC). The gap: every Rust-native option trusts an external
solver blob (Z3/CBMC) and produces no independently checkable evidence, and
verifies source-level Rust while trusting rustc+LLVM to preserve what was
proved. Axeyum's identity — *untrusted fast search, trusted small checking*,
pure Rust, deterministic, certificate-bearing — is precisely the missing
combination, and the finite/BV-shaped obligations of kernels and protocol
stacks are its strongest fragment.

The question this closes: is this a consumer-track side quest, or a first-class
goal with its own track, phases, exit criteria, and scoreboard presence?

## Decision

**The verified-systems trajectory is a first-class goal: Track 5
(`docs/plan/track-5-verified-systems/`), targeting a push-button, IR-level,
certificate-producing verifier for Rust systems code — "Hyperkernel-style
guarantees on a Rust kernel, where *proved* is independently checkable."**

Detail:

1. **Scope.** Reflection of compiled artifacts (rustc MIR *and* LLVM IR) into
   `axeyum-ir` terms; contract-driven modular verification; panic-freedom /
   memory-safety / constant-time (2-safety) / protocol-refinement obligations;
   translation-validation between IRs and across optimization levels; the
   solver-as-fuzzing-oracle loop (witness → replay → reproduce). All obligations
   stay in the decidable finite-domain fragment; where automation cannot reach,
   the answer is an honest `unknown` handed to directed fuzzing — never `sorry`.
2. **Placement.** Track 5 lives beside Tracks 1–4 under `docs/plan/`, with the
   same phase/task/exit-criteria conventions. The consumer-track `verify` app
   remains the UX surface (`#[verify]`, contracts) and demand-pull; Track 5 owns
   the front ends, theories, and measured targets.
3. **What we explicitly do NOT build** (the boundaries that keep this honest):
   no whole-kernel interactive functional correctness (that is proof-assistant
   territory; our Lean-reconstruction track is the bridge, not a replacement);
   no Verus-style ghost-code deductive language (their lane — ours is
   push-button + certificates); no source-level Rust semantics
   (borrows/aliasing) — we verify *post-borrowck MIR* and *post-optimization
   LLVM IR*, and the cross-IR equivalence proofs are what let us trust both
   views at once.
4. **Evidence discipline is unchanged.** Every `sat` witness replays against the
   real compiled function; every `unsat`/proof follows the Track 3 certificate
   ladder (DRAT today; Alethe/Lean as those keystones land); refuters are
   themselves replay-checked. External-target results follow the measured
   scoreboard discipline (DISAGREE=0, committed baselines, no seeded claims).
5. **Dependencies honored, not forked.** Track 5 consumes Track 1 keystones
   (CDCL(T), e-graph) and Track 3 formats when available but is *not blocked* on
   them — the prototype rounds proved the eager pipeline already discharges the
   flagship obligations in milliseconds. Crate creation (`axeyum-reflect`) is
   its own ADR when the test-scaffold boundary is proven by use, per ADR-0001.

## Evidence

- Working prototypes, all gates green (34 test binaries in `axeyum-verify` as of
  2026-07-03): `tests/reflect_common/{mod,mir,llvm}.rs`,
  `tests/cross_ir_equivalence.rs` (16 proofs incl. hypothesis-gated
  `unreachable` semantics), `tests/cross_ir_refutation.rs` (5 miscompile shapes
  refuted, countermodels replay-checked), `tests/checked_reflection.rs`,
  `tests/checked_division.rs` (exact panic specs: `b==0`;
  `b==0 ∨ (a==MIN ∧ b==-1)`), `tests/checked_bounds.rs` (bounds-check
  unreachability over all 2^64 indices), `tests/checksum_module.rs`
  (module-scale, both platforms, protocol receiver property).
- Measured wall-times: individual equivalence/panic proofs in milliseconds;
  whole suites < 3 s debug (fuzz-dominated) — cheap enough for per-commit gates.
- Landscape: Hyperkernel (SOSP '17, LLVM-IR + Z3, finitized interface) is the
  design precedent; Asterinas/vostd (Verus on the OSTD TCB) is the market
  precedent; neither produces independent certificates nor runs pure-Rust.

## Consequences

- `docs/plan/track-5-verified-systems/` exists with phases P5.1–P5.5; PLAN.md's
  track map, STATUS.md's phase tables, `docs/plan/README.md`,
  `docs/plan/00-north-star.md` (a third, application-level definition of done),
  and `docs/plan/01-dependency-dag.md` carry the track.
- The consumer-track verify docs
  ([verified-systems-and-protocols.md](../../consumer-track/verify/verified-systems-and-protocols.md))
  are upgraded from "horizon note" to the adopted application charter of
  Track 5.
- The trajectory is subject to the same standing rules as every track: measured
  claims only, DISAGREE=0 gates, pathspec commits, and the frontier ratchet
  before solver-facing changes.
