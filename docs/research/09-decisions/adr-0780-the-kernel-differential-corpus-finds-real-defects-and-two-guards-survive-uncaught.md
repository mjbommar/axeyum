# ADR-0780: The kernel differential corpus finds real defects, and two guards survive uncaught

Status: accepted
Date: 2026-08-30
Index-summary: A 32-case, hand-authored (both sides independently) Axeyum-vs-pinned-Lean corpus across all eight ADR-0717 S5 subsystems ran clean against Lean 4.30.0 with one registered incompleteness (no `Quot.sound`, by design); building it caught two real construction bugs (a de Bruijn depth error, a `Pi`-for-`Lam` confusion) before any Lean comparison ran, and a follow-up kernel-source mutation pass found the corpus kills 4 of 8 targeted guards outright -- including a proof-irrelevance mutation that alone flips 10 of 32 cases to P0 -- while `literals` and `quotient` survive for named, expected coverage-gap reasons and `inductives` survives unexplained.

Lane: `l0-s5-kernel-differential`. Phase: ADR-0717 L0,
`docs/plan/trusted-library-safety-roadmap-2026-08-30.md` phase **S5**.

## Context

ADR-0717's risk 1 is that Axeyum's kernel could have a semantic defect that
no amount of axiom-freedom detects, because every proof in this repository
is checked by that same kernel. S5's spec asks for a deterministic corpus of
well-typed and nearly-well-typed core declarations across conversion,
universes, inductives, recursors, projections, literals, quotient, and proof
irrelevance, compared against pinned Lean, plus mutation testing of the
kernel tests themselves with surviving mutants published by subsystem.

`Kernel::render_lean_module` only walks an already-checked declaration
closure (`crates/axeyum-lean-kernel/src/lean_pp.rs`), so it cannot express
the nearly-well-typed half of the corpus: a rejected declaration never
reaches `kernel.environment()`, so there is nothing to render. The
established pattern in this crate's `real_lean_*_crosscheck` suites --
hand-authoring the Axeyum side (kernel term-builder API) and the Lean side
(plain `.lean` surface syntax) independently -- is the one this ADR follows,
because it is the more meaningful differential besides: each kernel decides
accept/reject using its own native surface, not a translation designed to
please the other.

## Decision

`crates/axeyum-lean-kernel/tests/kernel_differential.rs` holds 32 cases (4
per subsystem: 2 well-typed, 2 one-step-from-valid mutants), each built twice
independently. Classification is three-way: both agree (expected, the
default), Axeyum-accepts-Lean-rejects (P0, hard failure, no waiver), and
Axeyum-rejects-Lean-accepts (incompleteness, must be pre-registered in
`EXPLAINED_INCOMPLETENESS` with a citation or the test fails just as hard).
One case is registered: `quotient::quot_sound_absent` -- this kernel
implements exactly Lean's four-declaration `Quot`/`Quot.mk`/`Quot.lift`/
`Quot.ind` package and deliberately has no `Quot.sound` (ADR-0456;
`creal.rs`, `int_prelude.rs`, `rat_prelude.rs` module docs already document
this), so a term citing it is trivially accepted in Lean and rejected here
because the name does not exist.

`scripts/check-kernel-differential.py` is the gate: it runs the suite with
`AXEYUM_REQUIRE_LEAN=1` and independently re-derives pass/fail from the
parsed output text via six named guards (corpus non-empty, every subsystem
non-empty, Lean actually invoked, zero P0, zero unexplained incompleteness,
process exit status) rather than trusting the test binary's exit code alone.
Each guard is mutation-verified on a scratch copy
(`scripts/tests/test-kernel-differential-gate.sh`): deleting any one of the
six kills exactly one fixture and no other.

`artifacts/kernel-differential/mutant-kill-table.json` records a hand-run
kernel-source mutation pass, one mutation per subsystem, each disabling a
specific guard in `crates/axeyum-lean-kernel/src/{tc,inductive,quotient}.rs`
and re-running the corpus against pinned Lean before reverting.
`scripts/check-kernel-differential-mutants.py` ratchets the artifact's own
internal consistency (every subsystem covered once, every `KILLED` entry
names evidence, summary counts match the entries) rather than re-running the
~8 kernel rebuilds the measurement itself needs -- mutating tracked kernel
source is exactly the operation CLAUDE.md's shared-worktree section forbids
running unattended, so re-measuring is a deliberate, human-triggered act,
never an automatic one.

## Evidence

Full run against `leanprover/lean4:v4.30.0`
(`d024af099ca4bf2c86f649261ebf59565dc8c622`): 32/32 cases, `checked=32`,
zero unexplained disagreement, exactly the one registered incompleteness.

Building the corpus caught two real bugs in the corpus itself before any
Lean comparison ran, both instructive beyond this file:

- `inductives::parametric_container_positive` briefly reported
  `AxeyumRejectsLeanAccepts`: a field type's own free-variable reference was
  built at one nesting depth (`bvar(0)`) and then placed one binder deeper
  than that, without shifting. Axeyum correctly rejected the resulting
  ill-formed term; the bug was in the test, not the kernel.
- A quotient case's function VALUE was built with the same `close_pi` helper
  used for TYPES (which always emits `Pi`), producing a `Pi` whose "body" is
  a proof term rather than a type -- `NotASort`. A second helper,
  `close_lam`, was added for values.

The kernel-source mutation pass (8 mutations, one per subsystem, against the
live corpus and Lean):

| subsystem | status | signal |
|---|---|---|
| proof_irrelevance | KILLED | dropping the Prop-only restriction on proof irrelevance (`tc.rs::proof_type`) flips 10 of 32 cases to P0 |
| universes | KILLED | dropping the undeclared-universe-param check flips exactly its own targeted case |
| recursors | KILLED | always selecting the first iota rule regardless of the major's constructor crashes the whole run before any case prints (the logic prelude's own proofs use multi-rule recursors) |
| conversion | KILLED | disabling `infer_app`'s per-argument type check flips two OTHER subsystems' cases (recursors, quotient), not conversion's own, which are caught by a separate declared-vs-inferred `def_eq` check at `Theorem` admission |
| inductives | SURVIVED, unexplained | the targeted non-positive-occurrence guard's removal did not flip `non_positive_occurrence_negative`; the true rejecting mechanism is not yet identified |
| projections | SURVIVED, explained | a second, structural check (constructor-telescope exhaustion) is redundant with the disabled bounds check for this case's shape |
| literals | SURVIVED, explained | no case in this corpus presents a malformed `Nat` bootstrap declaration |
| quotient | SURVIVED, explained | no case builds a second, non-canonical quotient package to be confused with the real one |

Three of the four survivals are named, expected coverage gaps, not silent
holes. The fourth (`inductives`) is a genuine open question this ADR
records rather than papers over.

## What this does NOT cover

Stated in `kernel_differential.rs` itself and repeated here because it
matters for anyone extending this corpus: four cases per subsystem
demonstrates the harness and exercises one concrete near-miss per subsystem,
not an exhaustive enumeration of that subsystem's defect space. It does not
cover mutual/nested inductive families, indexed families beyond the trivial
0-index case, `Prop`-restricted large elimination, structure eta beyond
plain projection, string literals, `let`/zeta reduction, well-founded
recursion, multi-step reduction chains longer than the two-hop delta chain
in `conversion`, or malformed-package/malformed-bootstrap shapes for
quotient and literals specifically (the two subsystems whose survived
mutants trace to exactly that gap).

## Alternatives

**Render checked declarations through `Kernel::render_lean_module` instead
of hand-authoring both sides.** Rejected: that renderer only walks an
already-admitted closure, so it cannot express the Axeyum-rejects half of
the corpus at all -- a rejected declaration never enters `environment()`.

**Re-run the full kernel-source mutation pass automatically in CI.** Rejected
for now: it mutates tracked kernel source in place across ~8 rebuilds, which
is the exact hazard CLAUDE.md's shared-worktree section names (a mutant on
disk breaks every other lane's concurrent build). The ratchet instead
ratchets the recorded artifact's shape; re-measuring is a deliberate,
by-hand act until an isolated (worktree-per-mutant) runner exists to make it
safe to automate.

## Consequences

The next slice of this lane's work is widening the corpus toward the named
gaps above -- particularly a malformed-package case for `quotient` and a
malformed-bootstrap case for `literals`, which would very likely turn two of
today's "explained" survivals into kills -- and root-causing the
`inductives` survival before treating it as explained. Any future case that
finds a genuine P0 (Axeyum accepts, Lean rejects) preempts all other
`axeyum-lean-kernel` work per ADR-0717, unconditionally.
