# ADR-0053: `axeyum-strings` crate + the Phase-B word-equation core

Status: proposed
Date: 2026-07-03

## Context

Phase A of the strings program is landed: strings are first-class IR terms
(`Sort::Seq`, ADR-0051), the `len`↔LIA link + the bounded-unsat gate hold
`DISAGREE=0` on the measured string divisions (ADR-0052), and the bounded
packed-BV encoder (ADR-0029) remains the decision path for provably-small
instances. The measured remainder — QF_S 52/134, QF_SLIA 12/50, and the
StringGate's ~16 honest `unknown` downgrades — is exactly the **unbounded
word-equation fragment**: variable `str.++` equalities, symbolic `substr`,
loops. No amount of bounded encoding reaches it; this is the cvc5 CAV-2014
normal-form/arrangement procedure's territory
([Phase B plan](../../plan/track-2-theories/P2.7-strings/04-phaseB-word-equations.md)).

ADR-0051 deferred the `axeyum-strings` crate split "until the Phase-B
word-level solver proves the boundary" and required a superseding ADR for the
solver architecture before it lands (ADR-0001 boundary rule; the standing rule
that semantics, model lifting, and checker routes are explicit before a new
logic fragment becomes public surface). This ADR is that record.

## Decision

**Create `crates/axeyum-strings`: a pure-Rust word-level string theory solver
implementing the CAV-2014 normal-form/arrangement procedure, landed in the
Phase-B task slices (T-B.1 … T-B.7), consumed by `axeyum-solver` as a
routing stage strictly after the ADR-0029 bounded pre-check and the ADR-0052
gate.**

- **Crate boundary.** `axeyum-strings` depends only on `axeyum-ir` (the same
  shape as `axeyum-fp`): input is `Sort::Seq`-sorted `TermId`s over a shared
  `TermArena`, output is verdicts + witness assignments + derivations. No
  solver-crate dependency, no C/C++, `forbid(unsafe_code)`, WASM-clean.
  The boundary is proven by use per ADR-0001: `axeyum-solver` routes to it,
  and its normalization pass is a denotation-preserving rewrite family the
  SMT-LIB front end can also reach.
- **Module layout** follows the
  [architecture plan](../../plan/track-2-theories/P2.7-strings/02-architecture.md):
  `normal_form.rs` (T-B.1/T-B.2), `core_solver.rs` (T-B.3/4/5), `eager.rs`
  (T-B.6), `length.rs` (the Phase-A LIA link, consumed not duplicated),
  `regex/` + `extf.rs` + `model.rs` + `automata.rs` arriving with Phases C–E.
- **First slice (T-B.1): the normalization invariant.** A confluent,
  terminating rewrite over `Seq`-sorted terms — flatten nested `SeqConcat`,
  drop `SeqEmpty` components, fuse adjacent sequence constants, push `SeqLen`
  through concatenation and constants. Every rule is **denotation-preserving
  and property-tested against the ground evaluator** (random terms, random
  assignments: rewritten term evaluates identically). This is the precondition
  for flat/normal forms and is useful stand-alone (it feeds the canonicalizer
  contract in `axeyum-rewrite`, which currently declines all `Seq` ops).
- **Bridge execution mode.** Until P1.4/P1.5 provide the CDCL(T) loop, the
  solver runs one-shot/eager behind `check_auto` dispatch, exactly as the
  bounded path does today. Verdict discipline:
  - `sat` ⇒ a concrete assignment that **replays through the ground
    evaluator** against the original assertions — the trust anchor; a
    non-replaying model is a decline, never a verdict.
  - `unsat` ⇒ only through a re-checkable derivation. Until the derivation
    checker exists (T-B.7's explanation tracking), word-level UNSAT is
    **declined to `unknown`** — the ADR-0052 LenAbs/Parikh abstraction
    remains the only unbounded-UNSAT route. We never ship a wrong verdict by
    construction, not by hope.
  - Budget-guarded `unknown` outside the straight-line/acyclic/chain-free
    fragments (`F-Loop` regularizes loops; past budget ⇒ `unknown`,
    first-class). Every solve honors `config.timeout` from day one — the
    deadline-hole bug class (bug330, the uflra fuzz hang) is designed out,
    not patched in later.
- **Front-end fork (ADR-0051 §open-reconciliation) resolves per-route, not
  up front.** `(Seq E)`/`String` syntax keeps parsing to the ADR-0029 bounded
  representation. The word-level solver is fed by a *parser-side dual build*
  landed as its own slice when T-B.4 can first decide something: the parser
  additionally emits first-class `Sort::Seq` terms for the string fragment,
  and dispatch picks bounded-first, word-level second. Re-routing
  `parse_sort` wholesale stays forbidden until that slice's differential
  gates are green.
- **Automata substrate: deferred to a Phase-C ADR.** Phase B needs no
  automata dependency — `F-Loop` emits `str.in_re` constraints, and until
  Phase C those route to the existing bounded/abstraction handling (or
  decline). The `regex-automata` vs `aws-smt-strings` vs from-scratch choice
  is made when derivatives land, with the reference clones consulted.

## Evidence

- The measured gap is concentrated where only this procedure reaches:
  QF_S 82/134 undecided, QF_SLIA 38/50 undecided on the committed baselines
  (`bench-results/SCOREBOARD.md`), and every StringGate downgrade is a
  word-equation shape by inspection (the gate's telemetry is the routing
  signal).
- cvc5's `theory_strings` (in `references/cvc5`) is the working reference for
  rule-level behavior; the CAV-2014 paper fixes the procedure; both are
  design references, not dependencies.
- The bounded path + ADR-0052 gate stay untouched underneath: this ADR only
  adds a route above validated surface, so the 371-instance bounded
  DISAGREE=0 record and the gate's soundness tests cannot regress.

## Alternatives

- **Keep growing the bounded encoder** (larger `max_len`, wider content).
  Rejected: exponential encoding growth buys instances linearly; unbounded
  word equations stay unrepresentable; the 9-hour-hang class showed the
  bound-growth path's cost profile.
- **Eager reduction to arrays/BV over an unbounded index theory.** Rejected:
  reproduces Z3str3's known fragility; contradicts the untrusted-search /
  trusted-check identity because models stop being directly replayable.
- **Build inside `axeyum-solver` without a crate split.** Rejected by
  ADR-0051's own deferral condition: Phase B *is* the boundary proof, the
  module set is large (7 files, growing through Phase E), and the SMT-LIB
  front end is a second consumer of the normalization pass.
- **Word-level UNSAT immediately (trust the arrangement derivation).**
  Rejected for the bridge period: the reference solvers shipped soundness
  bugs in exactly this procedure; UNSAT waits for checkable derivations
  (T-B.7), mirroring how the pure-Rust SAT path waited for DRAT.

## Consequences

- **Easier:** unbounded string sat becomes reachable (replay-checked, so
  soundness-cheap to ship incrementally); the StringGate's downgrades get a
  second-chance route; Phases C–E have a crate to land in; the canonicalizer
  can start consuming `Seq` rewrites.
- **Harder / the cost:** a new crate to gate (fmt/clippy/deny/doc/WASM);
  the parser dual-build slice is delicate (two representations of one
  syntax alive simultaneously — mitigated by dispatch ordering and the
  existing differential fuzzes); normal-form explanation tracking (T-B.2/T-B.7)
  is bookkeeping-heavy and must be built for the later proof story, not
  bolted on.
- **Revisited when:** T-B.4 first decides an unbounded instance (parser
  dual-build slice + scoreboard re-measure); Phase C regex derivatives need
  the automata-substrate ADR; P1.5 CDCL(T) lands and the bridge mode is
  replaced by a real `TheorySolver` integration.

## Foundational-DAG / register updates

- Add the word-equation procedure under the theory-solver layer of the
  foundational DAG (new public logic-fragment surface: unbounded QF_S/QF_SLIA
  sat).
- Close the P2.7 "word-level solver home" research-question entry with a link
  here.
