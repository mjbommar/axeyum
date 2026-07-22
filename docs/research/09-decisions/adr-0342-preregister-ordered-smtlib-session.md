# ADR-0342: Preregister an ordered transactional SMT-LIB 2.7 session

Status: proposed
Date: 2026-07-21

## Context

P4.4's machine-readable command/API census shows broad parser and direct-helper
coverage but zero ordered textual-session outputs. The first planning response
was to add a session runner over the existing `ScriptCommand` sequence. A
source-and-standard audit shows that boundary is insufficient.

The official SMT-LIB 2.7 standard makes assertions, declarations, definitions,
options, execution modes, query snapshots, and responses part of one ordered
state machine. Declarations and definitions are scoped by `push`/`pop` by
default; `reset-assertions` removes non-global declarations; output-related
options affect the response of the command that sets them; and continued
execution after an error requires the semantic state to remain unchanged.

Axeyum currently parses a whole script into one shared `TermArena`. Assertion
operations and checks are ordered, but most output requests are no-ops or final
side fields, options collapse into a final map, declarations stay global, full
reset is rejected, and pop underflow is silently ignored. Direct helper APIs
then reparse and reconstruct a selected/final assertion stack. Rendering those
values would not establish protocol conformance. A further mismatch is explicit
in `CheckResult`: only `Sat` carries a model, while SMT-LIB places both `sat` and
`unknown` in its sat query mode and permits model inspection there.

This ADR addresses the open Formats question in
[`research-questions.md`](../08-planning/research-questions.md) and is backed by
the [session contract design](../../plan/smtlib-session-contract-design-2026-07-21.md),
the [machine-readable prototype](../../plan/smtlib-session-contract-v1.json),
and its [generated transcript matrix](../../plan/generated/smtlib-session-contract.md).

## Decision

**Pin the interactive compatibility target to the official SMT-LIB 2.7 release
dated 2025-07-07, select continued-execution error behavior, and implement one
ordered transactional session whose typed events are the sole future source of
textual responses and convenience-helper snapshots.**

The proposed architecture has five explicit boundaries:

1. `SessionEpoch` owns one `TermArena`, parser/theory registries, and
   deterministic declaration identities. Full `reset` atomically replaces the
   epoch; no `TermId`, model, or proof crosses it.
2. `ScopeFrame` owns assertions plus default-scoped declarations, definitions,
   sort aliases, macros, and named bindings. External names resolve through the
   visible frames to fresh internal identities; popped names may be redeclared.
3. `QuerySnapshot` binds the exact assertion context, one-shot assumptions,
   verdict, model, evidence, and route to one query ID. Output commands inspect
   or lazily complete that immutable snapshot and never re-solve final script
   state.
4. A command is parsed/validated against an immutable state view, then either
   commits one delta and event or emits one error event with no semantic delta.
5. The pure session core returns typed `SessionEvent`/`SessionResponse` values
   plus frozen output-route metadata. CLI/file/process I/O is an adapter concern
   so native library, CLI, tests, and WASM share semantics.

For full `reset`, an enabled `success` response is formed from the pre-reset
`:print-success` and regular-channel snapshot, then the fresh epoch/default
options take effect. This matches the bounded local Bitwuzla probe and avoids
making the reset response disappear as a side effect of resetting the flag.

Implementation is staged. S1 captures a complete ordered command/event IR
without switching behavior. S2 adds exact query snapshots and ordered typed
outputs for the existing assertion subset. S3 adds scoped signatures and reset
epochs. S4 enforces options and renders canonical text. S5 exposes categorical
commands and converges compatibility helpers onto the same engine. Acceptance
of this ADR authorizes S1 only; each later slice must pass its own gates before
the next starts.

## Preregistered acceptance gates

1. `scripts/gen-smtlib-session-contract.py --check` validates 14 invariants,
   20 fixtures, and 107 abstract commands with zero transcript mismatch.
2. S1 records every currently accepted command in exact order with stable
   command/epoch identities, while all existing `solve_smtlib*` results remain
   byte/value-identical.
3. S2's output events identify the exact preceding query; adversarial
   sat/unsat/sat, push/pop, assumption, option-update, and repeated-output
   scripts cannot observe a later query or final global field.
4. S3 passes paired default/global declaration fixtures across `pop` and
   `reset-assertions`, redeclaration-after-pop, full-reset epoch isolation, and
   pop-underflow/duplicate/use-after-pop state-atomicity mutations.
5. Every definitive query snapshot preserves the existing model replay and
   evidence checker requirements. Proof retrieval after nonempty assumptions is
   rejected before invoking an emitter.
6. The post-unknown model-inspection policy is explicit and deterministic. It
   either returns a well-sorted inspection model tied to that unknown query or a
   visibly labeled unsupported deviation; it never reuses a previous sat model.
7. S4 reproduces the committed transcripts byte-for-byte through an in-memory
   sink and differentially matches Z3 plus Bitwuzla on the common standard
   subset. Differences are classified; no solver output is silently rewritten
   into agreement.
8. Two same-input/same-seed runs emit byte-identical event sequences and text.
9. The existing 30-row command/API matrix, parser/solver suites, formatting,
   Clippy, rustdoc, WASM profile, and documentation-link gates pass under the
   repository's bounded job policy.
10. `solve_smtlib*` wrappers converge onto the session engine only after their
   compatibility return values are proven equivalent; no permanent second
   scope/query interpreter is accepted.
11. Documentation labels exact protocol, theory, proof, and performance scopes
    separately. Passing session tests grants no new theory or speed claim.

## Evidence

- The official
  [SMT-LIB 2.7 reference](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf)
  provides the mode, response, scope, option, reset, and query-inspection
  requirements used by the prototype.
- The current source facts are checked directly by the generator: narrow
  `ScriptCommand`, final option/request side fields, output no-ops, shared-arena
  reset rejection, global declaration behavior, silent pop underflow,
  model-less `Unknown`, and the absence of a public session ABI.
- Bounded local Bitwuzla 0.9.1 probes at clean checkout
  `8d1eb01093ae54d9b4586456b69c3bf31000a4c2` reproduce the standard-critical
  declaration lifetime, option gate, print-success, reset-assertions, and exit
  behavior.
- Z3 command-context source at commit `c9a4a5907dc86511cba1f788b01333ecd8968e45`
  independently demonstrates scoped declaration stacks and explicit response
  state, without being treated as the specification.
- The abstract prototype passes 20 deterministic traces / 107 commands and
  includes nine deliberate errors whose subsequent commands prove continued
  execution.

## Alternatives

- **Add a renderer around existing helper APIs.** Rejected: helpers lose command
  chronology, query identity, option timing, and default declaration scope.
- **Extend `ScriptCommand` only with output variants.** Rejected: declarations,
  definitions, options, parser environments, and reset epochs are also ordered
  semantic state.
- **Make all declarations permanently global.** Rejected: it could be a
  documented nonstandard profile, but cannot satisfy the pinned default
  contract or neutral differential fixtures.
- **Rollback `TermArena` on pop.** Rejected as the default design: destructive
  rollback complicates stable IDs and outer-term references. A scoped external
  name environment over fresh internal identities preserves inert arena nodes.
- **Write output directly inside the parser/solver.** Rejected: it couples
  semantics to process I/O, harms WASM/library use, and makes error/output tests
  less deterministic.
- **Use immediate-exit error behavior.** Rejected for the proposed public
  session because continued execution is more useful for embedders and makes
  atomicity explicit. A CLI may still offer an outer stop-on-first-error policy.
- **Implement every missing SMT-LIB command in the same change.** Rejected: the
  state boundary must become trustworthy before recursive definitions,
  categorical commands, or general SyGuS add semantic breadth.

## Consequences

The work is now correctly sized as a protocol/state refactor rather than a text
formatting task. It adds deterministic identities and explicit mapping at the
parser/model/render boundaries, but those maps make scope, reset, replay, and
evidence ownership auditable.

The existing whole-script benchmark parser can remain as a compatibility facade
during S1/S2. Whole-script theory pre-scans and the word-only fallback must be
incrementalized or explicitly declined before S3 is called conforming. Direct
helpers remain available, but their independent scope reconstruction becomes
temporary migration debt with a named removal gate.

No production behavior, public API, theory support, proof coverage, or
performance claim changes while this ADR remains proposed.
