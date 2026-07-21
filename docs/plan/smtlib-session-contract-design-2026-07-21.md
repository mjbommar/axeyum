# Ordered SMT-LIB session contract — design and gap audit

Date: 2026-07-21

Status: **prototype complete; Rust implementation not yet authorized**

Track: [P4.4 SMT-LIB command/API conformance](track-4-usecases-frontend/P4.4-smtlib-surface.md)

Decision: [proposed ADR-0342](../research/09-decisions/adr-0342-preregister-ordered-smtlib-session.md)

## Executive result

The missing product boundary is larger than a text renderer but smaller than a
new solver engine. Axeyum already has many useful one-shot and incremental Rust
helpers. It does **not** yet have the state machine those helpers need in order
to behave like one SMT-LIB process.

The critical discovery is signature scope. Under
[SMT-LIB 2.7](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf),
declarations and definitions are part of the current assertion level by
default: they disappear on `pop`, and `reset-assertions` removes them unless
`:global-declarations` was enabled in start mode. Axeyum currently interns all
declarations into one shared arena and keeps them global. Therefore a conforming
session cannot be implemented by replaying the existing `ScriptCommand` list
and printing the current helper return values.

The committed prototype makes the control-plane contract executable before any
Rust API is frozen:

- [machine-readable contract](smtlib-session-contract-v1.json);
- [generated invariant and transcript matrix](generated/smtlib-session-contract.md);
- `scripts/gen-smtlib-session-contract.py`, a small abstract state machine that
  checks 14 invariants and 20 fixtures / 107 commands byte-for-byte; and
- source assertions that fail when the current implementation facts change.

This is planning evidence, not a conformance claim. The abstract model does not
parse terms, solve formulas, construct proofs, or perform I/O.

## Evidence base

### Standard

The contract is pinned to the official SMT-LIB 2.7 release dated 2025-07-07.
The load-bearing requirements are:

| Topic | Standard requirement | Why it matters here |
|---|---|---|
| execution modes | start, assert, sat, and unsat; invalid-mode commands error; `exit` is always legal | output helpers need a query mode, not merely a parsed request bit |
| command responses | specific results are ordered; optional `success` is controlled by `:print-success`; errors use a regular-channel response | one final aggregate cannot represent a session transcript |
| error behavior | continued execution must leave semantic state unchanged after an error | parse/mutation must be transactional |
| assertion stack | assertions, declarations, and definitions inhabit levels | scoping only formula terms is insufficient |
| declarations | local by default; `:global-declarations true` makes later declarations permanent | the current shared-arena/global-name behavior is not the default protocol |
| option timing | output-related options affect the response to the command that sets them | a response must snapshot its route after option commit |
| query inspection | model/value/assignment or proof/core/assumption requests inspect the most recent check result | helpers may not reconstruct and solve the final script state |
| reset | full reset restores startup state; `reset-assertions` preserves options but conditionally removes declarations | full reset needs an arena epoch; the two reset commands are not synonyms |

### Reference implementation probes

The clean local Bitwuzla 0.9.1 checkout at
`8d1eb01093ae54d9b4586456b69c3bf31000a4c2` and executable at
`references/bitwuzla/build/src/main/bitwuzla` were probed with bounded SMT-LIB
scripts:

- `:print-success true` affects its own command and `exit` prints `success`
  before termination;
- `get-model` without `:produce-models true` fails rather than returning a
  model;
- a declaration introduced after `push` is undefined after `pop` by default;
- `reset-assertions` removes a default-scoped declaration but preserves one
  created after `:global-declarations true`; and
- full `reset` prints its enabled success response, then clears startup state.

These probes are corroboration, not the specification. Z3's command-context
source at commit
[`c9a4a590`](https://github.com/Z3Prover/z3/tree/c9a4a5907dc86511cba1f788b01333ecd8968e45/src/cmd_context)
likewise maintains scoped declaration stacks and explicit response/output
state. Axeyum should implement the standard contract in its own types rather
than clone either solver's internals.

## Current data flow and why it cannot carry a transcript

```text
whole input bytes
  -> read_all + whole-script pre-scans/desugarings
  -> parse_command mutates one Script + one TermArena
       assertions/push/pop/check/get-assertions -> ordered ScriptCommand
       options/info/get-* requests             -> final maps, vectors, booleans
       declarations/definitions                -> shared arena + global parser maps
       echo/exit/core/proof/assignment/...      -> accepted no-op or side flag
  -> one helper reparses the whole script
  -> helper reconstructs one final or selected assertion stack
  -> Rust value (not an ordered textual response)
```

Eight source-checked findings are recorded in the generated prototype. The
highest-impact gaps are:

1. **No complete command IR.** `ScriptCommand` records assertion-stack changes,
   checks, and `get-assertions`, but not the rest of the protocol.
2. **Final-state collapse.** `set-option` values end in one map and requests in
   separate lists, so a request can observe a later update.
3. **Signature mismatch.** declarations, macros, sort aliases, and `:named`
   bindings are global parser maps instead of scope-frame members.
4. **No arena rollback/name shadowing.** a popped external name must be
   redeclarable, but a globally interned raw symbol name cannot safely model
   that lifecycle.
5. **Full reset is structurally unavailable.** one `TermArena` owns the entire
   parsed input.
6. **Errors are not transactional.** pop underflow is silently ignored by the
   incremental helper.
7. **Whole-script theory pre-scans remain.** sequence and finite-field
   registries plus the word-only fallback currently assume all commands are
   available before execution. A streaming session must make these registries
   epoch-local and incremental or explicitly decline the affected command.
8. **`unknown` has no model payload.** SMT-LIB enters its sat query mode after
   either `sat` or `unknown`, but Axeyum's `CheckResult::Unknown` carries only a
   reason. The implementation must choose a deterministic well-sorted
   inspection model for unknown or label that part of the protocol unsupported;
   it must not reuse a stale sat model.

## Proposed Rust contract

The public boundary should be typed events, not a writer and not a vector of
strings. Names are illustrative until ADR-0342 is accepted.

```rust
pub struct SmtLibSession {
    next_command_id: u64,
    epoch: SessionEpoch,
    mode: SessionMode,
    options: SessionOptions,
    global_env: NameEnv,
    scopes: Vec<ScopeFrame>,
    last_query: Option<QuerySnapshot>,
}

pub struct SessionEpoch {
    id: u64,
    arena: TermArena,
    next_declaration_id: u64,
    theory_parse_state: TheoryParseState,
}

pub struct ScopeFrame {
    assertions: Vec<NamedAssertion>,
    declarations: NameEnv,
    definitions: DefinitionEnv,
}

pub enum SessionMode {
    Start,
    Assert,
    SatLike(QueryId), // the standard places both sat and unknown here
    Unsat(QueryId),
    Terminated,
}

pub struct QuerySnapshot {
    epoch: EpochId,
    id: QueryId,
    context_generation: u64,
    assertions: Vec<TermId>,
    assumptions: Vec<TermId>,
    result: CheckResult,
    model: Option<Model>,
    evidence: LazyCheckedEvidence,
    route: RouteTrace,
}

pub struct SessionEvent {
    command_id: CommandId,
    epoch: EpochId,
    mode_before: SessionModeTag,
    mode_after: SessionModeTag,
    response: Option<SessionResponse>,
    output: Option<OutputRouteSnapshot>,
}

pub enum SessionResponse {
    Success,
    CheckSat(CheckResult),
    Assertions(Vec<RenderedTerm>),
    Assignment(Vec<(String, bool)>),
    Model(SmtLibModel),
    Values(Vec<(RenderedTerm, Value)>),
    Info(InfoResponse),
    Option(OptionValue),
    Proof(CheckedProofArtifact),
    UnsatAssumptions(Vec<RenderedTerm>),
    UnsatCore(Vec<String>),
    Echo(String),
    Unsupported,
    Error(SessionError),
}
```

`SatLike` is deliberately not spelled `Sat`: it includes the standard's
post-`unknown` query mode. `QuerySnapshot.model == None` after unknown is an
explicit unresolved protocol obligation. Before conformance is claimed, the
implementation must either build a deterministic well-sorted inspection model
permitted for unknown results or return a visibly scoped unsupported response
and record the deviation in the matrix. A previous sat model is never eligible.

### Identity and name handling

External SMT-LIB names must be separated from arena identity. Each declaration
gets a deterministic `(epoch, declaration_id)` internal identity and a retained
external spelling. Name resolution consults the visible scope frames; `pop`
removes the binding without deleting the inert arena nodes. Redeclaring the same
external name later creates a new internal identity. Model and proof renderers
use the retained external binding appropriate to the query snapshot.

This avoids adding destructive rollback to `TermArena`, preserves lifetime-free
`TermId`, and makes full reset a cheap replacement of the entire `SessionEpoch`.
It does require an explicit mapping at every parser/model/render boundary; that
mapping is a correctness asset, not optional bookkeeping.

### Transaction boundary

One command executes in four stages:

1. read exactly one S-expression and assign a command ID;
2. parse, resolve, sort-check, and validate mode/options against an immutable
   view of session state;
3. commit one state delta and construct one typed response plus frozen output
   route; or emit an error with no semantic delta; and
4. let an outer adapter render/write the response.

No parser mutation is visible before stage 3. Solver calls occur only after the
query snapshot is fully assembled. A proof may be generated lazily, but only
from the immutable snapshot and never by reparsing/re-solving the script's final
state.

### I/O boundary

The session core must not open files, switch process streams, or terminate the
process. `OutputRouteSnapshot` represents `stdout`, `stderr`, or a validated
file target. The CLI owns actual writes and process exit; library and WASM users
consume events in memory. This retains one semantic implementation across all
deployment profiles and makes transcript tests deterministic.

## Migration plan

The implementation should land in narrow, independently reviewable slices.

### S0 — Contract freeze (this prototype)

- Pin SMT-LIB 2.7.
- Review the 14 invariants and 20 abstract transcripts.
- Decide the reset-response snapshot policy and continued-execution policy in
  ADR-0342.

Exit: the generator is checked in CI and no Rust behavior is claimed.

### S1 — Complete command/event IR, no behavior switch

- Add internal `ParsedCommand`, `SessionEvent`, `SessionResponse`, mode tags,
  IDs, and pure render traits.
- Make the parser retain every currently accepted command in order.
- Keep existing public helpers as the production route.

Exit: parse-only fixtures reproduce command identity/order twice byte-for-byte;
the existing helpers are behavior-identical.

### S2 — Query snapshots and ordered output for the existing semantic subset

- Execute assertions, checks, push/pop, assumptions, and existing output
  helpers through one internal runner.
- Store the exact result/model/evidence context at each check.
- Emit in-memory typed events; do not yet claim scoped-declaration conformance.

Exit: multi-query fixtures prove that every output binds to the correct query;
ordinary and session solving have identical verdict/model replay.

### S3 — Scoped name environment and reset epochs

- Move declarations, definitions, sort aliases, macros, and named bindings into
  scope frames.
- Introduce external-name to internal-identity mapping.
- Implement default/global declaration behavior, atomic pop underflow,
  `reset-assertions`, and full `reset` with a fresh epoch.
- Incrementalize or explicitly decline whole-script theory pre-scan paths.

Exit: default/global paired transcripts pass; popped names can be redeclared;
no ID crosses reset; source mutation/error tests prove state atomicity.

### S4 — Option enforcement and canonical textual adapter

- Enforce start-only and produce-* options at the command point.
- Render all admitted standard responses as valid S-expressions.
- Add CLI channel routing and an in-memory/WASM sink.

Exit: the committed transcript corpus passes byte-for-byte in Rust and against
at least two neutral solver CLIs on the shared standard subset; divergences are
classified rather than normalized away.

### S5 — Categorical adapters and compatibility facade convergence

- Add textual interpolation, Horn, and abduction commands only after their
  syntax/ordering contracts are explicit.
- Move `solve_smtlib*` convenience helpers onto the same session engine, keeping
  source-compatible return types where possible.
- Update the 30-row API matrix from source/test evidence.

Exit: there is one command semantics implementation. No direct helper and
session runner may independently reconstruct scopes or query state.

## Acceptance gates before calling the session conforming

1. All 20 prototype fixtures are represented by exact Rust transcript tests.
2. A generated mode/command cross-product proves every admitted transition and
   wrong-mode error.
3. Every error fixture proves full semantic-state equality before/after.
4. Default and global declaration lifetimes match the standard under pop and
   both reset commands, including redeclaration after removal.
5. Every model/value/assignment/proof/core/assumption artifact names the exact
   query ID and passes its existing replay/checker gate.
6. Two same-seed runs produce byte-identical events and rendered output.
7. Z3 and Bitwuzla transcript differentials agree on the common standard
   subset; solver-specific deviations are retained as labeled evidence.
8. Existing `solve_smtlib*` tests and the 30-row conformance generator pass
   before and after facade convergence.
9. Default, `qfbv`, full, and WASM profiles preserve the no-C/C++ default and
   no-unsafe invariants.
10. Documentation says **session conformance** only for the tested subset; it
    does not convert this protocol work into a theory-coverage or performance
    claim.

## Explicit non-goals

- No new theory engine, proof rule, or solver routing policy.
- No promise of full SyGuS, recursive definitions, or parametric sorts from the
  session refactor alone.
- No requirement that interactive execution retain a warm backend; semantic
  session correctness comes first and performance remains separately measured.
- No direct filesystem I/O in the semantic core.
- No compatibility claim based solely on parsing commands or returning a Rust
  helper value.

## Immediate next action

Review proposed ADR-0342 and the machine-checked traces. If accepted, implement
S1 only: complete ordered command/event capture without switching public solver
behavior. The signature-scope discovery makes a renderer-first patch actively
misleading; it would produce plausible text for the wrong context semantics.
