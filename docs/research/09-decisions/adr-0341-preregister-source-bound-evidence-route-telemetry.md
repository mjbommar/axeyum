# ADR-0341: Preregister source-bound evidence-route telemetry

Status: proposed
Date: 2026-07-21

## Context

ADR-0005 requires every evidence artifact to retain enough source/query and
lowering provenance to replay a result against the original query. ADR-0050
adds verdict-invariant `RouteTrace` telemetry to `check_auto`, but that trace
ends at the decision dispatcher: it does not record which evidence producers
were attempted, which source obligation a lowered proof covers, which checker
ran, or the first uncertified boundary.

The current generated proof-gap matrix contains 327 baseline UNSAT decisions:
325 reproduce through evidence production, 267 are certified and independently
checked, 260 reconstruct in Lean, and 259 satisfy the full conjunction. The
remaining 58 bare-UNSAT occurrences reduce to 51 exact contents. All 58 now
carry a coarse decision backend, but `auto-solve` and
`smtlib-string-front-door` each bundle multiple evidence attempts and
fallbacks.

The schema-v2 refresh exposed why the missing layer matters. Four QF_SEQ audit
records created before the string evidence soundness fix credited DRAT over the
bounded/flat arena. The sound text front door correctly withdraws that credit:
all four use bounded sequence lowering, none has a word, regex-membership, or
length-skeleton certificate lane, and the DRAT does not certify the source-level
`seq.rev`, `seq.update`, or `seq.replace_all` obligation. The verdicts do not
change. The first missing boundary is `source-side-channel-not-serialized`, but
the current APIs cannot emit that fact.

This closes the open evidence-envelope follow-up in
[`research-questions.md`](../08-planning/research-questions.md) and implements P1
of the [evidence-route provenance design](../../plan/evidence-route-provenance-design-2026-07-21.md).

## Decision

**Add a versioned, source-bound evidence trace through an optional recorder on
the existing evidence-production path, while leaving `RouteTrace` as the
decision-dispatch trace and preserving all existing APIs as recorder-free
wrappers.**

The proposed diagnostic surface is:

```rust
pub fn produce_evidence_explained(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<(EvidenceReport, EvidenceTrace), SolverError>;

pub fn produce_evidence_smtlib_explained(
    input: &str,
    config: &SolverConfig,
) -> Result<(EvidenceReport, EvidenceTrace), SolverError>;
```

`produce_evidence` and `produce_evidence_smtlib` remain source-compatible thin
wrappers over the same internal producer with no recorder. Recording must never
participate in a branch condition, mirroring ADR-0050's structural
verdict-invariance guarantee.

`EvidenceTrace` v1 contains typed, closed identifiers for:

- the source obligation: canonical assertion fingerprint for arena entry or
  exact input SHA-256 plus parser-side-channel inventory for SMT-LIB entry;
- the decisive solver route already exposed by `Provenance.backend`;
- each evidence attempt, its input/output obligation identity, and one of
  `selected`, `declined-outside-fragment`, `declined-no-refutation`,
  `skipped-size-gate`, `skipped-evidence-budget`, `checker-rejected`, or
  `producer-error`;
- the selected evidence kind and checker disposition; and
- exactly one first uncertified boundary for every definitive result that lacks
  a fully certified route.

Initial first-boundary variants are:

- `decision-has-no-certificate-route`;
- `certificate-emitter-declined`;
- `certificate-skipped-evidence-budget`;
- `certificate-checker-rejected`;
- `source-side-channel-not-serialized`; and
- `reduction-not-certified(TrustId)`.

Stable enum/route IDs are serialized; Rust `Debug` strings and implementation
function names are not identities. Obligation fingerprints use deterministic
source bytes or canonical writer/IR order, never hash-map order or `Debug`
output.

The first implementation instruments only the four existing bare-UNSAT exits:
NRA fallback, mixed-theory fallback, string certificate-upgrade fallback, and
QF_BV XOR fallback. Successful evidence families may initially record only the
selected route and checker; exhaustively tracing every successful emitter is a
later measurement-gated extension.

## Preregistered acceptance gates

1. On the exact 58-occurrence bare population plus the eight certified,
   checked, trust-free reconstruction-only rows, explained and ordinary APIs
   return equal `EvidenceReport`s, including byte-identical serialized evidence.
2. Two explained runs over every registered row produce byte-identical traces.
3. Every definitive bare result records a non-null decision route, ordered
   evidence attempts, source obligation, and exactly one first uncertified
   boundary.
4. The four stale QF_SEQ cases record
   `source-side-channel-not-serialized`; none may claim that the bounded DRAT
   proves the source obligation.
5. Source-byte mutation changes the source identity; a canonical-assertion
   mutation changes the arena identity; neither mutation may change a stable
   route ID merely because term allocation order changed.
6. Certified evidence records the checker that was actually attempted. Bare
   `Unsat(None)` remains `not-applicable-uncertified` and cannot acquire an
   independent-check credit through tracing.
7. Existing focused evidence, route-trace, dominance, parser-census, formatting,
   Clippy, rustdoc, and documentation-link gates pass under the existing bounded
   job policy.

Acceptance of this ADR authorizes telemetry only. It does not authorize a new
proof mechanism, routing reorder, evidence timeout change, or public default.

## Evidence

- The generated proof-gap census attributes all 58 bare occurrences to three
  coarse backends: 31 string front door, 15 `auto-solve`, and 12 NRA fallback.
- All 26 residual string/sequence contents use bounded lowering; three are
  word-only fallbacks. The parser-backed diagnostic binds those facts to source
  SHA-256 values and exact parser state.
- Git lineage proves the QF_SEQ audit predates the string evidence soundness
  correction: `9d12953c` created it, `f719c27d` fixed the text evidence boundary,
  and `64238437` refreshed only QF_S/QF_SLIA.
- ADR-0050 already validates the optional-recorder pattern with a single shared
  dispatch, differential verdict invariance, and deterministic traces.

## Alternatives

- **Reuse `RouteTrace` unchanged.** Rejected: it describes decision dispatch on
  an already-lowered arena and cannot represent source obligations, evidence
  attempts, reductions, or checkers without conflating two different layers.
- **Infer the missing proof rule from syntax or final `Evidence` variants.**
  Rejected: one backend/final variant bundles multiple causal paths, and the
  QF_SEQ stale credit demonstrates that lowered syntax can hide the source
  obligation.
- **Add loose strings to `Provenance` or the dominance JSON only.** Rejected:
  that duplicates routing logic outside the producer, lacks typed stability,
  and cannot preserve input/output obligation identities.
- **Instrument every successful certificate emitter immediately.** Deferred:
  the 58 bare outcomes are the measured blocker; broad instrumentation adds
  churn before the minimal schema and invariance gates are proven.

## Consequences

The proof backlog can be ranked by the actual first uncertified boundary rather
than by operator co-occurrence. Source-level and lowered obligations become
explicit, preventing bounded proofs from being credited as unbounded source
certificates. The cost is a new versioned diagnostic contract and recorder
plumbing through four evidence exits. After the exact rerun, a separate ADR is
still required for any new certificate family or source-to-lowered checker.
