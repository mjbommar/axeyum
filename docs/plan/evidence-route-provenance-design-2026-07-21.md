# Evidence-route provenance design — 2026-07-21

Status: **causal-instrumentation prototype; implementation gate for proof work**

This note turns the generated
[uncertified shape census](generated/proof-gap-shape-census.md) into an
instrumentation plan. Operator presence identifies populations; it does not say
which refuter decided UNSAT, which certificate emitters declined, or where the
first uncertified transformation occurred. Those causal facts must be emitted by
the decision/evidence pipeline itself before a proof mechanism is selected.

## What direct code tracing established

`Evidence::Unsat(None)` is produced by several materially different paths:

| Decision path | Current `Provenance.backend` | Why a bare UNSAT can escape |
|---|---|---|
| Pure real fallback | `nra-linear-abstraction` | SOS, even-power, and linear proof routes decline; `check_with_nra` decides UNSAT without a transferable certificate |
| General mixed-theory fallback | `auto-solve` | Structural/Alethe/arithmetic/bounded certificates decline; under an explicit evidence timeout the expensive reduced-CNF proof is skipped |
| String text front door | `smtlib-string-front-door` | The sound string route decides UNSAT, but regex-emptiness and word-clash certificate upgrades decline; concat/length/other side-channel conflicts remain unserialized |
| QF_BV XOR fallback | SAT-BV backend identity | Interleaved XOR/CDCL can refute without an RUP-checkable artifact; this route already records explicit trust steps |

The 51 unique uncertified contents therefore cannot be treated as one Lean
reconstruction backlog. At minimum they contain NRA decision proofs, mixed
theory evidence-budget/coverage gaps, and string-side-channel conflicts.

### Audit semantic defect found during the trace

`Evidence::check` returns `Ok(true)` for `Evidence::Unsat(None)` and
`Evidence::Unknown`. That return means the no-certificate object is structurally
well formed; it is not an independent proof replay. The v1 dominance audit
called it directly on non-string rows, so 28 uncertified `bare-unsat` instances
were recorded as `evidence_checked=true`.

The v2 audit producer now:

- gates every independent check on `Evidence::is_certified()`;
- records `decision_backend` from existing provenance;
- records `evidence_check_mode` as one of
  `not-applicable-uncertified`, `internal-route-replay-only`, or
  `independent-recheck-attempted`; and
- retains Lean reconstruction as a separate axis, because Lean may independently
  reconstruct an original query even when the selected solver evidence is bare.

The generated proof-gap reports originally normalized the v1 artifacts to
**271**, not 299, independently checked certified outcomes. The eight affected
rows have now been rerun under v2: current artifacts report **267** certified
and independently checked outcomes, zero uncertified rows with
`evidence_checked=true`, and complete backend attribution for all 58 bare-UNSAT
occurrences. The reduction from 271 is not an accounting change: four QF_SEQ
rows now stably fall back from DRAT-with-`bit-blast`-trust to bare UNSAT.

A focused three-instance v2 smoke confirms the coarse seam without claiming
population prevalence:

| Exact instance | Decision backend | Evidence/check result |
|---|---|---|
| QF_NIA `pow2-native-3` | `auto-solve` | bare, uncertified, independently unchecked |
| QF_NRA `mult.01` | `nra-linear-abstraction` | bare, uncertified, independently unchecked |
| QF_S `str002` | `smtlib-string-front-door` | bare, uncertified, independently unchecked |

The audit example's unit test separately fixes the semantic invariant that a
structural `Ok(true)` on `Unsat(None)` is not an independent check. The three
smoke rows validated attribution wiring before the population refresh.

### Population refresh result

The release-profile v2 rerun covers the eight audit rows that contained every
historical bare-UNSAT occurrence: QF_AUFLIA, QF_NIA, QF_NRA, QF_S, QF_SEQ,
QF_SLIA, and two QF_UFLIA slices. Across 211 decided instances it preserves all
baseline verdicts with zero mismatches and zero timeouts; the two pre-existing
QF_NIA `IntPow2` proof-production errors remain. Coarse backend prevalence for
the 58 current bare outcomes is:

| Decision backend | Occurrences | Unique paths | Unique contents |
|---|---:|---:|---:|
| `smtlib-string-front-door` | 31 | 31 | 26 |
| `auto-solve` | 15 | 13 | 13 |
| `nra-linear-abstraction` | 12 | 12 | 12 |

This closes P0's population gate, but it does not identify which certificate
attempt declined inside `auto-solve` or the string front door. The rerun also
changed 22 timing-derived `dominant_candidate` flags, mostly in QF_SEQ, because
the audit recomputes one-shot timing against historical baseline cells. Verdict
and evidence denominators, rather than those unpaired timing flags, are the
appropriate evidence for this refresh.

## Proposed diagnostic schema

Do not add loose strings directly to the public `EvidenceReport` or enlarge the
existing `Provenance` struct ad hoc. Add a versioned diagnostic companion returned
by new, non-breaking explained entry points:

```rust
pub struct EvidenceTrace {
    pub version: EvidenceTraceVersion,
    pub decision_route: DecisionRouteId,
    pub source: SourceObligation,
    pub attempts: Vec<EvidenceAttempt>,
    pub selected_evidence: &'static str,
    pub checker: CheckerDisposition,
    pub first_uncertified: Option<UncertifiedBoundary>,
}

pub struct EvidenceAttempt {
    pub route: EvidenceRouteId,
    pub disposition: AttemptDisposition,
    pub input_obligation: ObligationId,
    pub output_obligation: Option<ObligationId>,
    pub reason: Option<ReasonCode>,
}
```

The ordinary APIs remain source-compatible:

```rust
pub fn produce_evidence_explained(...) -> Result<(EvidenceReport, EvidenceTrace), SolverError>;
pub fn produce_evidence_smtlib_explained(...) -> Result<(EvidenceReport, EvidenceTrace), SolverError>;

pub fn produce_evidence(...) -> Result<EvidenceReport, SolverError> {
    produce_evidence_explained(...).map(|(report, _trace)| report)
}
```

The exact ownership may be inverted internally to avoid allocating a trace for
ordinary calls. The compatibility requirement is observable equivalence of the
existing APIs and byte-identical evidence artifacts when tracing is disabled.

### Stable identifiers, not prose

Initial `DecisionRouteId` values should name semantic seams, not implementation
functions:

- `decision.qfbv.sat-bv`
- `decision.real.linear-or-nra`
- `decision.mixed.auto-solve`
- `decision.smtlib.string`

Initial `EvidenceRouteId` values should include:

- `evidence.nra.sos`
- `evidence.nra.even-power`
- `evidence.nra.bare`
- `evidence.string.regex-emptiness`
- `evidence.string.word-clash`
- `evidence.string.side-channel-bare`
- `evidence.mixed.zero-trust-alethe`
- `evidence.mixed.arithmetic-alethe`
- `evidence.mixed.structural`
- `evidence.mixed.bounded-int-blast`
- `evidence.mixed.reduced-cnf-drat`
- `evidence.mixed.bare`

`AttemptDisposition` is a closed enum:

- `selected`
- `declined-outside-fragment`
- `declined-no-refutation`
- `skipped-size-gate`
- `skipped-evidence-budget`
- `checker-rejected`
- `producer-error`

The distinction between “outside fragment” and “no refutation found” matters:
the former points to feature coverage; the latter points to proof-search depth.
Neither may be inferred later from the final evidence variant.

### Obligation identity

Every transformation-bearing attempt records both sides:

- exact input-file SHA-256 for text entry points;
- a deterministic canonical assertion fingerprint for arena entry points;
- a side-channel fingerprint for regex/word/length problems not represented in
  the ordinary term DAG;
- the output obligation fingerprint after each reduction; and
- the stable reduction ID connecting the two.

An `ObligationId` is an identity and reproducibility key, not a soundness claim.
The certificate/checker still has to establish that the reduction preserves the
required direction.

### First uncertified boundary

Every definitive result without a fully certified route must name exactly one
first boundary:

```text
decision-has-no-certificate-route
certificate-emitter-declined
certificate-skipped-evidence-budget
certificate-checker-rejected
source-side-channel-not-serialized
reduction-not-certified:<TrustId>
```

Later holes remain in `trusted_steps`; `first_uncertified` is the causal routing
key that prevents a long chain from being counted multiple times when ranking
work.

## Phased implementation

### P0 — Audit semantics and coarse backend attribution (landed)

- Correct the vacuous-check accounting.
- Emit existing `Provenance.backend` and explicit check mode in dominance v2.
- Refresh every row containing a historical bare UNSAT under schema v2.

Exit met: no uncertified evidence is reported as independently checked, and all
58 current bare outcomes carry a decision backend and explicit check mode.

### P1 — Trace the four bare-UNSAT exits

Instrument only the places that construct `Evidence::Unsat(None)`:

1. NRA fallback;
2. mixed-theory timeout/bare fallback;
3. string certificate-upgrade fallback; and
4. XOR fallback.

Record selected route, preceding certificate attempts, and first uncertified
boundary. Do not instrument every successful certificate emitter yet.

Exit: every bare UNSAT has a non-null stable route and first boundary; ordinary
API behavior remains byte-identical.

### P2 — Obligation fingerprints and reduction chain

Add source/assertion/side-channel fingerprints and input/output obligation IDs
to transformation-bearing attempts. Reuse deterministic writer/IR ordering;
do not hash Rust `Debug` output.

Exit: the same source/config reproduces an identical trace, and mutation of the
source or a reduced obligation changes the appropriate identity.

### P3 — Rerun and select mechanisms

Rerun the exact 51-content SHA set plus the eight reconstruction-only cases.
Generate raw-occurrence, path-deduplicated, and exact-content-deduplicated route
tables.

A proof mechanism is authorized only when:

- one causal route/boundary recurs in at least two independent source families;
- the proposed certificate covers both SAT/UNSAT soundness boundaries where
  relevant;
- an independent checker and Lean reconstruction path are specified before the
  public evidence variant ships; and
- the exact rerun improves certified/dominant coverage without changing verdicts.

## What this changes in the roadmap

The next proof task is **not** “implement the largest syntax family.” It is:

1. investigate the four stable QF_SEQ DRAT-to-bare regressions as a bounded
   trace case;
2. implement P1 tracing at the four bare exits;
3. regenerate the 51-content causal matrix; then
4. choose between NRA certificate work, string side-channel serialization, or a
   mixed-theory reduction proof based on route prevalence.

The eight already certified, checked, trust-free Lean reconstruction gaps remain
an independent, immediately actionable lane because their causal certificate
route is already known.
