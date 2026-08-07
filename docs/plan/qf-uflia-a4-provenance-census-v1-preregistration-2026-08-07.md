# QF_UFLIA A4 provenance recovery and causal census v1 preregistration

Date: 2026-08-07  
Status: preregistered; capture and solver changes have not started

## Decision and scope

A4 starts by repairing its evidence boundary, not by changing the solver.  The
retained parity ledger names a complete per-file sidecar, but that ignored file
was not committed and no surviving copy has been found.  Aggregate prose is not
enough to reconstruct which 86 files cvc5 decided and Axeyum did not.  This
slice therefore authorizes only:

1. a deterministic reference-capture adapter and census validator;
2. one fresh, complete current-main capture of Axeyum route traces and plain
   cvc5 outcomes over the frozen list;
3. retention of the exact-path sidecar, complete traces, manifest, and causal
   census; and
4. selection of a later bounded mechanism cluster if every gate below passes.

It authorizes no production solver edit, route reorder, timeout/cap increase,
recursive MBQI experiment, or unchecked SAT credit.  Any mechanism selected by
the census requires a separate preregistration before implementation.

## Frozen population and historical claim

The source boundary inspected before this document is
`770ce20dc31520483de9a2d6c272f1266b42f03b`.  The capture harness will be
implemented only after this preregistration is committed and pushed; the result
must identify the later exact harness commit and prove that its solver-relevant
source is clean.

| Item | Frozen value |
|---|---|
| List | `bench-results/parity-lists/QF_UFLIA.txt` |
| List SHA-256 | `f88e67890fae78fb27bb35ecc0f19532dc3bc77fd7f1ac7453fcda343b36fb35` |
| Ordered nonempty rows | 200 |
| Axeyum configuration | shipped default; 24,000 ms per query |
| Reference | `/nas3/data/axeyum/harness/bin/cvc5` |
| Reference version | `cvc5 1.3.4 [git f3b21c4 on branch HEAD]` |
| Reference binary SHA-256 | `7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee` |
| Reference options | none; plain invocation, not a competition portfolio |
| Per-file wall/memory budget | 24 seconds / 8 GiB; 5-second outer kill margin |
| Retained aggregate to reproduce | Axeyum 94/200; cvc5 180/200; both 94; Axeyum-only 0; reference-only 86; disagreements 0 |
| Historical missing sidecar hash | `921299a93e2895d59741115036150156e7a294d8182f5e2e46086b9330c00b78` |

The historical sidecar hash is context, not a required byte-for-byte target:
the old file may have used basenames and came from solver commit `71ca85d9f`.
The fresh file must use exact committed-list paths and current route telemetry.
Its verdict matrix, however, must reproduce the retained aggregate exactly.

## Harness boundary and execution protocol

The harness increment must be committed and pushed before either full stream is
captured.  It may add nonproduction tooling under `scripts/` and tests, but must
not alter `crates/axeyum-solver`, the shipped CLI, any solver default, or the
frozen list.  The result records:

- exact Git commit and clean solver-source check;
- SHA-256 and byte size of the release `explain_corpus` executable;
- exact cvc5 version, SHA-256, and byte size;
- list SHA-256 and row count;
- command lines, timeout and memory settings;
- UTC start/end times and `/proc/loadavg` at both boundaries; and
- SHA-256 for each retained raw and derived artifact.

The two streams are:

1. **Axeyum:** release `explain_corpus --list
   bench-results/parity-lists/QF_UFLIA.txt 24000 --json`, with the whole process
   under the 8 GiB memory wrapper and a bounded outer deadline.  It runs once;
   its output is both the scored Axeyum verdict stream and the trace stream.
2. **Reference:** the new adapter visits the same list in the same order and
   invokes plain cvc5 as `cvc5 --tlimit=24000 FILE`, under the established 8 GiB
   memory wrapper and 29-second outer wall limit per file.  It records a typed
   outcome and elapsed milliseconds for every row; stderr is diagnostic and
   cannot be interpreted as a verdict.

Start only when one-minute load is at most 12 on this 24-core host and no other
Axeyum measurement/build process owned by this lane is running.  The streams are
serialized, not run against each other.  A later load rise is retained in the
manifest; exact aggregate reproduction remains the acceptance test.  Do not
resume from a partial stream.  An interruption discards that stream and the
next attempt restarts it from row one.

## Complete-record predicate

Before looking at causal counts, the validator must reject unless all of the
following are true:

1. Each raw stream is valid JSONL with exactly 200 records, in byte-for-byte
   list order, with no blank, missing, duplicate, or extra path.
2. Every Axeyum record has `status="decided"`, a verdict in
   `{sat,unsat,unknown}`, and a `trace` whose `schema_version` is exactly 1 and
   whose ordered `attempts` array is nonempty.  `word-first-fallback`,
   `ingest-resource-limit`, `skipped-scoped`, read/parse errors, and generic
   errors all fail this v1 capture because they do not provide the required
   complete route record.
3. Every reference record has one typed outcome in
   `{sat,unsat,unknown,timeout}`.  `unknown` requires a clean cvc5 exit and an
   exact standalone `unknown` response.  Timeout is the outer deadline or its
   corresponding terminated child.  A signal, memory-limit exit, nonzero exit,
   missing/multiple verdicts, malformed output, or adapter error invalidates
   the capture rather than silently becoming `unsolved`.
4. The validator independently extracts each benchmark's first declared
   `:status` token after removing comments and quoted/string content.  A
   decided Axeyum or cvc5 verdict that conflicts with a declared `sat`/`unsat`
   status invalidates the capture.  If both decide, their verdicts must agree.
5. Counting only `sat`/`unsat` as solved reproduces exactly: Axeyum 94,
   reference 180, both 94, Axeyum-only 0, reference-only 86, and zero
   disagreements.  `unknown` and `timeout` remain distinct in the raw stream
   but both are unsolved in the parity sidecar.

Failure of any item stops A4 before causal classification.  Do not weaken this
predicate, infer rows from the historical aggregate, or select a mechanism from
an incomplete or drifted run.

## Retained artifacts

After validation, retain and commit these deterministic outputs:

- `bench-results/parity-details/QF_UFLIA.tsv`: header plus exactly 200 ordered
  rows, with exact path, Axeyum parity verdict, reference parity verdict, and
  declared status.  `unknown`/`timeout` normalize to `unsolved` only in this
  compatibility sidecar.  The path is intentionally force-added despite the
  general `parity-details/` ignore rule.
- `docs/plan/evidence/qf-uflia-a4/axeyum-traces-v1.jsonl`: the complete validated
  Axeyum stream, preserving every schema-1 trace.
- `docs/plan/evidence/qf-uflia-a4/reference-outcomes-v1.jsonl`: the complete
  typed cvc5 stream.
- `docs/plan/evidence/qf-uflia-a4/reference-only-v1.txt`: the 86 exact paths in
  frozen-list order.
- `docs/plan/evidence/qf-uflia-a4/causal-census-v1.json`: the deterministic
  per-case census and aggregate buckets below.
- `docs/plan/evidence/qf-uflia-a4/capture-manifest-v1.json`: identities,
  commands, budgets, load/times, counts, and artifact hashes.

The validator writes temporary files first and atomically replaces derived
artifacts only after the complete-record and aggregate gates pass.  Raw streams
from a failed attempt stay outside the repository and receive no evidence
credit.

## Frozen causal extraction

Only the validated 86 reference-only rows enter the causal census.  Every case
retains its exact path, declared/Axeyum/reference outcomes, full trace, source
quantifier flag, first substantive decline, terminal substantive decline, and
coarse bucket.  A **substantive decline** is a trace attempt with
`outcome="declined"` whose reason is neither `unsupported` nor
`not-applicable`; probe entries and decided entries are not declines.  First
and terminal mean ordered first and last among that filtered sequence.  A
reference-only trace with no substantive decline invalidates the census.

The primary lossless grouping key is the exact tuple:

`(terminal route, reason, kind-or-null, normalized-detail-family)`.

Normalization lowercases ASCII, replaces decimal/hex quantities and paths with
placeholders, collapses whitespace, and otherwise preserves words and
punctuation.  Both the unmodified detail and normalized family are retained, so
normalization can group observations but cannot erase evidence.

The required coarse bucket is assigned by the first matching rule, in this
fixed order:

1. `quantifier-discovery`: the SMT-LIB token stream contains `forall` or
   `exists`, or any trace detail explicitly reports a quantifier.
2. `replay`: any substantive decline is `verifier-rejected`, or its detail
   contains `replay`, `re-check`, `verify`, `verification`, `original
   assertion`, or `rejected candidate`.
3. `uf-model-construction`: any substantive UF/EUF route detail contains
   `model`, `candidate`, `reconstruct`, `projection`, `function table`, or
   `assignment`.
4. `budget-routing`: the terminal substantive decline has reason `budget`, or
   kind in `{timeout,resource-limit,memory-limit,node-budget,encoding-budget}`.
5. `arithmetic-participation`: the terminal route is `uf-arith-online`,
   `uf-arithmetic`, `uf-arith-lazy-overbound`,
   `uf-arith-lazy-overbound-pre-lia`, or an integer/LIA route; or its detail
   contains `arith`, `lia`, `simplex`, `branch-and-bound`, `gomory`, `farkas`,
   or `integer`.
6. `uf-model-construction`: the terminal route begins with `uf` or `euf` and
   was not classified above.

Any row that reaches no rule is emitted as `unclassified`; a nonempty
`unclassified` bucket fails v1 and prevents cluster selection.  The repeated
last bucket deliberately groups residual UF congruence/search incompleteness
with the requested UF-model surface while the lossless tuple preserves the
more precise route and detail family.

## Selection and later experiment gates

This census may select a next cluster only when at least three reference-only
rows share the same lossless grouping key and reference verdict.  Selection is
by descending group size, then bucket name, route, reason, kind, normalized
detail, reference verdict, and exact path as deterministic tie-breakers.  The
result must name every target and explain a single bounded mechanism suggested
by the retained details; size alone does not authorize a change.

A later mechanism preregistration must include:

- all selected targets;
- at least three same-route near-miss controls when available;
- all 94 retained Axeyum decisions as a no-loss population;
- original-term replay for every new SAT result and existing checkers for any
  UNSAT evidence;
- a target-stage gate before a 200-row A/B run; and
- the unchanged 24-second/8-GiB full-list protocol, zero disagreements, no loss
  among the 94, and a strict Axeyum solved-count gain for retention.

If no group meets the minimum, or if details do not support one sound bounded
mechanism, A4 records the census and yields without solver edits.

## Stop conditions

Stop and record a negative result on any population/hash/identity drift,
incomplete stream, operational reference failure, wrong verdict, disagreement,
aggregate mismatch, trace-schema mismatch, unclassified residual, or failure
to find a coherent three-row cluster.  Never repair a failed measurement by
raising caps, dropping rows, changing the reference, broadening accepted
process failures, or treating an unchecked candidate as SAT.
