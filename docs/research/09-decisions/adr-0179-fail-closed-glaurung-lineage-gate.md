# ADR-0179: Fail-closed Glaurung lineage gate

Status: accepted
Date: 2026-07-15

## Context

ADR-0178 accepts repeated held-out lineage evidence, but the processes and
`/usr/bin/time` footers are assembled manually. That is not yet a per-commit
regression gate: a dirty tree, different driver bytes, variable work cutoff,
changed resource policy, finding drift, or missing footer can be compared by
mistake. GQ10 requires artifact identity and fail-closed comparison before GQ9
can fit an automatic policy from these bars.

## Decision

Adopt Glaurung's `glaurung-axeyum-lineage-gate-v1` runner, validator, and
comparator as the executable held-out 9/512 boundary.

- The runner records Glaurung/Axeyum revisions and dirty paths, release-binary
  and driver hashes, platform/Rust identity, policy/resource limits, exact work
  and warm lifecycle traffic, finding-output hashes, time, and RSS.
- Dirty repositories fail unless explicitly marked exploratory. Each child has
  a hard 4 GiB address-space limit. JSON is atomically published only after all
  expected-work, agreement, unknown, finding, lifecycle, fallback, and limit
  invariants pass.
- SurfacePen and fixed-budget NETwtw10 traffic are schema-v1 identity. A
  deliberate exploration-shape change needs a new version/evidence decision;
  it is never timed as if it were the same work.
- Artifact comparison permits source revision/binary changes but requires the
  same system, policy, repetitions, driver bytes/configuration, exact traffic,
  and findings before reporting Axeyum, ratio, and median-RSS deltas.
- The tool is downstream benchmark methodology. It does not select lineage,
  cache verdicts, change Axeyum semantics, or weaken model/proof replay.

## Evidence

Glaurung `89aea59` adds the runner and three focused unit tests. Tests cover
exact footer/time parsing, accepted repetition summaries, and rejection of one
structural counter drift. Python byte compilation and Ruff formatting/lint pass.

A real one-process SurfacePen smoke runs through the new child memory limit and
artifact publisher, then passes independent `validate` and self-`compare`:
2,551/2,551 checks agree, exact 9/512 traffic has zero fallbacks/resets, Axeyum
is 1.067 seconds versus Z3 4.429, and the self-comparison reports zero timing,
ratio, and RSS delta. The smoke records dirty paths only because the unrelated
consumer feedback file and the new runner were present during development;
release mode rejects that state.

ADR-0178 supplies the already repeated semantic/performance evidence that the
runner encodes: three identical SurfacePen streams and three identical
fixed-budget NETwtw10 streams, totaling 92,721 held-out agreements. The runner
does not manufacture a new performance claim from its one-process smoke.

## Alternatives

Keeping shell snippets and hand-parsed logs was rejected because identity and
exact work remain implicit. Reusing wall deadlines was rejected by ADR-0178's
different NETwtw10 query counts. Storing only means was rejected because
structural/finding drift would disappear. Running inside Axeyum's regular test
suite was rejected because the drivers are Glaurung-owned, large, and
access-controlled; Axeyum remains independent of the consumer repository.

## Consequences

The GQ10 held-out gate is executable and versioned. Next publish a clean
baseline artifact and add explicit same-environment timing/ratio/RSS regression
alarms to the comparator. Keep diagnostic warm profiles separate.

Once that baseline exists, GQ9 may fit a telemetry-visible topology/cost rule
for whether to select warm lineage at all; fixed 9/512 remains the only accepted
resource envelope after selection. GQ8 caching still requires separate
identity, capacity, invalidation, and replay decisions.
