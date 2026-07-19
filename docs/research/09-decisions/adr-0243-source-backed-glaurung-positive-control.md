# ADR-0243: Source-backed Glaurung positive finding control

Status: accepted
Date: 2026-07-18

## Context

ADR-0240 corrected provenance laundering in the tcpip authority experiment,
and ADR-0242 corrected the WDM `SystemBuffer` ownership model. Both corrections
reduced the candidate accepted-finding populations to zero. A zero denominator
can test determinism and absence of unexpected output, but it cannot support a
finding-recall gate for the configurable concretization-policy sweep.

Glaurung's producer confidence partition is intentionally not ground truth.
The repository containing the original IOCTLance test drivers provides a
stronger bounded control: tracked planted-vulnerability source and matching PE
binaries. Nine fixtures contain direct dangerous operations that survive the
corrected WDM model. Their producer output contains 14 high-confidence rows at
12 distinct instruction/call sites.

## Decision

Accept `ioctlance-source-backed-positive-v1` as the first nonzero validated
Glaurung **positive control**. Define its denominator by an exact manifest of
driver/source hashes and finding bytes, with a source-line and machine-code
basis for every row. Join that manifest fail closed to the v5 sole-authority
report; do not infer validity from the producer confidence label alone.

The join must reject an empty denominator, missing or extra producer-high rows,
authority divergence, repetition instability, source-identity drift, driver
population drift, incomplete source evidence, untracked/dirty fixture paths,
or any source/binary hash mismatch. Retain raw and diagnostic rows alongside
the validated population.

Use all nine currently validated fixtures and all 14 rows rather than selecting
only the five simplest examples. Count rows and machine-code sites separately:
the physical-memory `memcpy` site intentionally yields three detector labels.

Future A0 configuration sweeps must preserve this control at 14/14 with no
unexpected producer-high row. This is a regression gate, not evidence that a
policy improves coverage. Report policy-dependent real-driver output as an
unlabeled discovery population unless its own source/machine validation creates
a ground-truth denominator. Keep symbolic memory conditional on a validated
residual gap after the configuration sweep.

## Evidence

At IOCTLance revision `905629a773f191108273a55924accd9f31145a8d`, all 18
manifest source/binary paths are tracked, clean, and hash-exact. Direct source
and disassembly review covers file creation/writes, two unchecked allocation/
copy multiplications, physical mapping, attacker-addressed copy, arbitrary port
I/O, `wrmsr`, `rdmsr`, an attacker-derived indirect call, a stack copy, and
process termination.

The unchanged v5 authority harness ran two order-balanced repetitions for each
of nine drivers under sole Z3 and sole Axeyum authority: 36 processes total.
Every output and per-driver solve count is stable and identical between
authorities. Each authority/repetition emits 122 raw rows partitioned into 14
high-confidence and 108 diagnostic rows, using 2,322 solves across the nine
drivers. The source join accepts 14 true positives, zero false negatives, and
zero unexpected high-confidence rows.

The manifest, raw authority report, derived validation report, exact commands,
hashes, and per-driver metrics are committed under
[`bench-results/glaurung-source-backed-positive-validation-20260718/`](../../../bench-results/glaurung-source-backed-positive-validation-20260718/README.md).

## Consequences

The project now has an executable nonzero positive-control denominator that is
independent of solver agreement and producer labeling. This repairs the
methodological gap exposed by tcpip and usbprint without reverting either
environment correction.

The result is deliberately bounded. The fixtures are planted, small, and
shallow; 1.0 recall/precision applies only to these 14 rows. It is not a
real-world recall estimate, a prevalence sample, an exploration-equivalence
claim, or a performance comparison. It does not establish that any non-default
concretization policy is useful.

The next admissible step is a preregistered configuration sweep that keeps this
positive control as a hard regression stratum and reports real-driver policy
variation separately. A real-driver row may enter a recall denominator only
after the same source/machine validation. The sweep remains a measurement of
one pluggable policy knob; it does not promote least/greatest/boundary/diverse
settings into separate research projects.

## Alternatives

- Use only the five clearest single-row fixtures: rejected because nine clean
  fixtures and 14 source-backed rows are available under the same protocol.
- Treat all producer-high rows as validated: rejected because ADR-0242 showed
  that producer environment errors can create stable, confident false rows.
- Count the physical-memory `memcpy` labels as separate vulnerabilities:
  rejected; they are separate detector rows at one machine-code site.
- Call the planted-fixture result real-world recall: rejected because the
  sample was authored to contain direct detectable sinks.
- Begin symbolic-memory work now: rejected because the cheap policy sweep has
  not established a validated residual coverage gap.
