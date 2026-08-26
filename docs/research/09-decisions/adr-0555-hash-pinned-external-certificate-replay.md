# ADR-0555: Hash-pinned external certificate replay is a non-authoritative import boundary

Status: accepted
Date: 2026-08-25
Index-summary: Replay third-party certificate checkers with pinned bytes, bounded process isolation, finding-dependent success, and a content-addressed non-authoritative receipt

## Context

The August 2026 open-problems programme consumes certificates produced by research software
outside Axeyum.  The first real case is Wang's bilinear-rank lower-bound certificate for
`R_F2(P_6) >= 16`; later cases may include exact theta certificates and VeriPB logs.  These
formats do not become Axeyum evidence merely because their published verifier exits zero.
Nevertheless, a faithful replay must bind the exact checker and artifact bytes, enforce a
wall limit, distinguish timeout from rejection, retain the observed outputs, and prove by a
negative control that successful completion alone is insufficient.

ADR-0470's registered-operation receipts solve a stronger and different problem: a reviewed
registry chooses the only command, input, fact, route, budget, and expected result that may
participate in Autogenesis admission.  Generalising that authoritative interface to arbitrary
third-party commands would erase its trust boundary.

## Decision

Add `scripts/check-external-certificate.py` as a **non-authoritative import boundary**.  It
accepts one versioned JSON manifest and no command-line fragments.  The manifest must pin:

- the checker executable by SHA-256;
- every certificate, instance, archive, or auxiliary input by a unique role and SHA-256;
- an argument vector whose artifact references occupy whole arguments;
- a wall-clock timeout from 1 through 86,400 seconds; and
- both accepted exit codes and at least one required output substring.

The runner validates every digest before execution, starts the checker in a new process
session, kills and reaps the session on timeout, captures stdout and stderr in files rather
than pipes, and emits a content-addressed JSON receipt.  `verified`, `failed`, and `timeout`
are distinct observations with exit statuses 0, 1, and 3.  Manifest/input/checker errors exit
2 before the checker runs.  Captured output over 16 MiB is hashed but is not eligible for a
successful substring match; truncation therefore fails closed rather than hiding the
finding-bearing portion.

The receipt records paths for reproducibility, but hashes are the identities.  Elapsed time
is telemetry, not part of the manifest identity.  A receipt proves only this proposition:
the exact external checker accepted the exact inputs under the recorded policy and observable
success contract.  It does not establish checker independence, soundness, novelty, a Lean
kernel theorem, or fact-ledger admission.  Those require a format-specific Axeyum checker or
a separately registered authoritative operation.

## Evidence

Focused tests exercise four load-bearing outcomes:

1. exact checker and artifact bytes produce a `verified` receipt;
2. mutating an artifact after manifest creation is rejected before execution;
3. exit zero without the required finding exits 1; and
4. exceeding the wall limit kills the process session and exits 3 rather than passing.

The first real integration target is the published `full_q02_n06` certificate.  Its research
package retains the upstream commit and LFS-object hashes, the complete replay receipt, and a
semantic certificate mutation that the upstream verifier must reject.

## Alternatives

### Add arbitrary external commands to the Autogenesis registry

Rejected.  A generic command is not a reviewed statement-to-input derivation and must not
gain ledger authority through convenience.

### Treat exit zero as acceptance

Rejected.  Several repository checkers historically exited zero after merely completing;
the external runner therefore requires an observable finding in addition to an accepted
exit status.

### Reimplement every external checker before recording any result

Rejected as the only ingestion path.  Independent reimplementation remains the stronger
assurance milestone, but byte-pinned replay is needed first to reproduce the published claim,
measure its cost, and localise incompatibilities without overstating trust.

## Consequences

- All five problem packages can record external replay with one stable receipt shape.
- Third-party outputs remain explicitly below Axeyum's checked-evidence and kernel tiers.
- Format-specific adapters can consume a receipt later without rediscovering source identity,
  input identity, resource policy, or the original observation.
- A source rebuild changes the executable hash even when it uses the same commit; research
  packages must therefore record both source provenance and binary identity.
