# ADR-0242: Correct WDM SystemBuffer finding baseline

Status: accepted
Date: 2026-07-18

## Context

ADR-0241 selected complete x64 Windows 11 `usbprint.sys` as the first nonzero
producer-confidence candidate: five Z3-authoritative versus four
Axeyum-authoritative rows, including one stable Z3-only `SystemBuffer` null
dereference. It deliberately required independent classification before using
those rows as a concretization-policy recall denominator.

Public symbols, the raw dispatch table, and disassembly place all five rows in
`HPUsbIOCTLVendorGetCommand`. IOCTL `0x0022003c` is `METHOD_BUFFERED`; the three
byte reads occur only after explicit `SystemBuffer != NULL` and
`OutputBufferLength >= 3` guards. Windows owns the kernel SystemBuffer pointer
and allocates the larger input/output size. Glaurung instead seeded that
pointer as a free attacker-controlled 64-bit symbol, conflating address
ownership with attacker-controlled buffer contents.

## Decision

Retire all five usbprint rows as producer-environment-model false positives,
not validated driver findings. Correct the WDM seed in Glaurung by storing a
fixed synthetic kernel SystemBuffer address and preserving attacker provenance
through a separate tainted concrete-memory-region contract. Keep
`Type3InputBuffer` and `UserBuffer` symbolic for genuine `METHOD_NEITHER`
pointer-control analysis.

Accept high-confidence authority parity only on the corrected producer. Keep
the remaining one-row-per-backend generic-argument `memcpy` difference visible
as diagnostic raw output. Do not use usbprint as the nonzero A0 policy-sweep
population, do not preregister a recall sweep on another producer-only label,
and do not infer that canonicalizing model representatives would repair the
environment model.

The A0 strategy is unchanged: concretization is one pluggable configuration
knob, and least/greatest/site/boundary/diverse choices are settings to sweep.
The sweep now waits for an independently validated nonzero target. Symbolic
memory remains the sole architectural Pillar-A item and stays conditional on a
validated residual coverage gap after the cheap sweep.

## Evidence

The PE CodeView GUID and public-PDB GUID agree, while their ages differ; symbol
names therefore corroborate rather than replace direct machine-code evidence.
The dispatch table maps IOCTL `0x0022003c` to the handler call. Direct
disassembly shows the non-null and three-byte guards followed by reads at
offsets 2, 1, and 0.

Ordered pre-correction traces expose the Z3-only row's mechanism. At the same
address-concretization query for `SystemBuffer + 2`, Z3 chooses effective
address 1 and Axeyum chooses 3. Z3 thereby binds the invalid free base to
`2^64 - 1`; the next `base + 1` wraps to zero. Both representatives satisfy
the malformed environment, so their difference is model steering rather than
finding recall.

The correction adds a reduced regression that emitted the same three
controlled reads and two null dereferences before the fix and emits none
afterward. All 22 focused IOCTL tests pass independently under Z3 and Axeyum.
Both authority-specific `ioctlance` examples compile.

The unchanged v5 Axeyum harness then runs two order-balanced repetitions over
the complete 18-of-21 reachable-function boundary. Every process performs
16,537 solves. Both authorities emit 214 raw diagnostics and zero
high-confidence rows in both repetitions, so high-confidence parity is
accepted. The raw sets retain a 213-row intersection plus one backend-specific
generic-`ArgN` CRT `memcpy` store each.

The exact identities, disassembly, trace hashes, per-run metrics, correction
scope, and remaining KMDF/length-model debt are committed under
[`bench-results/glaurung-usbprint-system-buffer-validation-20260718/`](../../../bench-results/glaurung-usbprint-system-buffer-validation-20260718/README.md).

## Consequences

The confidence protocol behaved as intended: it exposed a bounded candidate
but did not turn a producer label into ground truth. The corrected result is a
negative recall result and a positive methodology result. It reinforces the
reviewer-facing rule that verdict agreement, stable output, and producer
confidence are necessary but insufficient without validating the consumer
environment model.

No nonzero validated concretization target is currently established by the
tcpip or usbprint slices. The next work is target selection and independent
labeling, with raw, producer-confidence, and validated populations kept
separate. A policy sweep remains cheaper than symbolic memory, but a zero
validated denominator cannot support a recall claim.

The WDM correction is not a general bounds engine. SystemBuffer contents are
conservatively tainted across the maximum 32-bit request span. A later bounds
primitive must relate accesses to the appropriate request lengths. Glaurung's
KMDF retrieve-buffer summary still has the older symbolic-pointer abstraction
and must be corrected before KMDF SystemBuffer rows can be accepted.

## Alternatives

- Keep the pointer symbolic and suppress only the five addresses: rejected as
  an unsound special case.
- Canonicalize Axeyum to Z3's representative: rejected because it reproduces a
  false environment rather than fixing it.
- Make SystemBuffer concrete and discard content taint: rejected because it
  loses genuine attacker-controlled values passed to dangerous operations.
- Treat the output-length guard as proof for every buffer method: rejected;
  raw `METHOD_NEITHER` pointers retain different ownership and probe rules.
- Proceed with a zero-positive policy sweep: rejected because it can measure
  determinism and cost, but not finding recall.
