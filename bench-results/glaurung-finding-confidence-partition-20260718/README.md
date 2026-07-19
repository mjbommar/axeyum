# Glaurung finding-confidence partition — 2026-07-18

This artifact replaces raw `IOCTLANCE_ALL=1` finding counts as a coverage
surrogate with one producer-owned, machine-readable partition. Glaurung emits
each already-sorted row as `confidence=high|diagnostic` and an exhaustive
`glaurung-ioctlance-confidence-v1` footer. Axeyum's v5 authority harness strips
the annotation before retaining the historical raw bytes, validates the footer,
and records raw, high-confidence, and diagnostic sets from the same process.

## Tcpip existing-policy rebaseline

Every row in the fixed first-15-of-338 tcpip slice is diagnostic under the
corrected producer policy:

| Policy | Z3 raw | Axeyum raw | Z3 high | Axeyum high | Raw parity | Choice attempts / probes |
|---|---:|---:|---:|---:|---|---:|
| AnyModel | 128 | 126 | 0 | 0 | no: two Z3-only `**Arg0` rows | 0 / 0 |
| least unsigned | 110 | 110 | 0 | 0 | yes | 1,206 / 79,466 |
| greatest unsigned | 84 | 84 | 0 | 0 | yes | 513 / 33,858 |
| site-hash-0 | 95 | 95 | 0 | 0 | yes | 419 / 27,654 |
| site-hash-1 | 98 | 98 | 0 | 0 | yes | 1,197 / 78,872 |

The AnyModel union and four deterministic-setting union each contain 128 raw
rows, with 95 shared, 33 AnyModel-only, and 33 deterministic-only. All 33 of
the formerly unclassified AnyModel-only rows are now producer-classified
diagnostics: their labels are exclusively `Arg0`/`Arg1` ancestry and nested
dereferences. This is not a manual false-positive label; it is an accepted
statement only about Glaurung's current confidence policy.

Every policy used two order-balanced repetitions per authority, a 250 ms
per-check timeout, a 300,000-check and 300-second solve budget, and the fixed
15-function boundary. All high-confidence acceptance gates pass. AnyModel's
raw mismatch remains intentionally visible.

## Positive-corpus selection

Rechecking the four earlier small drivers plus a 50-function NETwtw10 prefix
finds zero high-confidence rows after provenance correction:

| Driver | Raw Z3 / Axeyum | High Z3 / Axeyum | Raw relation |
|---|---:|---:|---|
| DptfDevGen | 17 / 17 | 0 / 0 | exact |
| vwififlt | 104 / 104 | 0 / 0 | two rows differ only as `**Arg0` vs `*Arg0` |
| IntcSST | 116 / 116 | 0 / 0 | exact |
| SurfacePen | 65 / 65 | 0 / 0 | exact |
| NETwtw10 prefix 50 | 565 / 565 | 0 / 0 | exact |

The complete x64 Windows 11 `usbprint.sys` run is the first suitable nonzero
candidate: Z3 emits five and Axeyum four stable high-confidence rows. Four are
shared; Z3 alone emits a `SystemBuffer` null dereference at `0x140002770`.
The harness therefore rejects the run for high-confidence authority parity.
This is the next labeling and root-cause target, not an accepted finding-parity
result and not yet a true-positive denominator. Do not start BoundarySet,
DiverseEnum, symcrete, or symbolic-memory work until these five rows are
independently classified and the sweep is preregistered.

## Exact identities and scope

- Axeyum harness revision: `593cc582a8d533989e7a2aa678674669f392e26e`.
- Glaurung producer revision: `931d8a844c7ffeb4e96d9b7ab4834b7be1ef9701`.
- Z3-authority binary SHA-256:
  `4b59501a1cb0e2322d1812445cc305782e89bf2053d7a023352400bc769ca485`.
- Axeyum-authority binary SHA-256:
  `4d43aa1c61e59b8e6e84c05c4435c4c5ffffd4c2c56334a4999a97b2b9f85fa6`.
- Tcpip input SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`.
- Usbprint input SHA-256:
  `3eb6b8172849290bac6ff548b53fbf78c37c6f68a22bdc604b12418d1b22a968`.

The JSON reports are the canonical evidence. They include exact source,
binary, input, environment, order, work, timing/RSS, finding bytes/hashes,
confidence partition, differences, and post-run source identity. The first
site-hash-1 attempt was rejected when documentation changed during execution;
the committed report is the clean unchanged-source rerun.

This artifact establishes a trustworthy measurement partition and a bounded
negative result for the old tcpip recall story. It does not equate producer
confidence with ground truth, claim that the usbprint rows are vulnerabilities,
or establish a Pareto-dominant concretization policy.
