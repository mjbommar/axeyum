# Glaurung concretization-policy sweep

This directory preserves preregistered attempts to measure Glaurung's five
executable A0 scalar-policy settings under sole Z3 and sole Axeyum authority.
The validated positive-control population is kept separate from unlabeled real-
driver discovery output.

## Attempt 1: rejected at the complete-usbprint resource boundary

ADR-0244 preregistered a three-stratum matrix from clean detached Axeyum
`234c6678c0521e30a8a92c76a0abf7758fc01395` and clean isolated Glaurung
`b79f26959378f9b8ea51eee6f1b3809a4a234c84`. The runner preserved the partial
campaign under [`attempt-1-usbprint-deadline/`](attempt-1-usbprint-deadline/).
It stopped at the first rejected cell, before maximum and site-hash policies,
as preregistered.

Accepted partial cells:

| Policy | Stratum | Coverage | Validated/high findings | Raw Z3/Axeyum | Solves per authority/repetition |
|---|---|---|---:|---:|---:|
| AnyModel | nine-driver positive control | complete | 14/14 validated | 122/122 total | 2,322 total |
| AnyModel | tcpip prefix 15 | fixed-work 15/338 | 0/0 high | 128/126 | 3,079/2,991 |
| AnyModel | usbprint | complete 18/21 | 0/0 high | 214/214 | 16,537/16,537 |
| minimum | nine-driver positive control | complete | 14/14 validated | 81/81 total | 60,064 total |
| minimum | tcpip prefix 15 | fixed-work 15/338 | 0/0 high | 110/110 | 80,563/80,563 |

The minimum positive-control source join was run after the fail-closed stop as
an explicitly named postmortem check. It accepts the same 14 true-positive rows
with zero false negatives and zero unexpected high-confidence output. It is not
represented as an in-protocol runner step.

The rejected cell is minimum/complete-usbprint. All four order-balanced
processes independently reported `analysis hit the wall-clock safety deadline`
under the preregistered 300-second analysis and 360-second process bounds. The
authority report therefore contains four process failures, no summary, and
`accepted=false`. Source identities stayed clean and stable; policy selection
used the preferred `GLAURUNG_CONCRETIZATION_POLICY=min-unsigned` surface.

The result is a policy/resource finding, not a backend disagreement: a driver
that completes quickly under AnyModel does not necessarily retain a complete
coverage boundary under deterministic extremum probing. The campaign must not
raise the deadline after observing this output and call it the same experiment.
Complete usbprint is therefore removed from the all-policy v2 matrix and retained
as a separate resource-frontier target. A later frontier must preregister its own
bounded function/work cells.

Exact attempt identities:

- preregistration SHA-256:
  `9f205f3807700eada3f96f084bdcb78b0d10a51b0413862c69c8e675959df564`
- execution manifest SHA-256:
  `d5de147cfd3d0cd4bcce96c5f5600d74da2abcf1712cc4fa9ba1a4a260c54266`
- rejected authority report SHA-256:
  `9b4b6daf5e2350e6472b68c34278f706db7747ff9b198c2596c81a3819f5ffbd`

No attempt-1 timing is a solver-speed comparison. Policy-dependent elapsed
time, solver time, RSS, and solve counts are descriptive integration costs.

## Attempt 2: rejected at maximum's positive-control precision gate

ADR-0245 removed complete usbprint from the all-policy matrix without changing
the remaining policies, sources, binaries, work, or order. The exact campaign
ran from clean detached Axeyum
`e11a2157b50115f38031520a587e7940767d787c` and the same clean isolated
Glaurung `b79f26959378f9b8ea51eee6f1b3809a4a234c84`. The runner preserved the
partial campaign under
[`attempt-2-max-unexpected-high/`](attempt-2-max-unexpected-high/) and stopped
before either site-hash policy, as preregistered.

| Policy | Stratum | Validated/high findings | Raw Z3/Axeyum | Solves per authority/repetition |
|---|---|---:|---:|---:|
| AnyModel | positive control | 14/14 exact | 122/122 | 2,322 |
| AnyModel | tcpip prefix 15 | 0/0 high | 128/126 | 3,079/2,991 |
| minimum | positive control | 14/14 exact | 81/81 | 60,064 |
| minimum | tcpip prefix 15 | 0/0 high | 110/110 | 80,563 |
| maximum | positive control | 14 expected + 1 unexpected high | 69/69 | 60,721 |
| maximum | tcpip prefix 15 | 0/0 high | 84/84 | 34,659 |

Maximum retained every expected source-backed finding, but both authorities
and both repetitions also emitted:

```text
stack-overflow va=0x2a09211bc fn=IoctlHandler sev=Arbitrary taint=["*SystemBuffer"]
```

The source at that address is `RtlCopyMemory(request->TargetAddress,
request->SourceAddress, request->Size)`: the destination is an arbitrary
attacker-supplied address, not a local stack object. Glaurung `b79f269` labels a
copy as stack overflow when separately concretized `dst` and `rsp` values land
within a +/-64 KiB numeric window. Maximum makes that accidental proximity
possible. The source-backed validator therefore correctly rejects the row as a
model-choice-dependent false-positive classification: recall remains 1.0,
precision becomes 14/15, and the exact-positive-set gate fails.

This is stronger than ordinary model divergence. A semantic region
classification must not be inferred from the accidental proximity of two
unconstrained concrete witnesses. The remaining site-hash cells stay unobserved
until the detector uses model-independent stack-region evidence and a corrected
sweep is preregistered.

Exact attempt identities:

- preregistration SHA-256:
  `ad5ef20e61210efd8eabe94c4c6b71e3ddc2a6d78f531ef87c65e27fc6b9b17f`
- execution manifest SHA-256:
  `51c02bfeb8e971a73dcd4ce963d8244f57d4c238554910299eac242148c4f236`
- rejected positive validation SHA-256:
  `062a5beaf59c75cb929f893e77ef4495ff664e6e0de6277bcf045cf4c652c2cb`

As in attempt 1, elapsed time is descriptive integration cost, not a
solver-speed comparison.

## Detector correction: accepted maximum-policy source control

ADR-0246 preserves the complete correction trail under
[`detector-correction-max-control/`](detector-correction-max-control/):

| Candidate | Structural rule | Validation | Meaning |
|---|---|---:|---|
| Glaurung `52bd3c0` | `rsp` shared-symbol origin | 13/14, no unexpected | Removed the false row but missed genuine `[rbp-0x70]` storage |
| Glaurung `3d0e2aa` | `rsp` or `rbp` shared-symbol origin | 13/14, no unexpected | Fresh-symbol unit test passed, but the real stack DAG has no free symbols |
| Glaurung `0581f57` | non-leaf expression-DAG ancestry or shared-symbol origin | 14/14 exact | Accepted: precision=1.0, recall=1.0, zero unexpected high rows |

The accepted exact N=2 control uses Z3 binary
`027dad8802083021a278216ad471fc85f73c2a2aeeb228b08d6ebe6e9ea8031e`
and Axeyum binary
`ee7ef0f84000080700129fe12d49f34396f6be8aeae4d36b35bdb2a4912ae6cd`.
Both authorities and both repetitions emit the same exact source-backed set.
The accepted report SHA-256 is
`8ff7eef2738c51c78de2576807fa7c27a1b8cf5c0c77e77951f0912f6392cc6e`;
the validation SHA-256 is
`281ccf95a5ca1ecf176f5b9bfddcddf6fb2bd4e098549b7a8844caf599d32dc8`.

This gate accepts the detector correction only. It does not rehabilitate v2 or
turn maximum into a preferred policy.

## Attempt 3: preregistered corrected five-policy sweep

ADR-0247 fixes v3 at final documented Glaurung `7f682e5`, rebuilt authority
binaries with the hashes above, and the unchanged positive/tcpip v2 work
boundaries. All five policies will be rerun from one clean detached Axeyum
commit. No v3 cell was observed before committing the registration. Complete
usbprint remains a separate resource-frontier result.

The exact clean-detached Axeyum `f2af8b40` run is preserved under
[`attempt-3-accepted/`](attempt-3-accepted/). The aggregate analyzer accepts the
full matrix.

| Policy | Positive raw | Positive validated | Positive solves | Tcpip raw Z3/Axeyum | Tcpip solves Z3/Axeyum |
|---|---:|---:|---:|---:|---:|
| AnyModel | 122 | 14/14 exact | 2,312 | 128/126 | 3,079/2,991 |
| minimum | 81 | 14/14 exact | 59,800 | 110/110 | 80,563/80,563 |
| maximum | 68 | 14/14 exact | 60,456 | 84/84 | 34,659/34,659 |
| site-hash-zero | 77 | 14/14 exact | 59,791 | 95/95 | 28,258/28,258 |
| site-hash-one | 72 | 14/14 exact | 60,465 | 98/98 | 79,950/79,950 |

Every positive cell has precision and recall 1.0, zero false negatives, zero
unexpected high rows, stable repetitions, and exact authority parity. Every
tcpip cell has zero high-confidence rows. Tcpip policy variation is therefore
retained as unlabeled diagnostic output, not a recall result.

The integration-cost frontier is also explicit. Site-hash-one tcpip is the
largest cell: roughly 68 seconds / 147 MiB under Z3 and 264 seconds / 235 MiB
under Axeyum. Minimum is roughly 68 seconds / 150 MiB and 160 seconds / 186 MiB;
site-hash-zero is roughly 21 seconds / 139 MiB and 19 seconds / 140 MiB. These
numbers describe policy execution in Glaurung and are not solver-speed claims.

Exact attempt identities:

- preregistration SHA-256:
  `6cf0f41c8fd0f0024c8189ae59812943f8c119738bd8f8b26a087d2abec56300`
- execution manifest SHA-256:
  `8a2caae84e0cdf8fe0703e9fc7eea8b9220756e165ee74b48faed5c74e71e3e0`
- accepted analysis SHA-256:
  `6de0c7592f00d90711f4a4b7dbb5a381bfe663c914094aa55c069c355dfdcb99`

V3 closes the five executable scalar-policy matrix. It does not itself open
symbolic memory: the labeled control is policy-invariant. ADR-0248's subsequent
exhaustive source-backed adjudication closes the varying planted-fixture rows
without finding a validated residual gap. Usbprint remains a separate resource
frontier.

## Exhaustive source-backed difference adjudication

ADR-0248 follows the accepted v3 sweep with a stronger no-sampling control. It
freezes and reviews the complete 54-row union-minus-intersection from the
tracked positive population. The accepted result is preserved under
[`policy-difference-adjudication-v1/`](policy-difference-adjudication-v1/).

All 43 sites revalidate against exact source ranges and instructions at pinned
IOCTLance revision `905629a`; all 14 source/binary files are tracked, clean, and
hash-exact. Thirty rows are ordinary fixed IRP/request-buffer plumbing and 24
are duplicate presentations of already validated sinks. There are zero
independent primitives and zero indeterminate rows. Consequently the five
scalar policies have no validated finding difference on this exhaustive
source-backed population, and no residual gap admits symbolic-memory work.
