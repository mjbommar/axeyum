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
