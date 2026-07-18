# Accepted tcpip site-schedule authority-union result

ADR-0239's isolated exact rerun passes every preregistered gate. The arbitrary
model remains an intentionally rejected control with 126 shared findings and
two Z3-only rows. Minimum and maximum reproduce ADR-0238 exactly. Both new
site-hash policies are repetition-stable and byte-identical under sole Z3 and
sole Axeyum authority.

| Policy | Findings | Solves per process | Choices completed | Probes | Ordered-list SHA-256 |
|---|---:|---:|---:|---:|---|
| minimum | 110 | 80,563 | 1,204 | 79,466 | `e657ea6be385ba32b2aec6e49f2a780ec7f80850eb3105dc750fce74810d438e` |
| maximum | 84 | 34,659 | 513 | 33,858 | `ceb7789a3a20100c1f8e12566779a832b1093aa89687ebf3f2fa3d54dff2e01d` |
| site-hash zero | 95 | 28,258 | 419 | 27,654 | `04e63d1e49c30fe39e0298075428543e50309c4384d66232ace7043f9ca9f9da` |
| site-hash one | 98 | 79,950 | 1,195 | 78,872 | `4a965d6324613ce292eaa5d9c1b37e8c8041ddb9be7bbee20a13d39bfd6863bd` |

Every count above is identical in all three repetitions under both authorities.
Minimum and site-hash one each also report two identically classified infeasible
choices; every policy reports zero inconclusive, unknown, error, unsupported,
or no-solver choice.

The minimum/maximum union remains 125 findings. The two site schedules together
contain 122. Adding them to the extrema contributes three new rows, producing a
128-finding four-schedule union with SHA-256
`9304e52ec8014146558152b81883c51b7c9b244aeb811721b8a3610fe0daf816`.
Of those 128 rows, 69 occur under all four policies, two under three, 48 under
two, and nine under one. Policy-unique counts are maximum 6, minimum 0,
site-hash-zero 3, and site-hash-one 0.

Against the arbitrary-model combined union, the accepted four-schedule union
has 95 shared, 33 arbitrary-only, and 33 four-schedule-only rows. The mixed-site
extension therefore improves the deterministic ensemble by three rows but does
not recover any of the 33 arbitrary-only rows. This is bounded authority parity,
not exhaustive model, path, finding, or vulnerability coverage.

## Artifact hashes

```text
a45a140b0122dd1c3b35c4029ad1fe9d91d45b1cbf1f3e3e79597c43077e998e  any-model-report.json
18394d9730a58354d44e058584f33ab658a99a39e492691f3462f8e39b913712  min-unsigned-report.json
f64059309c546b634805e0501e4783733d37c0024d5587c95e9183cfe020319c  max-unsigned-report.json
a36273deaa38621a74e01d663c031de30d6dc97fc1c683eabbd666fff23fe851  site-hash-0-report.json
1ea679796dcc181a11ae8814d7729b917218b5f87cf7c6420b27021873ec91ee  site-hash-1-report.json
c3637c308f1041a2e9e7088f3b8ef86bcc11e322219a8aa5f79f1da218da9a5c  site-schedule-union-report.json
```
