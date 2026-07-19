# Exhaustive source-backed policy-difference adjudication

ADR-0248 froze all 54 raw findings that vary across the five accepted scalar
policies in the tracked IOCTLance positive population. This directory preserves
the completed no-sampling review.

The fail-closed validator re-read every named source range and the instruction
at every recorded VA from IOCTLance
`905629a773f191108273a55924accd9f31145a8d`. All 14 source/binary files were
tracked, clean, and SHA-256 exact. The result accepts 54/54 findings at 43/43
sites:

| Classification | Rows |
|---|---:|
| Ordinary IRP/request plumbing | 30 |
| Duplicate presentation of an already validated sink | 24 |
| Independent real vulnerability primitive | 0 |
| Indeterminate | 0 |

The request-field rows use fixed `IO_STACK_LOCATION` or I/O-manager-owned
`METHOD_BUFFERED` storage. Rows immediately feeding an existing validated
`ZwCreateFile`, `ZwWriteFile`, integer-overflow, `MmMapIoSpace`, arbitrary-copy,
`ZwTerminateProcess`, `rdmsr`, indirect-call, or stack-copy sink are retained as
duplicate presentations rather than new primitives. In particular, a later
security-sensitive use does not turn the preceding fixed-buffer load into an
independent arbitrary-address read.

No policy has an independently validated primitive in the varying population.
Therefore the scalar sweep shows no validated policy difference or residual
coverage gap, and the symbolic-memory gate remains closed. This source-backed
planted-fixture result is not a real-driver recall estimate; tcpip remains
unlabeled diagnostic evidence.

Exact identities:

- frozen population SHA-256:
  `3671540494b85b2a93af3bddbeb1cbad410b34961c65761f9f9799f43d49e999`
- review SHA-256:
  `f61801fc770da5f6e79df4abc7818a31b5f29fe7c1dac2f74186f37703e57603`
- validator SHA-256:
  `2f3ad18e187064308b35c836dc36659badd6faa2b20b8c9d2638dc174b4ac803`
- accepted result SHA-256:
  `18fe36e155506f201d7e2eba4404995afa76fd9cca6a602df4c6259200822df3`

Reproduction:

```sh
scripts/validate-glaurung-policy-difference-adjudication.py \
  --frozen corpus/glaurung-finding-populations/policy-difference-adjudication-v1.json \
  --review corpus/glaurung-finding-populations/policy-difference-adjudication-v1-review.json \
  --source-repository /path/to/ioctlance-at-905629a \
  --out result.json
```
