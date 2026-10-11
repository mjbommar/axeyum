# Wide CAS trace cost diagnostics

Measured with the sealed debug Python extension identified in
[cost-initial.json](cost-initial.json). Source for that native build is
9ea2285ab; c6b0a5db1 subsequently extracts an unchanged division-validation
helper. These are local measurements under concurrent aggregate test load,
not benchmark or parity claims. Seven samples follow one warm invocation.
Every sample checks exact results; production also checks deterministic bytes;
byte replay binds independently constructed original input and expected result.

| Workload | Steps | JSON bytes | Exact evaluation median | Trace production median | Byte replay median |
|---|---:|---:|---:|---:|---:|
| Closed rational fourth power | 2 | 1,354 | 0.084 ms | 0.424 ms | 0.167 ms |
| Exact 360-period payment | 6 | 34,998 | 18.135 ms | 1,515.594 ms | 367.583 ms |

Exact evaluation does not produce a certificate. Ordinary normalization has
narrower coefficient limits, so it is not a matching wide-baseline operation.
The revised [run with baseline](cost-with-baseline.json) completed seven
samples: small ordinary normalization median0.011 ms, tracing0.152 ms,
replay0.062 ms. Payment tracing median0.848 s and replay0.367 s. The different
initial/revised timings demonstrate host-load sensitivity; neither supports a
stable performance ratio. Both retain identical trace bytes/step counts.

The payment trace is much more expensive than exact evaluation. It serializes
intermediate endpoints and rechecks local relations; these measurements justify
examining repeated validation and large rational witness work before expanding
workload size. Limits remain explicit; no performance claim is inferred from
these two closed expressions.
