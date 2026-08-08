# QF_UFLIA A4 theory-model reuse result

Date: 2026-08-07

## Result

Stopped negatively. No solver code is retained, no QF_UFLIA sidecar is
published, and no reference capture or breadth gain is credited.

The v3 Axeyum restart at pushed commit
`a18171343af5dea1df57fcde70b637213df31358` completed 200/200 records with
exactly 26 typed ingest rows and zero stderr, but decided 93 rather than the
required 94. Its raw stream SHA-256 is
`99d703d56d35923bead16ca3dcfafe9ced47564dffb736b0b02c3f5c1326834d`.
The only verdict drift from v2 was
`mathsat/Wisa/xs-18-09-1-5-4-4.smt2`, SAT to `unknown`. The preregistered exact
aggregate therefore failed before cvc5 and validation.

## Reproduction

Three isolated runs of the unchanged v3 release binary at 24 seconds produced:

| Run | Verdict | Wall time |
|---:|---|---:|
| 1 | SAT | 19.41 s |
| 2 | unknown | 24.33 s |
| 3 | SAT | 19.92 s |

The `unknown` trace reached a SAT candidate but exhausted the shared deadline
during integer model reconstruction. This is a hardware/load-relative
completeness boundary, not a wrong verdict.

## Rejected repair

The preregistered repair preserved a SAT theory model from the conflict scan so
`try_finish_sat` would not solve the identical conjunction again. Warning-denied
Clippy and focused cached-model/replay controls passed. The first implementation
also changed the scan from the lazy loop's fixed node cap to the reconstruction
oracle's deadline-relaxed cap; it was rejected after 4 SAT / 1 unknown isolated
runs. A corrected version retained the exact fixed node cap and identical LIA
algorithm; it still produced SAT in 19.92 seconds and `unknown` in 24.33 seconds
on its first two acceptance runs. A third in-flight run completed SAT in 22.52
seconds while the remaining repetitions were stopped.

Thus duplicate model reconstruction is real but not the binding source of the
unstable frontier. The first conjunctive theory probe itself crosses the wall
deadline under ordinary timing variation. Both experimental variants were
removed with `git diff` confirming no solver source changes remain.

## Disposition

- Do not retry the full census until 94 happens to pass.
- Do not lower the retained baseline, raise the timeout, special-case the file,
  or reinterpret an `unknown` as solved.
- Revisit A4 only with an architecture-level deterministic-work proposal for
  the conjunctive LIA probe and a fresh preregistration covering the full
  94-decision control.
- Yield to A5's cross-division linear-arithmetic residual census.
