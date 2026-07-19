# Glaurung six-cell neutral warm regime

This directory begins as ADR-0272's **zero-result-row registration**. The
mechanism, v3 consumer, exact release executable, driver population, runtime
linkage, run order, statistical contrasts, and acceptance gates were frozen
before any real-driver v3 timing row was observed.

- Registration: [`registration.json`](registration.json)
- Preregistration: [ADR-0272](../../docs/research/09-decisions/adr-0272-preregister-six-cell-neutral-warm-regime.md)
- Glaurung producer: `2961d7c1bca03f14b77b12fb852d193413207982`
- Axeyum v3 analyzer: `5d74283b8cc1779df4d67b654c44d6b7dcc94611`
- Fail-closed campaign runner:
  [`scripts/run-glaurung-six-cell-neutral.py`](../../scripts/run-glaurung-six-cell-neutral.py),
  SHA-256 `daeec160c41862e3a70cc216831971a402d8b7392e3e6b60504b2503e89fbc7c`
- Release executable SHA-256:
  `5d454daf6c12c1d69bc0e28e12c391286b53d1a7735514043b85ea82057ef17b`

At registration time there are no trace paths, timing values, ratios,
confidence intervals, or driver conclusions in this directory. Raw traces use
access-controlled drivers and will remain outside git; accepted reports and
their hashes will be added here after the fixed campaign completes.
