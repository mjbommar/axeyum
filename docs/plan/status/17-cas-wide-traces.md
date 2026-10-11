# Lane: cas-wide-traces — promoted coefficients and closed rational steps

<!-- plan-section: lane-status -->

**LIB-5/LIB-6 (`WIP`, cas-wide-traces, 2026-10-11).** Base435de8c46.
ADR6500 defines opt-in v2 promoted arithmetic/codec,16384-bit intermediate cap,
width-weighted work, bounded shape/expansion/degree and constant powers512.
V1 stays narrow. V2 constant division carries checked nonzero conditions and
validates original domains even for empty traces. Sourcec6b0a5db1.

Rust suites passed8 v1+7 v2,0 failed/ignored after helper extraction:
`/var/tmp/axeyum-cas-wide-postlint-tests.log`. Private snapshot controls:
baseline7 passed; condition/domain/bit guard removal each causes6 passes and
one intended failure, exit101; restored bytewise. Logs
`/var/tmp/axeyum-cas-wide-control-{baseline,condition,domain,bits}.log`.
Full lint58742 passed926/926 targets,27 crates,0 diagnostics:
`/var/tmp/axeyum-cas-wide-clippy-v2.log`.
Serial full CAS29000 running, uncredited: `/var/tmp/axeyum-cas-wide-full-cas.log`.
Parent solver2028 passed; parent workspace remains pending.

Fresh native68539 passed; package
`/data0/axeyum/artifacts/python/cas-wide-trace-zyb2jcxy/package`, SHA256
`8d15fa2aa3664369c9031fbe191aeeb46032fe11720ea15072d74e45dde83f55`.
Python34 trace tests passed/0 skipped,9.07s; Fraction payment controls and
separate-process replay included. Example exact payment2859/2849 coefficient
bits; zero-rate2500/3. Stubs27 modules/658 items; runtime1867 symbols;
types1817 parameters/1732 typed,131 Any all allowlisted.

Cost runs completed with exact checks:payment6 steps/34998 bytes, revised
median production0.848s/replay0.367s. Small ordinary normalization0.011ms,
tracing0.152ms. [Diagnostics](../notes/cas-wide-traces/cost.md) retain both runs
and extension identity; host-load sensitivity prevents parity claims.

Next: finish broad gates; wide guarded quotients, kernel reconstruction and
branch integration. Entire feedback goal remains active.
