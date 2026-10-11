# Lane: cas-wide-guarded-traces — conditional wide arithmetic

<!-- plan-section: lane-status -->

**LIB-5/LIB-6 (`WIP`, cas-wide-guarded-traces, 2026-10-11).** Child of4cd646409.
ADR6600 specifies guarded-quotient v2 with exact external nonzero-context binding
and matching polynomial-v2 identity witnesses. Existing v1 remains narrow.
Rust producer/checker now select v1/v2 transport and arithmetic consistently;
both identity witnesses must match envelope version. Zero-polynomial denominator
checks and exact external-context binding remain mandatory. Existing Rust suite passed4/0 failed/ignored; new wide suite passed4/0 failed/ignored:
`/var/tmp/axeyum-cas-wide-guarded-{rust,tests-v2}.log`. First wide compile
failed a nonexistent context field; corrected, not credited as a test run.
Wide suite has missing crate-doc warning to fix after current build.
Python `cancel_trace(..., wide=True)` added; replay/getters carry wide values.
Fresh native32955 running, uncredited: `/var/tmp/axeyum-cas-wide-guarded-native.log`.
Added10 Python runtime cases including separate-process replay with producer
disabled; syntax compilation passed, runtime awaits native32955.
Parent wide CAS2147 passed/0 failed/11 ignored,389.32s; this is parent evidence.
Next: Python runtime run and stubs, private
mutations and broad gates. Entire feedback goal remains active.
