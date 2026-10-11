# Lane: cas-wide-guarded-traces — conditional wide arithmetic

<!-- plan-section: lane-status -->

**LIB-5/LIB-6 (`WIP`, cas-wide-guarded-traces, 2026-10-11).** Child of4cd646409.
ADR6600 specifies guarded-quotient v2 with exact external nonzero-context binding
and matching polynomial-v2 identity witnesses. Existing v1 remains narrow.
Rust producer/checker now select v1/v2 transport and arithmetic consistently;
both identity witnesses must match envelope version. Zero-polynomial denominator
checks and exact external-context binding remain mandatory. Existing Rust suite
26983 running, uncredited: `/var/tmp/axeyum-cas-wide-guarded-rust.log`.
Next: wide Rust
negative controls, Python explicit wide API, separate-process replay, private
mutations and broad gates. Entire feedback goal remains active.
