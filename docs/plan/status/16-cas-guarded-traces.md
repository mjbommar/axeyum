# Lane: cas-guarded-traces — conditional quotient certificates

<!-- plan-section: lane-status -->

**LIB-5 guarded traces (`WIP`, cas-guarded-traces, 2026-10-11).** Child of
71d640d68, separate from running portable-OMT Rust gates. ADR-6400 allocates
conditional quotient evidence with caller-bound nonzero assumptions and existing
polynomial trace witnesses. Original version-1 semantics remain unconditional.
Source search found no existing guarded cancellation trace. `just brief
guarded_fraction_trace` returned UNRESOLVED with its 2971-fact positive control;
stale shape inventory prevents treating that as mathematical absence.

Implemented `guarded_trace`: original quotient/result/context transport, explicit
denominator premise, polynomial-trace identity replay, syntactic cancellation
producer and bounded JSON export/replay. Three Rust tests cover byte replay,
missing/altered assumptions, an incorrect quotient and the zero corner. Cargo
job16697 pending/running; `/var/tmp/axeyum-cas-guarded-tests.log`, Data0 target.
No passing test count credited yet. Source frozen while that job runs.

Next: inspect focused result, Python exposure, private mutation controls and
broader CAS gates. Nested cancellation, wide trace
coefficients and kernel admission remain required follow-up work.
