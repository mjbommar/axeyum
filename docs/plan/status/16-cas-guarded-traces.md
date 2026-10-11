# Lane: cas-guarded-traces — conditional quotient certificates

<!-- plan-section: lane-status -->

**LIB-5 guarded traces (`WIP`, cas-guarded-traces, 2026-10-11).** Child of
71d640d68, separate from running portable-OMT Rust gates. ADR-6400 allocates
conditional quotient evidence with caller-bound nonzero assumptions and existing
polynomial trace witnesses. Original version-1 semantics remain unconditional.
Source search found no existing guarded cancellation trace. `just brief
guarded_fraction_trace` returned UNRESOLVED with its 2971-fact positive control;
stale shape inventory prevents treating that as mathematical absence.

Next: implement producer, subject/context-bound checker and byte replay; test
zero, missing/altered assumptions and altered result; then Python, private
mutation controls and broader CAS gates. Nested cancellation, wide trace
coefficients and kernel admission remain required follow-up work.
