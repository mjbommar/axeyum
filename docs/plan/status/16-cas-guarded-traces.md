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
job16697 completed: 3 passed, 0 failed/ignored, 0.00s, 2151 filtered out,
`/var/tmp/axeyum-cas-guarded-tests.log`, Data0 target. No broad-gate credit.

Portable parent stub generation/signature/type gates passed (27 modules, 654
items, 1860 runtime symbols). Its private source/priority mutations each yielded
6 passed plus exactly 1 intended failure; snapshot restored byte-for-byte.
Parent lint45243 is terminal101: missing panic documentation for midpoint expect,
173-line portable checker and collapsible priority if. These require repair;
no full-lint pass claimed.

Python now exposes `cancel_trace`, `replay_guarded_trace`, guarded trace/result
classes and explicit produced/checked/rejected/unsupported/resource-limited
outcomes. JSON replay returns the checked object after one parse. Fresh native
77101 passed; sealed package
`/var/tmp/axeyum-cas-guarded-python-04jfnbsk/package`, SHA256
`4e100b9c0f070c4af1e0983f3ca063c5604b763977625dc6c7c7055ded153708`.
Twenty-one Python guarded/unconditional trace tests passed, 0 skips, 0.47s;
separate-process replay and assumption/subject/result/premise/witness/envelope
controls included. Updated example checked guarded cancellation with x != 0 and
rejected the missing context. Logs `/var/tmp/axeyum-cas-guarded-python-tests.log`.
Rust return-signature rerun14760 and stub generation launched, not credited.

Parent post-lint focused tests passed 17; lint-v2 exposed docs/test-naming errors,
repaired in parent source; lint-v3 is running. This child still needs those source
repairs imported after parent commit, plus generated SMT stubs from e48755b70.

Next: complete Rust/stub gates, private mutation controls and broader CAS gates. Nested cancellation, wide trace
coefficients and kernel admission remain required follow-up work.
