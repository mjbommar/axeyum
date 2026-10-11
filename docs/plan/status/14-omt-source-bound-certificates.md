# Lane: omt-source-bound-certificates — original-query optimality evidence

<!-- plan-section: lane-status -->

**OMT evidence (`WIP`, omt-source-bound-certificates, 2026-10-11).** ADR-6301
binds Farkas atoms, variable columns and assertion origins to original LRA
constraints. Integer strict-better refutations exclude the current optimum pin,
retain earlier lexicographic pins, and regenerate deterministic real relaxation
for replay. Gold eligibility checks feasible models and refutations for every
lex prefix objective; box results are independent. Integer-only cuts and BV
optimality evidence remain explicitly missing.

Verified: 2 source-binding controls; 10 gold Rust tests; fresh native rebuild
and 53 Python tests, zero skips. Five private guard mutations each cause exactly
one intended failure (three source bindings; model constraints and value).
Generated stubs: 27 modules/652 items; runtime gate1856 symbols; type gate
1717/1802 typed params. Format passes. All identities, logs, counts and storage
recovery details live in [notes](../notes/omt-source-bound-certificates.md).

Required runner54092 remains live: five z3 arithmetic suites, five front doors,
full solver, workspace. First qf_lra differential passes8; remaining phases
uncredited. Logs `/var/tmp/axeyum-omt-gold-required-_volk68z/`. Rust is frozen.
Next: complete required gates, portable source-bearing certificate transport and
independent process replay; Boolean/integer-cut/BV proof producers, bounded
ingest and replay, then kernel reconstruction. Overall goal remains active.
