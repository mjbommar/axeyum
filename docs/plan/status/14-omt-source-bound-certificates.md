# Lane: omt-source-bound-certificates — original-query optimality evidence

<!-- plan-section: lane-status -->

**OMT evidence (`WIP`, omt-source-bound-certificates, 2026-10-11).** Child of
42c42e303; parent full tests stay immutable. ADR-6301 specifies reconstruction
of original LRA atoms, variable columns and assertion origins before accepting
carried Farkas multipliers. Added checker and two tests covering original/forged
sources, columns, origins and expired deadline. Focused runner 23596 queued;
log `/var/tmp/axeyum-omt-source-bound-farkas.log`, no pass credited.
Added original-context strict-better refutations through deterministic Int/Real
relaxation and replay_optimality; current optimum pin excluded. Regression
changes claimed maxima/minima to expose circular proofs. Generate after all
solves to stabilize relaxation columns; test box/lex certificate replay and
integer-cut-only optima with missing real refutation. Runner 42842 queued, log
`/var/tmp/axeyum-omt-strict-better.log`. Not yet verified.
Next: compile/test, checker guard mutations, Boolean lowering binding,
strict-better certificates, model-plus-optimality Python results, serialization
and independent process replay, then required full gates. Gold still false.
