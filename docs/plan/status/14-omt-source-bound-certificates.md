# Lane: omt-source-bound-certificates — original-query optimality evidence

<!-- plan-section: lane-status -->

**OMT evidence (`WIP`, omt-source-bound-certificates, 2026-10-11).** Child of
42c42e303; parent full tests stay immutable. ADR-6301 specifies reconstruction
of original LRA atoms, variable columns and assertion origins before accepting
carried Farkas multipliers. Added checker and two tests covering original/forged
sources, columns, origins and expired deadline. Focused runner 23596 queued;
log `/var/tmp/axeyum-omt-source-bound-farkas.log`, no pass credited.
Next: compile/test, checker guard mutations, original Int/Boolean lowering binding,
strict-better certificates, model-plus-optimality Python results, serialization
and independent process replay, then required full gates. Gold still false.
