# Lane: omt-portable-evidence — byte replay without optimization search

<!-- plan-section: lane-status -->

**Portable OMT evidence (`WIP`, omt-portable-evidence, 2026-10-11).** Isolated
child of0a0a3b144; parent gates54092/32215 retain immutable Rust. ADR-6302
specifies original-source, selected-objective and lex-prefix certificates with
named models/columns and source-bound Farkas replay. Added strict transport and counted byte checker rebuilding subject/objectives,
models, lex prefixes and strict-better source bindings without optimization.
Five Rust tests cover modes/counts, retargeting, model/value/direction, prefixes,
refutations and malformed envelopes. Compilation78708 running, not credited.
Next: complete counted original-subject checker, corruption/guard controls,
fresh Rust/Python and external-process replay, then required broader gates.
Integer-only/BV/Boolean producers and kernel reconstruction remain open.
