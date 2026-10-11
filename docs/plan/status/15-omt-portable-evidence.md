# Lane: omt-portable-evidence — byte replay without optimization search

<!-- plan-section: lane-status -->

**Portable OMT evidence (`WIP`, omt-portable-evidence, 2026-10-11).** Isolated
child of0a0a3b144; parent gates54092/32215 retain immutable Rust. ADR-6302
specifies original-source, selected-objective and lex-prefix certificates with
named models/columns and source-bound Farkas replay. Implementing bounded strict
transport first, then independent byte checking; no byte-replay success credited.
Next: complete counted original-subject checker, corruption/guard controls,
fresh Rust/Python and external-process replay, then required broader gates.
Integer-only/BV/Boolean producers and kernel reconstruction remain open.
