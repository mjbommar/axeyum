# Lane: quotient-decision — W0-1, the quotient/extensionality decision (ADR-1595)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, quotient-decision, 2026-09-04).** Roadmap W0-1: decide
whether the kernel adds `Quot.sound`, commits to setoid quotients, or admits
`Quot.sound` in a labelled second tier. The decision is to be made by
measurement, not argument: the experiment is the first isomorphism theorem over
`AlgS.Group` (roadmap W2-8) built by the setoid route in
`crates/axeyum-lean-kernel/src/nat_prelude/structures_setoid.rs`, counting the
congruence obligations discharged by hand that a real quotient would give free.
ADR number 1595 is reserved. Status: started.

<!-- plan-section: landed-changes -->

| 2026-09-04 | quotient-decision | lane opened: W0-1 quotient/extensionality decision, ADR-1595 reserved |
