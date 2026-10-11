# Lane: cas-negative-powers — one line saying what this lane is for

<!-- plan-section: lane-status -->

**Signed CAS powers (`WIP`, cas-negative-powers, 2026-10-10).** Based on
97359c332's bounded wide Python surface. ADR-3000 proposes signed Rust/Python
powers lowering to existing partial Div/Pow nodes, with explicit magnitude,
zero and missing-binding behavior. Four Rust domain/boundary/identity-replay tests pass after checked-squaring
and power-one repair. Initial signed Python: 222 pass; example passes; stubs
645 items/27 modules. Fresh revised-core build and domain mutation remain;
focused lint is running (73272). Domain-aware trace certificates and kernel admission
remain required; no completion/integration claim. Details:
[notes](../notes/cas-negative-powers.md).
