# Lane: cas-pi — distinguished constant and variable-safe semantics

<!-- plan-section: lane-status -->

**CAS pi (`WIP`, cas-pi, 2026-10-11).** Isolated from integration baf50f913.
Distinct Pi leaf and Rust/Python constructors now preserve constant identity;
ordinary Var(pi) no longer triggers constant evalf/enclosure/trig recognition.
Internal formulas and examples migrate to Pi; polynomial decoding preserves its
leaf and rejects forged source constant keys. Source-bound enclosure controls
cover both constant and bound-variable subjects. ADR-6000 remains proposed.
Core compile passes; five targeted Rust and 21 trig tests pass. Fresh native
build succeeds and sealed Python CAS suites pass 269 tests/zero skips, including
constructor, pi/Unicode parser and wrong-rewrite controls (hash/logs in notes).
Stub generation passes (27 modules/649 items), name/arity and type ratchets pass.
Same-interval constant/variable replay rejection strengthens the five Rust controls.
Private head-guard mutation passes: baseline five; mutant four plus one failure.
Parent runner21448: CAS 2140 pass/11 ignored; workspace is live. Child evidence
repair gates nonzero Pi polynomial claims and rejects raw atom aliases in both
producer and replay. Seven Rust controls pass. Fresh child native build passes; sealed Python suites pass 271/zero skips.
Both private replay-guard mutations kill exactly one of seven controls. Child
runner15629 on source286c6d445: CAS red (2139 pass/one Gaussian expectation
failure/11 ignored); workspace live. Expression-wire child fixes that unsafe
inequality expectation and focused Gaussian passes; broad child gates pending.
Canonical tagged serialization and reconstruction remain pending.
Version-1 traces and rational-only bridges explicitly decline unsupported Pi.
Next: finish stubs and full gates, source-binding guard mutation, portable Pi
encoding/replay and remaining consumer audits. No full Pi or goal completion claim.
