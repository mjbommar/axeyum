# Lane: cas-expression-wire — portable exact source expressions

<!-- plan-section: lane-status -->

**Expression wire (`WIP`, cas-expression-wire, 2026-10-11).** Child of
ff9e9301e, isolated from the Pi repair broad runner. ADR-6100 specifies tagged
version1 JSON preserving Pi/Var(pi), ordered syntax, wide exact rationals and
all unary heads. Rust and Python APIs implemented; four Rust transport tests
pass, with every head and malformed/resource controls. Fresh native build
passes; eight Python suites collect/pass279, zero skips. Stub generation and runtime name/arity/type ratchets pass. Private canonical
guard mutation passes (four baseline, three plus one mutant failure).
Read-only format and focused CAS-library Clippy pass. Broad runner64759 is
on c34b7bc89: format passes and CAS 2140 pass/zero fail/11 ignored; workspace
remains live. Pi certificate child retains this source while implementing replay. Parent CAS broad run is red: 2139 pass/one failure/11 ignored;
Gaussian test expects a false opaque-atom inequality between equal functions.
Require Unknown before radical simplification while preserving certified
integration and simplified equality controls. Parent workspace remains pending.
Focused Gaussian regression passes one test, retaining certified integration.
Next: full CAS/workspace gates and remaining consumer/certificate work;
checker controls and broad gates. Certificate transport and kernel admission
remain separate unfinished requirements; no full goal completion claim.
