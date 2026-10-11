# Lane: omt-source-bound-certificates — original-query optimality evidence

<!-- plan-section: lane-status -->

**OMT evidence (`WIP`, omt-source-bound-certificates, 2026-10-11).** Child of
42c42e303; parent full tests stay immutable. ADR-6301 specifies reconstruction
of original LRA atoms, variable columns and assertion origins before accepting
carried Farkas multipliers. Added checker and two tests covering original/forged
sources, columns, origins and expired deadline. Focused runner 23596 terminal zero: 2 passed, 0 failed/ignored;
log `/var/tmp/axeyum-omt-source-bound-farkas.log`. Compiled source 3ce2f60e4.
Added original-context strict-better refutations through deterministic Int/Real
relaxation and replay_optimality; current optimum pin excluded. Regression
changes claimed maxima/minima to expose circular proofs. Generate after all
solves to stabilize relaxation columns; test box/lex certificate replay and
integer-cut-only optima with missing real refutation. Runner 42842 terminal
zero: 9 passed, 0 failed/ignored, 0.10s;
`/var/tmp/axeyum-omt-strict-better.log`.
Added Python replay_optimality with explicit None for missing evidence and
controls for max/min, integer-only cuts, unknown and BV results. Native rebuild
runner 30090 terminal pass. Sealed extension SHA-256
dbf382f850c122c5f4c84e74e8ce307eb53422013c30aacd69f543fc9762b87c:
24 Python tests passed, zero skipped. Added gold eligibility requiring model
and refutation replay for the entire lex prefix; gold Rust suite passes 10/zero failures/zero ignored (0.12s); fresh gold native
native build39580 terminal pass. Fresh gold binary SHA-256
cbb2a2366509201c1ecabf45ef4db47582bea336c1e661a7852fcd1022e84979:
53 selected Python tests pass, zero skips (4.37s). Build28856 and mutation baseline89277
failed from root filesystem ENOSPC, no test failures or green credit. Lane-owned
targets move to /data0; recovered gold runner39580 and mutation runner42006
use disk-backed targets. Migration36457 failed when the destination build started too early.
Remainder migration68923 and parent mutation migration80296 completed; root
space restored to14GiB. Parent replay mutations restart72743 on/data0.
Gold stub generator89655 is live; active target is untouched.
Required gates runner54092 live (five z3 fuzzes, five front doors, full solver,
workspace); logs `/var/tmp/axeyum-omt-gold-required-_volk68z/`. Rust frozen.
Source-binding mutations42006 pass: baseline2; each atom/origin/column guard
removal gives exactly one intended failure; private source restored.
Next: stubs and parent model replay mutations; Boolean lowering binding,
strict-better certificates, model-plus-optimality Python results, serialization
and independent process replay, then required full gates. Missing evidence never receives gold credit.
