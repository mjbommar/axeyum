# OMT source-bound certificate validation

## Source f829f2a92 and storage recovery

Prior source 3ce2f60e4 passed 2 Farkas source-binding and 9 OMT tests. Fresh
Python package `/var/tmp/axeyum-omt-source-python-fv11_63u/package` imported
the rebuilt binary; SHA-256
`dbf382f850c122c5f4c84e74e8ce307eb53422013c30aacd69f543fc9762b87c`.
24 selected Python tests passed, no skips. Those results precede gold eligibility.

Gold runner28856 and mutation baseline89277 failed with ENOSPC, not test
failures. Root filesystem had 69 MiB available; /data0 had 4.1 TiB available.
Only lane-owned caches move. Mutation cache migration9388 succeeded; recovered
baseline/mutations run under42006 at
`/data0/axeyum/target/omt-source-bound-certificates-mutation`, logs
`/var/tmp/axeyum-source-farkas-recovered-*.log`. No mutation pass yet.

Migration36457 failed because the recovered build started before copying ended
and created conflicting destination directories. Recovered runner39580 keeps
its active `/data0/axeyum/target/omt-source-bound-certificates` cache. Original
remaining cache moves separately under68923 into
`/data0/axeyum/target/omt-source-bound-certificates-migration-remainder`; it
does not modify the active destination. Recovered gold log names:
`/var/tmp/axeyum-omt-gold-recovered-{rust,native}.log`. No gold test pass yet.

Parent replay mutation45506 and stub53264 also terminal-failed from ENOSPC.
Their passes are not credited. Parent mutation cache migration80296 targets
`/data0/axeyum/target/python-omt-results-mutation`; await terminal migration
before restarting that mutation job. Root has 3.6 GiB available at last check.

Continue the same live handles; never restart because a poll expires.

## Recovery verified

Migration68923 and80296 terminal zero; root available space increased to14GiB.
Recovered gold Rust phase39580 terminal zero: 10 passed, 0 failed/ignored,
0.12s (`/var/tmp/axeyum-omt-gold-recovered-rust.log`), source f829f2a92.
Its native phase remains live. Source-binding mutation42006 remains compiling;
parent replay mutation72743 reruns baseline and two guards on the migrated
private cache, logs `/var/tmp/axeyum-omt-replay-recovered-*.log`. Gold stub
generator89655 is live, log `/var/tmp/axeyum-omt-gold-stub.log`. No Python gold,
mutation, or stub success is claimed yet.

## Fresh gold Python results and required gates

Gold native39580 terminal zero, source f829f2a92 (later changes Python rules
regression/docs only). Sealed package
`/var/tmp/axeyum-omt-gold-python-dysm8rkh/package`; imported path checked.
SHA-256 `cbb2a2366509201c1ecabf45ef4db47582bea336c1e661a7852fcd1022e84979`.
Runner92902 terminal zero: 53 passed, 0 skipped, 4.37s across optimization,
SMT proof regressions, Rules dates/packs/statute deadline suites. Ten OMT tests
include checked gold max/min, lex prefix requirements and explicit missing
integer-cut and BV optimality evidence.

Required runner54092 is live, logs
`/var/tmp/axeyum-omt-gold-required-_volk68z/`. It runs all five z3 arithmetic
differentials, corpus plus four string front doors, full-feature solver library,
then workspace libraries. Per-job exit files are authoritative; confirm nonzero
counts before claiming a pass. Rust source remains frozen. Format runner20489
is pending. Stub89655 and mutations42006/72743 remain live.

Source-binding mutation runner42006 terminal zero: baseline 2 passed; removing
each atom/origin/column comparison yields exactly 1 passed / 1 intended failed,
exit101. Logs `/var/tmp/axeyum-source-farkas-recovered-{baseline,atoms,origins,columns}.log`.
Private snapshot restored; its lra.rs bytes exactly equal the current source
(hash 75cdc8b41c3b5aac1c295dc3832b876fec688600d9da7cf6e30669d42a1d7f80). Format20489 terminal zero.

## Replay mutations and generated API

Parent replay runner72743 terminal zero: 7 baseline passed; each constraint
model/value guard removal yields exactly 6 passed / 1 intended failed, exit101.
Logs `/var/tmp/axeyum-omt-replay-recovered-{baseline,constraints,objective}.log`.
Private snapshot restored. Stub89655 terminal zero: 27 modules/652 items.
Signature check against the sealed fresh gold extension: 1856 symbols, 5 aliases,
319 synthesized dunders. Type check: 1802 params, 1717 typed, 131 Any all
allowlisted, 46 Any returns, 95.3 percent across 27 stub files. Generated SMT
stubs include both classes, optimize, optimality replay and gold eligibility.
Required qf_lra_differential_fuzz exit zero: 8 passed, 0 failed/ignored, 31.82s.
Remaining required runner54092 phases are live, not passing yet.

## Detailed status before compaction


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
Gold stub generator89655 passes (27 modules/652 items); runtime signature
gate checks1856 symbols, type gate1717/1802 typed params. Parent replay72743
passes: baseline7; each constraint/value guard removal kills one intended test.
Required gates runner54092 live (five z3 fuzzes, five front doors, full solver,
workspace); logs `/var/tmp/axeyum-omt-gold-required-_volk68z/`. Rust frozen.
Source-binding mutations42006 pass: baseline2; each atom/origin/column guard
removal gives exactly one intended failure; private source restored.
First z3 LRA differential: 8 passed, zero failures/ignored. Other gates live.
Next: Boolean lowering binding,
strict-better certificates, model-plus-optimality Python results, serialization
and independent process replay, then required full gates. Missing evidence never receives gold credit.

## Five arithmetic differential gates

Source f829f2a92: qf_lra differential8, simplex fallback1, qf_uflra2,
difference logic4, qf_lia5: total20 passed, zero failed/ignored. Each terminal
exit file is0, and each log has an actual positive test count. Same required
runner54092 continues the corpus/string front doors, solver and workspace.
Initial lint invocation used the cargo wrapper without --batch, so it attempted
`cargo bash` and ran no lint. Corrected runner32215 uses wrapper --batch,
log `/var/tmp/axeyum-omt-gold-clippy-corrected.log` and raw JSON
`/var/tmp/axeyum-omt-gold-clippy.json`. No lint result yet.
