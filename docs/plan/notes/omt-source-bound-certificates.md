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
