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
