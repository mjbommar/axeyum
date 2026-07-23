# SMT-COMP credited full-population F1 fixture result

Status: integrated on `origin/main`; live process-free preparation not yet
accepted
Date: 2026-07-23
Plan: [credited full-population execution](smtcomp-credited-full-population-plan-2026-07-23.md)

## Result

The fixture-first preparation and supervised-wave mechanisms required by F1
are implemented. No solver, SSH allocation, host probe, systemd unit, or NAS
run root was started or mutated while producing this result.

The implementation now provides:

- one immutable population contract binding all three solver cells to the
  45,905-row full list and v2 manifest;
- the exact 96-shard partition, 48 two-shard initial allocations, 96 one-shard
  different-host retries, and 16 three-host waves;
- the frozen two-worker/two-core/16-GiB/zero-swap/64-PID resource envelope;
- physical selected-file rehashing through the admitted S4 ledger and a live
  gate on the frozen list/manifest/accepted-root hashes;
- process-free composition and replay validation of three run manifests, three
  plans, three schedules, and 432 allocation command manifests;
- self-sealed wave checkpoints with contiguous-prefix restart skipping and
  complete cumulative population accounting;
- fail-closed scheduler decisions for unclosed, failed, or lost allocations,
  signal-boundary pause, and completed-cell state;
- exact `k10temp-pci-00c3 / Tctl / temp1_input` parsing, observations no older
  than 60 seconds, a 90.000 C stop threshold, and an 80.000 C cooldown-release
  threshold;
- an exact remote `systemctl --user stop <registered E3 unit>` helper that
  rejects other namespaces, noncanonical evidence, blanket process matching,
  unsuccessful stops, and still-active postconditions; and
- a dependency-injected one-wave supervisor that drains every started handle
  through a terminal after pause, partial launch failure, or thermal stop and
  publishes a checkpoint only after all three registered allocations complete.

The tiny admitted fixture contains two physical benchmarks but exercises the
full 96-shard topology. It produces all 432 process-free commands with
`launch_authorized=false`; fixture commands carry the hidden unadmitted-fixture
flag and cannot satisfy the live 45,905-row preregistration gate.

## Mutation and interruption coverage

The focused module now has 28 tests across F1 and the process-free F2
preparation boundary. It rejects population count/list/manifest/order
drift, resource and topology drift, same-host or missing retries, missing or
misbound thermal observations, stale observations, threshold and hysteresis
mutations, noncontiguous checkpoints, failed checkpoint terminals, mutated
command inventories, unexpected attempts, non-exact systemd stops, and live
promotion of the tiny fixture.

The supervised-wave fixture additionally proves:

- a successful three-host wave closes exactly one deterministic checkpoint;
- `SIGINT`/`SIGTERM`-style pause state is observed at the wave boundary only;
- one overheated allocation is stopped without stopping its two peers;
- every already-started allocation remains supervised through a terminal;
- thermal failure and partial launch failure publish no checkpoint; and
- an unclosed durable attempt causes zero launcher calls.

## Gates

The following pass on the rebased SMT topic branch:

```text
python3 -m unittest scripts.tests.test_smtcomp_full_population
28 tests, OK

./scripts/check-smtcomp-resume.sh
115 tests, OK (one expected live-host skip)
runner/scoring/pipeline/selection/provenance checks, OK
generated resume contract, selection authority, and repaired-P0 comparison, OK

./scripts/check-links.sh
all links ok
```

`cargo fmt --all --check` still stops on the previously recorded out-of-lane
bench/CAS formatting drift. The SMT lane did not edit or reformat those files.

The focused Lean store check still reaches the already reported cross-lane
current-source identity failure. Its sole observed failure is
`test_preregistered_source_identities_are_frozen`: the now-integrated SMT-owned
`resume_fs.py` hashes to `b05c32185d75d579...`, while
the test still expects historical identity `1968e7b6424c2dd9...`. The integrated
[Lean R7 plan](lean-complete-parity-current-source-identity-r7-plan-2026-07-23.md)
correctly keeps historical evidence frozen and preregisters a distinct current
source identity; its implementation has not yet landed. This result does not
edit Lean-owned validators, tests, or evidence.

Therefore branch-wide `just check` and live F2 preparation remain blocked on
those two explicitly out-of-lane gates even though the SMT-specific fixture
gate is green.

## Integration and next authorization boundary

The integrator landed the final supervised-wave implementation (`25f93413`) by
merge `8dc788b5`. The later
readiness gate (`bfb0cb87`, merged by `e5b1921f`) and F2 preparation mechanism
(`ea9781c9`, merged by `502e8875`) are also integrated. Current `origin/main` is
`502e8875`; F1 is no longer waiting on integration.

F2 may publish one live
process-free `launch_authorized=false` preparation only when all of the
following are simultaneously true:

1. the exact F0/F1 bytes are on `origin/main`;
2. local source, staged source, release-binary source, and `origin/main` are the
   same clean revision;
3. branch-wide `just check` is green;
4. the accepted full population rehashes to the frozen identities;
5. the three hosts reproduce the registered environment and thermal sources;
6. the repaired-P0 roots and incident sentinels still validate; and
7. preparation publishes no allocation attempt, resource session, or solver
   record.

F1 does not authorize live preparation or execution.

The process-free F2 completion candidate is implemented separately in the
[F2 implementation result](smtcomp-credited-full-preparation-f2-implementation-2026-07-23.md).
Its implementation bytes are integrated; this result document still requires
normal green-gated integration. No live host probe, sentinel, NAS publication,
or allocation launch has occurred.
