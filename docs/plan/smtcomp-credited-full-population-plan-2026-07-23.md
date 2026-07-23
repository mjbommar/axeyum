# SMT-COMP credited full-population execution plan

Status: preregistered design; F1/F2 process-free mechanisms and publication
fixtures integrated; live F2, F3, and F4 not yet accepted
Date: 2026-07-23
Selection authority: [accepted S4 result](smtcomp-official-selection-final-s4-2026-07-22.md)
Harness admission: [S5 result](smtcomp-harness-admission-s5-result-2026-07-23.md)
P0 prerequisite: [combined comparison result](smtcomp-repaired-p0-combined-comparison-result-2026-07-23.md)
Execution contract: [accepted ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)
Selection contract: [accepted ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)

## Objective and claim boundary

Measure Axeyum, cvc5, and Bitwuzla over one exact 45,905-file SMT-COMP 2026
Single Query selection. Publish a complete per-logic decide/decline/wrong map and
same-population pairwise/three-solver comparison without carrying forward the
repaired-P0 scope asymmetry.

This remains an internal 20-second, one-core-per-process measurement. It is not
an official SMT-COMP result, a 1,200-second competition-equivalence claim, or a
general performance-parity claim. A solver receives decision credit only for
`sat` or `unsat`; `unknown`, timeout, unsupported, parser failure, and other
typed non-decisions remain explicit.

No preparation or solver execution is authorized by this document alone.

## Frozen selection authority

Accepted root:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/accepted-322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698
```

| Artifact | Bytes / rows | SHA-256 |
|---|---:|---|
| `complete.json` | 1,172 bytes | `322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698` |
| `official-selected.txt` | 4,066,816 bytes / 45,905 rows | `49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b` |
| `selected-files.jsonl` | 11,096,728 bytes / 45,905 rows | `540fe29f2bc28e858b103fcd806eab709f58ed69b67d8cb95bd41bcdbaa87f39` |
| `decisions.jsonl` | 324,460,399 bytes / 450,472 rows | `0f44fff7d550a3aac19e1d3c86e8628db9ac3a6c85bd9dc54affc50ff9f4aaf9` |
| Full absolute execution list | 9,024,556 bytes / 45,905 rows | `9d5f51d5b84c65f6c2ab03db822b185f60e47a505ec93284363dbd229305ac2b` |
| Full v2 execution manifest | 19,266,433 bytes / 45,905 rows | `8e68f29c63f11867304d5fe03eb5a2c47e0cfd15ffdcb0b5b3878dd056734791` |

The selected population contains 15,148,369,947 physical bytes and 88 logics.
The decision ledger partitions it into 9,927 known `sat`, 17,427 known `unsat`,
and 18,551 absent-status rows. Preparation must stream and validate all complete
selection artifacts, physically rehash all selected bytes, and reproduce the
full list and v2 manifest hashes above.

All three cells must name the exact same full list and manifest. A
solver-specific subset, reordered list, or same-sized replacement rejects
before an attempt root is published.

## Solver and source authority

The cells run sequentially in this order:

1. Axeyum, built `--release --locked` from the clean integrated source revision,
   with a 19-second internal timeout inside the 20-second runner ceiling;
2. cvc5 1.3.4, candidate SHA-256
   `7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee`;
3. Bitwuzla 0.9.1, candidate SHA-256
   `d98164badcd34c12ccbbd9e5aab9373854bb187e79f99ccda4ec2aa9951c0eab`.

Unsupported logics remain part of each oracle cell and must decline or fail in
their exact typed form. Bitwuzla is not restricted to the repaired-P0 FP slice.

Live preparation requires all of the following:

- the plan and preparation implementation are byte-identical to `origin/main`;
- local `HEAD`, `origin/main`, the staged source revision, and the release
  binary source revision are identical;
- the source tree is clean;
- branch-wide `just check` is green; and
- the repaired-P0 comparison and all three external result roots still
  validate.

The current mainline format drift recorded in the P0 comparison result blocks
live preparation. This lane must not reformat or commit the bench/CAS files that
own that drift.

The three historical FP/AUFLIA incident sentinels from the repaired-P0 plan run
again before publication. Any unsafe sentinel outcome rejects preparation.

### F2 host and sentinel evidence contract

The F2 completion must carry one separately sealed preflight record; hashes
transitively embedded in run manifests are not sufficient. The record binds:

- exactly three canonical host observations, in `s5`, `s6`, `s7` order, plus
  the registrations reconstructed from those observations;
- the exact environment manifest reproduced from those observations and the
  same registrations present in every cell plan;
- exactly eight sentinel observations in this order: QF_ABVFP on Axeyum, cvc5,
  and Bitwuzla; QF_BVFP on the same three; then QF_AUFLIA on Axeyum and cvc5;
- the exact staged solver binary, sentinel input, stdout, and stderr hashes;
- monotonic start/end timestamps for every sentinel and one capture interval
  enclosing all host and sentinel observations; and
- a publication deadline no more than 30 minutes after the first captured
  observation. Preparation after that deadline rejects and requires fresh
  probes and sentinel runs.

All staged binaries, sentinel inputs, sidecars, the environment manifest, and
the preflight record live beneath the preparation attempt and enter its complete
artifact ledger. Live QF_ABVFP and QF_BVFP rows require completed, exit-zero
`unsat` from all three solvers. Live QF_AUFLIA requires completed, exit-zero
`sat` from cvc5; Axeyum may only complete with `sat`/`unknown` or time out with
no verdict. Any `unsat`, signal, resource termination, malformed identity,
missing row, duplicate row, stale interval, or output mutation rejects.

The completion schema advances before any live F2 publication. Historical
repaired-P0 records remain immutable and are not rewritten; the reusable
sentinel validator accepts only the new timestamped schema for F2.

## Resource and shard contract

The run reuses the registered `s5`/`s6`/`s7` NFSv4.1 environment class with a
larger but still bounded schedule:

- 96 striped shards; shards 0--16 contain 479 rows and 17--95 contain 478;
- 48 initial allocations, each owning consecutive shards `[2i, 2i+1]`;
- allocation `i` belongs to `s5`, `s6`, or `s7` by `i mod 3`;
- 16 waves per solver cell, each wave containing exactly one allocation on each
  host;
- two workers, two CPU cores, 16 GiB aggregate memory, zero swap, and
  `pids.max=64` per active host allocation;
- 8 GiB and one core per solver worker;
- 20,000 ms wall and CPU limits per benchmark; and
- `AYU_THREADS=1`, `OMP_NUM_THREADS=1`, and `RAYON_NUM_THREADS=1`.

At the registered ceiling, one allocation lasts at most about 2.67 hours, one
cell about 42.51 hours, and all three cells about 127.51 hours. These are
worst-case envelopes, not duration predictions.

Every shard has one preregistered generation-1 retry allocation on a different
host. Retries own exactly one shard. Initial owner `s5` retries on alternating
`s6`/`s7`; `s6` retries on `s7`/`s5`; `s7` retries on `s5`/`s6`. A retry may run
only after exact liveness, lease, resource-session, failed-attempt, and durable-
record validation for its named initial allocation.

## Wave scheduler and safe stop

The P0 coordinator is insufficient for a multi-day run because it assumes one
three-allocation wave and keeps live `Popen` handles in one process. The full-
population implementation must add a fixture-proven wave scheduler with these
rules:

1. At most one allocation per host and one solver cell may be active.
2. Completed allocation terminals are validated and skipped on restart.
3. An attempt without a terminal blocks new launches; it is never guessed dead
   or duplicated.
4. `SIGINT`/`SIGTERM` requests a clean wave-boundary pause. Active allocations
   remain supervised through their terminals; no later wave starts.
5. A failed/lost allocation stops the cell. Recovery is a separate exact-shard
   action; remaining initial waves do not continue around it.
6. Cell completion, raw export, and comparison publish only after all 96 shards
   and all E1/E2/E3 evidence validate.

The scheduler publishes a self-sealed wave checkpoint after every completed
wave, binding the run/plan, completed allocation attempts/terminals, record
count, and next wave. Checkpoints are derived state and cannot substitute for
the underlying evidence.

## Thermal contract

The repository operating guide requires backing off near 90 degrees Celsius.
Each host currently exposes the CPU control temperature at
`k10temp-pci-00c3 / Tctl / temp1_input` through `sensors -j`.

Before each wave and at intervals no longer than 60 seconds while a wave is
active, the scheduler must publish a canonical per-host thermal observation.
A missing sensor, malformed JSON, host mismatch, or temperature at or above
90.000 C rejects a new launch. Resume requires all hosts below 80.000 C.

If an active host reaches 90.000 C, the implementation must stop only that
allocation's exact registered systemd unit, preserve a typed thermal-stop
record plus the ordinary failed allocation/resource evidence, and stop the
cell. Blanket `pkill`, parent-only termination, and unrecorded continuation are
forbidden. The exact-unit stop and subsequent one-shard recovery path require
fixture tests before any live preparation.

## Adjudication and publication

After each cell, validate every result record and publish a completion-last
external result. Stop before the next solver on any known-status contradiction.
After cvc5 and Bitwuzla, also stop on any shared `sat`/`unsat` disagreement.

The final generated comparison must report, overall and per logic:

- reported `sat`/`unsat`/`unknown`/no-verdict counts;
- known-correct, known-contradiction, unadjudicated-decision, and no-decision
  counts;
- typed termination counts;
- pairwise both/left/right/neither/disagreement projections; and
- three-solver three/two/one/none/disagreement projections.

All pairwise and three-way populations are exactly 45,905. Do not publish one
scalar ranking that hides per-logic coverage, absent-status decisions, or
termination classes. Timing/PAR-2 publication requires a later explicit review
of host comparability and recovery effects.

## Required fixture and mutation gates

Before live preparation, tiny fixtures must prove:

- exact full-list identity for all three cells and rejection of subset/order/
  content drift;
- the 96-shard, 48-allocation, 16-wave partition and all 96 different-host
  retries;
- per-host concurrency, worker, CPU, memory, swap, and PID caps;
- deterministic wave checkpoints and restart skipping;
- no launch after an unclosed, failed, or lost allocation;
- clean signal pause without an orphan or next-wave launch;
- thermal sensor/source/threshold/hysteresis mutation rejection;
- exact-unit thermal stop without blanket process matching;
- completion-last external results and complete 45,905-row accounting; and
- stale source, plan, binary, environment, selection, and generated-artifact
  rejection; and
- missing/reordered/duplicate/stale host or sentinel evidence, unsafe sentinel
  outcomes, and mutated sentinel input/output rejection.

The process-free
[publication fixture](smtcomp-credited-full-publication-fixture-2026-07-23.md)
implements the remaining external-cell and same-population comparison boundary.
It does not provide a live F2 preparation, construct F3 execution authority, or
claim F4 results.

## Milestones and authorization

- **F0 — this plan:** freeze population, resources, waves, recovery, thermal,
  adjudication, and claim boundaries. No NAS write or solver execution.
- **F1 — fixture implementation:** add generic full-population preparation,
  wave scheduling, exact thermal observation/stop evidence, and mutation tests.
  No live NAS mutation.
- **F2 — process-free preparation:** only after F1 and this plan are integrated
  on a green `origin/main`, build/stage binaries, rehash the full population,
  probe hosts/sentinels, and publish an empty `launch_authorized=false` root.
- **F3 — sequential execution:** only after the exact F2 result is integrated,
  execute Axeyum, then cvc5, then Bitwuzla through wave/recovery gates.
- **F4 — comparison:** publish the complete 45,905-row per-logic inventory and
  same-population comparison, then rerank the gap-closing program.

No milestone authorizes a later milestone until its exact result/source bytes
are integrated by the designated mainline owner.
