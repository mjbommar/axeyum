# ADR-0175: Deterministic open-addressed AIG unique table

Status: accepted
Date: 2026-07-15

## Context

ADR-0174 moves the leading GQ5 question from CNF fusion to AIG construction
cost per added node. The warm native-lineage profile already times complete
term-to-AIG lowering, but a node count alone cannot distinguish Boolean
simplification, structural reuse, allocation, term-memo traffic, and literal
copying. Timing every primitive AIG request would itself perturb the hot path.

Glaurung `d79010a` and Axeyum `17f7747f` therefore advance the opt-in warm
profile to v4. Existing deterministic AIG counters classify primitive AND
requests; new profiling-only lowerer counters expose memo lookup/reuse,
operand/root literal-vector copies, term-bit writes, and symbol inputs. Axeyum's
summarizer accepts v1--v4, requires exact v4 field sets and partitions, and
aggregates only homogeneous schemas. Ordinary lowerers do not increment the
new counters.

The bounded Dptf control shows that the AIG unique table receives a minority of
primitive requests, but almost every request that reaches it is an insertion.
The existing `BTreeMap` therefore pays ordered-tree lookup and allocation on a
low-hit, construction-heavy stream. This selects one isolated data-structure
ablation before a broader lowering-ownership change.

## Decision

Replace the AIG AND-pair `BTreeMap` with an in-tree deterministic open-addressed
unique table.

- Canonical `(lhs, rhs)` ordering and caller request order continue to determine
  node IDs and AIG/AIGER output.
- A fixed integer mixer hashes the complete pair; equality resolves collisions.
  No randomized state or iteration order enters solver output.
- Linear probing uses no deletion and grows at a 70% load ceiling from a
  power-of-two capacity, so the first empty slot proves absence.
- Rehashing may change private slot positions only. It cannot change node
  identity, construction order, evaluation, lift maps, CNF, or proof replay.
- Construction telemetry retains the same exact semantic classification.

The implementation becomes the default because the repeated unprofiled native
gate improves every driver with unchanged decisions, scopes, root traffic, AIG
and CNF structure, while memory remains effectively flat.

## Evidence

The v4 Dptf control validates 561/561 decided and agreed records. It adds
284,870 AIG nodes in 40.989 ms of profiled bit blast (143.89 ns per added node):

- 786,558 primitive AND requests: 450,328 trivial simplifications (57.25%),
  24,698 absorption/consensus simplifications (3.14%), 34,982 unique-table hits
  (4.45%), and 276,550 new AND nodes (35.16%);
- 311,532 requests reach the unique table (39.61% of all requests), with an
  11.23% hit rate and an 88.77% insertion rate; and
- lowerer bookkeeping performs 586,624 operand-literal copies, 333,340
  term-bit writes, and 2,738 root-literal copies: 3.24 copied/written literals
  per added node.

The candidate Dptf profile preserves every outcome, structural total, CNF gate
counter, AIG request counter, and lowering-work counter exactly. Profiled bit
blast falls 40.989 to 26.196 ms (-36.09%). Five order-balanced unprofiled
control/candidate pairs all improve: Axeyum mean falls 238.36 to 224.10 ms
(-5.98%) and median falls 237.7 to 222.3 ms (-6.48%), with identical 561-check
path/root traffic and effectively flat median RSS.

The required wider gate uses three order-balanced pairs on each established
driver. Each policy decides and agrees 20,958/20,958 checks across the three
repetitions; root/prefix/pop/session traffic is identical and there are no
fallbacks or resets.

| Driver | `BTreeMap` Axeyum mean | Open-addressed mean | Change | Ratio to same-stream Z3, before -> after | Median RSS, before -> after |
|---|---:|---:|---:|---:|---:|
| `win10-vwififlt` | 4,821.77 ms | 4,438.67 ms | **-7.95%** | 1.069 -> 0.980 | 136,700 -> 134,960 KiB |
| `sqfs-intel-DptfDevGen` | 241.90 ms | 226.60 ms | **-6.32%** | 0.581 -> 0.544 | 77,564 -> 75,528 KiB |
| `windows-update-intel-audio-IntcSST` | 423.07 ms | 401.27 ms | **-5.15%** | 0.171 -> 0.160 | 128,036 -> 128,556 KiB |
| weighted three-driver round | 5,486.73 ms | 5,066.53 ms | **-7.66%** | 0.742 -> **0.680** | diagnostic only |

The aggregate ratio improves 8.34%. The +0.41% IntcSST median-RSS movement is
below the process-level timing/noise boundary and is outweighed on the other
two drivers; no driver shows a material memory regression.

One accepted-table v4 process per driver then validates all 6,986 records and
the same 8,758,247 added AIG nodes / 11,734,335 clauses. It observes 137.44
million primitive AND requests; 93.31% simplify trivially and only 6.54% reach
the unique table, but those nearly nine million probes are still worth
removing from ordered-tree search. Profiled bit blast is 1.221 seconds versus
ADR-0172's approximately 1.624 seconds (-24.8%); CNF and SAT absolute time stay
at approximately 3.12 and 1.24 seconds. The new weighted diagnostic shares are
CNF 46.55%, SAT 18.48%, and bit blast 18.21%.

Nine AIG tests cover structural hashing, truth tables, deterministic IDs,
deterministic AIGER, growth, and repeated lookup. All 33 BV tests and four
public incremental-attribution tests pass before the native gate.

## Alternatives

Keeping `BTreeMap` was rejected by the repeated native result. `HashMap` with
randomized state was rejected because determinism is a public contract and no
random seed belongs in AIG identity. Adding an external hash-table dependency
was unnecessary for a fixed two-literal key. Per-request wall-clock timing was
rejected because hundreds of thousands of clock reads distort the 41 ms Dptf
phase being measured. Removing the term memo or borrowing child vectors was
not combined with this change: ADR-0152 already shows that a superficially
redundant ownership rewrite can lose end to end, and v4 now provides a separate
future gate for literal-copy work.

## Consequences

The first native-lineage AIG tranche is accepted and production semantics stay
unchanged. The accepted warm three-driver ratio improves from approximately
0.746 to 0.680 against the actual same-stream Z3 client path; this is not a
cold pre-parsed-Z3 claim.

GQ5 now yields back to the larger product gates: calibrate lineage memory and
capacity admission, widen GQ10 drivers, and keep profiled/unprofiled bars
separate. Revisit operand-vector borrowing or compact lift-map writes only if a
fresh profile and an isolated ownership design can beat this new baseline.
CNF is again the dominant measured diagnostic stage; internal AND flattening
remains deferred, GQ4 remains off, and SAT remains behind CNF.
