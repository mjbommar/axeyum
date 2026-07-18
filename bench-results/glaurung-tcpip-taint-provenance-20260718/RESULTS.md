# Glaurung tcpip taint-provenance correction

Date: 2026-07-18

## Result

The two stable Z3-only AnyModel rows on the first 15 tcpip functions are raw
analysis artifacts, not established double-fetch true positives. Glaurung
discarded generic `Arg0` ancestry when an uninitialized load minted a fresh
symbol and relabeled the value `*attacker`. The accepted correction preserves
the exact source as `*Arg0`, `**Arg0`, and so on. Both authority runs then have
zero findings under ioctlance's normal high-confidence gate.

This corrects the interpretation of ADR-0236 through ADR-0239. Their raw
determinism and authority-parity results remain reproducible, but the raw union
is not a finding-recall ground truth and must not be the success target for the
next concretization-policy sweep.

## Source and input identity

- Glaurung isolated branch: `axeyum-concretization-policy-a0`
- Glaurung revision: `845239f0b120916b93ce224272ef8225c62b11e4`
- Axeyum measurement revision: `616737ead1eba2a7d4639701c4df172a51f2fffe`
- tcpip SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`
- fixed work: first 15 of 338 reachable functions
- common solver check wall: 250 ms
- solve budget: 300,000
- process wall: 1,800 seconds
- repetitions: two per authority and policy, order balanced by the committed
  authority runner
- both repositories are clean before and after every recorded run

The raw reports retain binary hashes, environment, per-run findings, solver
work, source identity, and post-run identity:

| artifact | SHA-256 | accepted meaning |
|---|---|---|
| [`any-model-raw-authority.json`](any-model-raw-authority.json) | `24eb804d82136cdcee4069b80ac656dafc9b11bb24edf80f1f3bed4edb1aaa64` | rejected raw parity control |
| [`min-unsigned-raw-authority.json`](min-unsigned-raw-authority.json) | `304802a12ba3b32799bd000698fa730b42ac9d0ff0c0d312f8323247d9463aa7` | exact least-unsigned raw authority parity |

## TDD correction

The red explorer test creates an uninitialized load through an address carrying
both `Arg0` and `SystemBuffer`. Before the correction it observes only
`["*attacker"]`; after the correction it requires the exact stable set
`["*Arg0", "*SystemBuffer"]`.

`TaintSpec` now stores a set of labels per symbol, `mark` accumulates rather
than overwrites, provenance queries flatten every source, and uninitialized
loads prefix each address source independently. All 18 focused explorer tests
pass under `solver-axeyum`; both sole-authority release examples build from the
same corrected source.

## Function and trace classification

Public PDB data maps section offset `0001:29296` to
`TcpSendTrackerMarkTransmits`. Module data places it in `sendtracker.obj`, and
the procedure record gives code size 2,104 bytes, beginning at virtual address
`0x1c0008270`. The two rows are internal traversal instructions:

```text
1c000830d: subl -0xc(%rax), %ecx
1c000832e: movq 0x8(%rax), %rcx
```

A freshly captured Z3-authoritative ordered trace validates with 14,549 events,
771 paths, 2,477 unique queries, 586 assertions, 3,079 checks, and 1,405 model
reads. At `0x1c000832e` its address choice is:

```smt2
(bvadd (_ bv8 64)
  (bvxor (bvxor (bvadd sym0_64 (_ bv48 64)) sym5_64) sym7_64))
```

`sym0_64` is generic `Arg0`; the later symbols are fresh values reached through
that generic ancestry. The corrected raw rows carry `**Arg0`, which
ioctlance's `is_attacker_real` intentionally rejects after stripping
dereference prefixes.

## Corrected authority observations

| policy | Z3 raw | Axeyum raw | stable raw relation | high confidence |
|---|---:|---:|---|---:|
| AnyModel | 128 | 126 | 126 shared; Z3-only `0x1c000830d` and `0x1c000832e` | 0 / 0 |
| least unsigned | 110 | 110 | byte-identical under both authorities | 0 / 0 |

AnyModel repeats use 3,079 Z3-authority and 2,991 Axeyum-authority solver calls.
Least unsigned repeats use 80,563 calls under either authority, including 1,206
choice attempts, 1,204 completed minima, two infeasible paths, and 79,466
probes, with zero inconclusive choice. Every least-unsigned raw row carries
only `Arg0`, `Arg1`, `*Arg0`, or `**Arg0`, so the normal confidence set is
empty without another expensive rerun.

## Planning consequence

The next policy work remains a sweep of one `ConcretizationPolicy` knob, not a
new algorithm program. Its preregistered gate must:

1. rebaseline every policy after the provenance correction;
2. publish raw, confidence-gated, and independently labeled partitions;
3. select a fixed-work corpus with nonzero validated positives before scoring
   recall or precision;
4. never require a candidate to maximize or contain the arbitrary-model raw
   union;
5. record work and cost, especially the roughly 79k extra probes incurred by
   least unsigned on this small slice;
6. begin symbolic memory only if the cheap corrected sweep leaves validated
   coverage headroom that value-selection policy cannot close.

The remaining 33 arbitrary-only rows from the older four-schedule comparison
are unclassified raw diagnostics. They are a labeling queue, not a known set of
missed bugs.
