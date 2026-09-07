# The trust ledger, read from a corpus sweep — 2026-09-07

What `smtcomp_cli --evidence` now prints, and what it says. The `trusted=` field
was added the same day
([lane diary](../../docs/research/12-performance/certificate-chain-2026-09-07.md)):
before it, `EvidenceReport::trusted_steps` appeared nowhere in the CLI's output,
so "how many refutations carry an ADR-1704 theory step" could only be asserted
per query from a test, never counted across a division.

## Method

Release `target/release/examples/smtcomp_cli`, `taskset -c 0-7`,
`--timeout-ms 8000` inside a `timeout -k 2 30s` hard-kill backstop, the **first
40 files** of each committed list in `bench-results/parity-lists/`. One TSV row
per file:

```
file    declared    verdict    kind    trusted    ms
```

`trusted` is the CLI's field verbatim: `0`, or `<n>:<label>[+],…` with `+`
marking a step this run certified.

**Forty files, not two hundred.** This is a certificate-coverage reading, not a
parity run; it is not comparable to the parity board's numbers and must not be
quoted as one.

## The harness fails

`scripts/trusted-step-sweep.sh` exits **1** when any file's verdict contradicts
its declared `:status`, so a clean run is a live check rather than a
decoration. Confirmed rather than asserted — `scripts/negative-control.smt2`
declares `:status sat` over a query that is plainly `unsat`:

```
lying.smt2  sat  unsat  unsat-farkas  1:farkas+  0
CONTRADICTION  …  declared=sat  got=unsat
SUMMARY|files=1|unsat=1|trusted_nonzero=1|modulo_theory=0|contradictions=1
exit=1
```

## Result

| division | files | `unsat` | carrying a trust step | of those, ADR-1704 | contradictions |
|---|---:|---:|---:|---:|---:|
| QF_IDL | 40 | 3 | **3** | **2** | 0 |
| QF_LIA | 40 | 4 | 4 | 0 | 0 |
| QF_UF | 40 | 16 | 1 | 0 | 0 |
| QF_LRA | 40 | 0 | 0 | 0 | 0 |

Reproduced twice on this host with identical counts.

### Reading it

- **QF_IDL is the ADR-1704 result.** All three refutations carry a step. Two are
  `sat-refutation-modulo-theory`, which is uncertified by construction; the
  third is `sat-refutation+`, a refutation where the theory contributed no lemma
  at all, so the Boolean DRAT alone refutes the CNF and `check_drat` verified
  it. The grade is a subtraction on the artifact
  (`|extended| - |cnf|`), and here it is visibly deciding in both directions.
- **QF_LIA's four steps are `farkas+` and are not new.** They come from the
  pre-existing Alethe route. What is new is that a sweep can see them.
- **QF_UF is the standing gap.** Sixteen refutations, one step. Fifteen arrive
  as `unsat-bool-euf-online`, whose evidence producer attaches no trusted step
  at all, so moving `euf_egraph` onto the proof-producing core does not surface:
  those refutations never reach the arm that reads the artifact channel. Moving
  a route is necessary and is not sufficient.
- **QF_LRA decided nothing at an 8 s budget.** Its row is a budget statement,
  not a certificate statement. Do not read the zero as a coverage gap.

### What this does NOT measure

The cost of dispatcher-wide proof recording. `produce_evidence` now records for
the whole dispatch, bounded by the 8M-literal budget. These sweeps ran without
complaint, but no before/after timing A/B was taken, so the recording overhead
on the evidence front door is **not measured** — not "free".
