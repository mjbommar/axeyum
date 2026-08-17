# A6 — what the 37 bare QF_BV UNSAT rows actually are

A6 asks to "use route provenance — not query syntax alone — to split the 38
QF_BV bare UNSAT rows". Measured 2026-08-17. The answer is that they are not a
routing mystery at all.

## The rows

From the evidence-mode re-run (`bench-results/PARITY.md`, QF_BV 2026-08-17;
per-file detail in the gitignored `bench-results/parity-details/QF_BV.tsv`):

```
axeyum unsat 130 · certified 93 · BARE 37
bare rows by evidence_verdict:  37  unsolved
bare rows by evidence_kind:     37  none
```

**Every one is `unsolved` / `none`.** They are not certificates we produced and
cannot check — they are certificates that were never produced. That already
rules out the reading "some route emits an object we then fail to validate".

## The decision is not the problem

Sampled four of the 37 with `diagnose_evidence`, each as a bounded subprocess:

```
bv-term-small-rw_539.smt2   solve: unsat   0.692 ms   (qf-bv: decided unsat)
bench_17078.smt2            solve: unsat 263.017 ms
bench_192.smt2              solve: unsat  92.476 ms
bench_3822.smt2             solve: unsat  93.114 ms
```

Sub-millisecond to a quarter-second to DECIDE, against a 60-second evidence
budget that expired. The same route that decides instantly cannot produce a
checkable object within budget. So the split by provenance is: one route,
deciding fine, and certificate production is where the cost is.

## What production is spending, measured honestly

Under an 8 GB address-space cap:

- `bv-term-small-rw_539.smt2` — production ABORTS: `memory allocation of 16
  bytes failed`. It wants more than 8 GB.
- `bench_17078`, `bench_192`, `bench_3822` — no allocation failure and no
  completion within 45 s. They run long inside 8 GB.

So it is **not** uniformly memory-bound; on this sample one of four is, and
three are time-bound at 8 GB. A larger sample would be needed to put a ratio on
that, and this note deliberately does not.

The connection worth carrying: unbounded evidence production is the same
behaviour that OOM-killed a session on this box the same day (a sweep reached
125 GB anon-rss). `scripts/check-evidence-portability.sh` therefore runs every
file as a capped subprocess, and any tooling that produces evidence over a
corpus should do the same.

## What this changes about A6

- The "38" is now 37 on the re-run, and the two counts are NOT comparable — the
  re-run was on different hardware at a different load, and `PARITY.md` says so
  in the entry.
- `proof_production_errors=2` in the parity snapshot is STALE, not live: the two
  QF_NIA `int.pow2` errors were fixed in `3cc574c70`, but the committed
  dominance audits predate the fix. Closing A6's "zero production errors" needs
  that audit regenerated, not more code.
- The remaining work is a performance question — make certificate production
  affordable for these shapes — not a provenance question. That is a different
  kind of task from the one A6's text describes, and it should be renamed
  before someone spends a day looking for a routing bug.
