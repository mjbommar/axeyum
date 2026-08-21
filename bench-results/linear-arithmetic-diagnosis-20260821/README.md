# Linear-arithmetic deficit diagnosis — per-file data (2026-08-21)

Backing data for
[`docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md`](../../docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md),
which executes ranked gap #1 of the
[2026-08-21 SMT capability gap analysis](../../docs/plan/gap-analysis-smt-solvers-2026-08-21.md).

These are the per-file sidecars the QF_LRA / QF_IDL / QF_RDL / QF_UFLIA entries in
[`PARITY.md`](../PARITY.md) name in their `per-file detail` row and that do not
exist in the tree: `bench-results/parity-details/` is gitignored (`.gitignore:51`),
so only `QF_BV.tsv` survives, force-added. Nothing here replaces a `PARITY.md`
entry — the reference below is **z3 4.13.3, not cvc5**, because cvc5 is not
installed on this host.

## `QF_{LRA,IDL,RDL,UFLIA}.tsv` — 200 rows each

The pinned competition lists (`../parity-lists/<div>.txt`, sha256 unchanged from
the recorded entries), each file run twice at a 24 s wall budget, 12 GiB
address-space cap, external kill at 32 s.

| column | meaning |
|---|---|
| `file` | benchmark path |
| `declared` | the benchmark's `:status` (`none` if absent) |
| `bytes` | file size |
| `axeyum` | `sat` / `unsat` / `unknown` / `HARDKILL` (still running at 32 s) / `error: …` |
| `unknown_kind` | the `UnknownKind` the competition CLI is required to suppress |
| `axeyum_ms` | wall ms |
| `z3` | z3 4.13.3 verdict at `-T:24` |
| `z3_ms` | wall ms |
| `detail` | the `UnknownReason` detail string, truncated to 200 chars |

`HARDKILL` is this probe's label, not the shipped solver's behaviour: the
competition CLI's watchdog prints `unknown` at ~25 s on the same files. Both
count as unsolved.

## `ab-atom-cap-fallthrough.tsv` — 71 rows

The refuted A/B of §5.1: `lra_theory.rs:203` `ResourceLimit` → `Incomplete`, so
the 1,024-atom decline falls through to the legacy fallback instead of ending the
query. 0 new decides; 54 memory aborts past 12 GiB.

## `ab-uflia-core-minimization.tsv` — 400 rows

The confirmed A/B of §5.2/§6: `dpll_lia.rs:48`
`MAX_MINIMIZED_THEORY_CORE_ATOMS` 128 → 4 096. QF_UFLIA 92 → 109 (+17),
QF_IDL 65 → 64 (the one loss re-decides on a quieter box, both binaries), zero
disagreements against z3 or the declared `:status`.

Reference frame: 16-thread i5-12600K, sweep at `-P 8` with three other lanes on
the box, load average 9–22. Decided counts are therefore a lower bound; QF_LRA
reproduced its recorded 86/200 exactly, the other three came in 2–6 files low.
