# Budget-driven theory-core minimisation — per-file data (2026-08-21)

Backing data for
[`docs/research/05-algorithms/budget-driven-theory-core-minimisation-2026-08-21.md`](../../docs/research/05-algorithms/budget-driven-theory-core-minimisation-2026-08-21.md),
the shipped form of the one confirmed fix in the
[linear-arithmetic deficit diagnosis](../../docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md).

Nothing here replaces a `PARITY.md` entry. The reference below is **z3 4.13.3,
not cvc5** — cvc5 is not installed on this host — and only
`scripts/parity-run.sh` may move a recorded ratio.

## `abc-QF_UFLIA.tsv`, `abc-QF_IDL.tsv` — 200 rows each

The pinned competition lists (`../parity-lists/<div>.txt`, sha256 unchanged from
the recorded entries). **Three axeyum binaries and z3 run per file, adjacent in
time**, so machine contention is shared across the arms rather than assigned to
whichever arm happened to run during a busy window. 24 s wall budget each, 12 GiB
address-space cap, external kill at 32 s.

| column | meaning |
|---|---|
| `file` | benchmark path |
| `declared` | the benchmark's `:status` (`none` if absent) |
| `z3` / `z3_ms` | z3 4.13.3 at `-T:24` (`other` is its `timeout` line) |
| `base` / `base_ms` / `base_detail` | unmodified build at the snapshot commit |
| `ab` / `ab_ms` / `ab_detail` | the diagnosis's A/B: `MAX_MINIMIZED_THEORY_CORE_ATOMS` 128 → 4 096, nothing else |
| `budget` / `budget_ms` / `budget_detail` | the shipped change: minimisation rationed by an oracle-call work budget, retention charged by retained width |

Verdict values are `sat` / `unsat` / `unknown` / `parse_error` / `HARDKILL`
(still running at the external 32 s kill) / `ABORT(<status>)`. `HARDKILL` is this
probe's label, not the shipped solver's behaviour: the competition CLI's watchdog
prints `unknown` at ~25 s on the same files. Both count as unsolved.

`*_detail` is the `UnknownReason` kind and detail that the competition CLI is
required to suppress, truncated to 700 characters — which is *before* the
`min_oracle_calls=` counters on the QF_UFLIA rows, because those arrive nested
inside the CEGAR wrapper's own decline string. The spend figures in the note come
from `spend-probe.tsv`.

## `spend-probe.tsv`

Untruncated `UnknownReason` details from the shipped binary on the QF_UFLIA files
it still declines, which is where the `min_oracle_calls` / `min_oracle_budget_left`
/ `min_declined_cores` counters can be read.

## Reference frame

16-thread i5-12600K, sweep at `-P 5` pinned to `taskset -c 0-11`, load average
9–17 throughout with other lanes on the box. Decided counts are therefore a lower
bound. The `base` arm reproduced the diagnosis's recorded QF_UFLIA baseline of
92/200 exactly.
