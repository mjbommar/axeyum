# QF_NIA A3 large-core group-deletion v2 result — 2026-08-07

## Verdict

The preregistered four-group deletion experiment is **rejected**. It produced
smaller sound conflict cores, but its extra theory-oracle work consumed the
shared query budget and neither target became SAT. All temporary solver code
and counters were removed; only the preregistration and result evidence remain.

No confirming target run, routing-control run, 34-decision retained-control
run, 200-row measurement, or full `just check` was authorized after the
two-target acceptance gate failed.

## Implementation and focused gate

The temporary implementation used exactly four stable contiguous groups and
at most four deadline-bounded oracle calls per otherwise-large core. It removed
a group only after an independent `Unsat` result and never invoked atom-by-atom
minimization afterward. Diagnostic counters were environment-gated.

Before measurement it passed:

- all 27 `dpll_lia::tests`, including the bounded group-deletion and aggregate-
  counter tests; 1,052 library tests were filtered by the focused command;
- `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --all-features`;
- `cargo fmt --all --check` and `git diff --check`.

The temporary release `explain_corpus` binary had SHA-256
`dbf7777aca9f2990f3a21330c7bbcc374fed46d2b38274c23149c98e24f5b83b`.
The A/B retained the v1 8 GiB and 24,000 ms per-query protocol and serialized
each direct observation on CPU 4.

## Target A/B

| Target | v1 representative | v2 result | Group work | Verdict |
|---|---|---|---|---|
| `SAT14/1051.smt2` | 192–202 lazy rounds; 170–179 large cores, principally length 513–653 | timeout after 35 rounds; 16 large cores, principally length 257–512 | 61 oracle calls; 15 groups / 2,438 atoms removed | `unknown`; reject |
| `SAT14/1280.smt2` | 391–397 lazy rounds; 363–369 large cores, principally length 257–490 | timeout after 338 rounds; 307 large cores, all length 129–256 | 1,227 oracle calls; 614 groups / 64,253 atoms removed | `unknown`; reject |

The pass never reduced a target core to 128 atoms or fewer. `1051` paid a
severe round-count penalty, while `1280` retained most of its rounds but still
exhausted the deadline. Clause width was therefore not the only limiting
factor, and four additional exact-theory probes per broad conflict are too
expensive for this architecture under the registered budget.

## Disposition and next boundary

The v2 stop condition says to reject when neither target gains or extra theory
work merely moves the stop earlier. Both conditions hold. The implementation
was reverted to the exact committed solver file, so there is no retained solver
change and no focused green claim for production code beyond the pre-
measurement experiment gate.

The stable conclusion is narrower than “core quality does not matter”:

- repeated broad cores are real and size-admitted;
- sound exact-theory group deletion can shrink them;
- paying up to four extra full oracle calls per conflict is not viable;
- neither a cap increase nor an unsound literal-sampling shortcut is justified.

A future A3 increment must repartition the remaining five DPLL/search rows or
identify a cheaper already-checked explanation mechanism. It must not revive
this group-deletion policy without new causal evidence and a new
preregistration.
