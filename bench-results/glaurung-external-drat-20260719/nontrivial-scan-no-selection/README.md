# Nontrivial external DRAT scan: no selection

ADR-0257's preregistered scan ran from clean detached Axeyum `10ee9795` over
the first 32 remaining expected-UNSAT holdout rows in ascending content-hash
order. All 32 exports succeeded and self-rechecked, but every DRAT was the same
two-byte, one-line empty-clause proof. No row met the required proof-size gate,
so the result is `no-selection` and the fixed cap is not widened.

The pinned checker printed an exact `s VERIFIED` line for both the real and
empty proof on every row. Sixteen input-unit/complementary-unit paths exited 0;
the other sixteen checker-detected trivial-UNSAT paths exited 1 despite the
marker. This checker behavior does not affect the selection: every proof failed
the independent `>2 bytes` and `>1 line` gates.

`result.json` retains all 32 ordered attempts with source/DIMACS/proof identities,
stream hashes, exit codes, checker classifications, and the clean exporter and
pinned checker hashes. Source queries and derived CNF/proof bytes remain outside
Git. This is a bounded negative proof-shape result, not prevalence, lowering, or
performance evidence.
