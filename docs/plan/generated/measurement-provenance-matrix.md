# Measurement provenance and coverage matrix

> **Generated; do not edit by hand.** Source contract: [`docs/plan/measurement-provenance-v1.json`](../measurement-provenance-v1.json). Regenerate with `python3 scripts/gen-measurement-provenance.py`; use `--check` in validation.

This is one vocabulary over **two separate measurement regimes**, not one merged score. The official SMT-COMP selection and PAR-2 rules are reference policies; neither committed population is an official SMT-COMP selection.

## Denominator audit

| Regime | Rows | Raw cases | File-backed | Unique paths | Unique bytes | Aggregate-only | Exact alias groups | Decided | Neutral rows |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Curated/regression scoreboard | 35 | 992 | 927 | 837 | 778 | 65 | 58 | 753 | 0 |
| Partial public inventory | 18 | 228 | 228 | 228 | 228 | 0 | 0 | 82 | 0 |

The public inventory's legacy 82/228 scorer field contains **78 known-status agreements** and **4 unadjudicated decisions**. Its 83 benchmarks without known status do not inherit benchmark-status correctness credit.

The scoreboard's 927 file occurrences contract to 837 normalized paths and **778 unique byte contents**. Its 58 exact-alias groups remove 59 further path identities after path deduplication; 65 synthetic cases have no file identity and remain explicit.

The regimes overlap on **99 exact contents**: 43.4% of the 228-file inventory and 12.7% of the scoreboard's unique file-backed contents. The public inventory is therefore a harder differently weighted view, but not an independent sample. The two decide rates must not be averaged or treated as replication.

## Row matrix

`PAR-2` is a within-row mean in seconds. `Neutral = absent` means no non-Z3 solver ran the exact row population; a separately sourced 24-file QF_BV head-to-head does not grant neutral-oracle credit to the 228-file inventory.

| Regime | Logic / population | Class | Raw | IDs | SHA | Agg | Sat | Unsat | Miss | Fail | Limit | PAR-2 | Truth | Neutral |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| scoreboard | `BV` / `bv-bitwuzla-regress-clean-quantified` | `decide-strong` | 5 | 5 | 5 | 0 | 1 | 4 | 0 | 0 | 10 | 0.000 | `:status` | absent |
| scoreboard | `BV` / `bv-cvc5-regress-clean-quantified` | `decide-strong` | 54 | 54 | 54 | 0 | 36 | 18 | 0 | 0 | 10 | 0.033 | `z3-binary` | absent |
| scoreboard | `LIA` / `lia-cvc5-regress-clean-quantified` | `frontier` | 12 | 12 | 12 | 0 | 0 | 0 | 12 | 0 | 10 | 30.000 | `:status` | absent |
| scoreboard | `QF_ABV` / `qf-abv-cvc5-bitwuzla-regress-clean` | `decide-strong` | 193 | 193 | 184 | 0 | 84 | 85 | 24 | 0 | 10 | 1.666 | `z3-library+binary` | absent |
| scoreboard | `QF_ALIA` / `qf-alia-cvc5-regress-clean` | `decide-strong` | 6 | 6 | 6 | 0 | 1 | 5 | 0 | 0 | 10 | 0.000 | `z3-binary` | absent |
| scoreboard | `QF_AUFBV` / `qf-aufbv-bitwuzla-regress-clean` | `decide-strong` | 44 | 44 | 43 | 0 | 21 | 20 | 3 | 0 | 10 | 1.979 | `z3-library+binary` | absent |
| scoreboard | `QF_AUFBV` / `qf-aufbv-cvc5-regress-clean` | `partial` | 9 | 9 | 9 | 0 | 5 | 0 | 4 | 0 | 10 | 3.334 | `z3-binary` | absent |
| scoreboard | `QF_AUFLIA` / `qf-auflia-cvc5-regress-clean` | `partial` | 7 | 7 | 7 | 0 | 3 | 2 | 2 | 0 | 10 | 5.715 | `z3-binary` | absent |
| scoreboard | `QF_AX` / `qf-ax-cvc5-regress-clean` | `decide-strong` | 8 | 8 | 8 | 0 | 3 | 5 | 0 | 0 | 10 | 0.004 | `z3-binary` | absent |
| scoreboard | `QF_BV` / `qf-bv-curated-bvred` | `decide-strong` | 6 | 6 | 6 | 0 | 4 | 2 | 0 | 0 | 10 | 0.000 | `z3-library` | absent |
| scoreboard | `QF_BVFP` / `qf-bvfp-bitwuzla-regress-clean` | `decide-strong` | 8 | 8 | 8 | 0 | 4 | 3 | 1 | 0 | 10 | 0.005 | `z3-library+binary` | absent |
| scoreboard | `QF_DT` / `qf-dt-cvc5-regress-clean` | `decide-strong` | 3 | 3 | 3 | 0 | 0 | 3 | 0 | 0 | 10 | 0.003 | `z3-binary` | absent |
| scoreboard | `QF_FF` / `qf-ff-cvc5-regress-clean` | `decide-strong` | 30 | 30 | 30 | 0 | 14 | 10 | 6 | 0 | 10 | 0.010 | `z3-library` | absent |
| scoreboard | `QF_FP` / `qf-fp-bitwuzla-regress-clean` | `decide-strong` | 16 | 16 | 16 | 0 | 9 | 7 | 0 | 0 | 10 | 0.010 | `z3-library+binary` | absent |
| scoreboard | `QF_LIA` / `qf-lia-cvc5-regress-clean` | `decide-strong` | 11 | 11 | 11 | 0 | 6 | 4 | 1 | 0 | 10 | 1.819 | `z3-binary` | absent |
| scoreboard | `QF_LRA` / `qf-lra-cvc5-regress-clean` | `decide-strong` | 11 | 11 | 11 | 0 | 6 | 3 | 2 | 0 | 10 | 3.637 | `z3-binary` | absent |
| scoreboard | `QF_NIA` / `qf-nia-curated-iand` | `decide-strong` | 3 | 3 | 3 | 0 | 1 | 2 | 0 | 0 | 10 | 0.003 | `:status` | absent |
| scoreboard | `QF_NIA` / `qf-nia-cvc5-regress-clean` | `decide-strong` | 39 | 39 | 39 | 0 | 18 | 15 | 6 | 0 | 10 | 2.730 | `z3-binary` | absent |
| scoreboard | `QF_NRA` / `qf-nra-cvc5-regress-clean` | `decide-strong` | 38 | 38 | 38 | 0 | 18 | 14 | 6 | 0 | 10 | 3.169 | `z3-binary` | absent |
| scoreboard | `QF_S` / `qf-s-cvc5-regress-clean` | `partial` | 134 | 134 | 133 | 0 | 59 | 28 | 47 | 0 | 10 | 1.323 | `z3-library+binary` | absent |
| scoreboard | `QF_SEQ` / `qf-seq-cvc5-regress-clean` | `partial` | 33 | 33 | 33 | 0 | 21 | 5 | 7 | 0 | 10 | 3.752 | `z3-library+binary` | absent |
| scoreboard | `QF_SLIA` / `qf-slia-cvc5-regress-clean` | `partial` | 50 | 50 | 50 | 0 | 10 | 8 | 32 | 0 | 10 | 3.650 | `z3-library+binary` | absent |
| scoreboard | `QF_UF` / `qf-uf-cvc5-regress-clean-bounded` | `partial` | 82 | 82 | 82 | 0 | 29 | 15 | 37 | 0 | 10 | 4.845 | `z3-library+binary` | absent |
| scoreboard | `QF_UF` / `qf-uf-cvc5-regress-clean-bounded-uninterp-sorts` | `partial` | 82 | 82 | 82 | 0 | 29 | 15 | 37 | 0 | 10 | 4.845 | `z3-library+binary` | absent |
| scoreboard | `QF_UF` / `qf-uf-cvc5-regress-clean-overbound-uninterp-sorts` | `partial` | 6 | 6 | 6 | 0 | 1 | 3 | 2 | 0 | 10 | 7.489 | `z3-binary` | absent |
| scoreboard | `QF_UFBV` / `qf-ufbv-bitwuzla-regress-clean` | `decide-strong` | 2 | 2 | 2 | 0 | 1 | 1 | 0 | 0 | 10 | 0.000 | `z3-binary` | absent |
| scoreboard | `QF_UFBV` / `qf-ufbv-cvc5-regress-clean` | `decide-strong` | 4 | 4 | 4 | 0 | 2 | 2 | 0 | 0 | 10 | 0.001 | `z3-binary` | absent |
| scoreboard | `QF_UFFF` / `qf-ufff-cvc5-regress-clean` | `decide-strong` | 8 | 8 | 8 | 0 | 2 | 6 | 0 | 0 | 10 | 0.003 | `:status` | absent |
| scoreboard | `QF_UFLIA` / `qf-uflia-curated-named` | `decide-strong` | 2 | 2 | 2 | 0 | 0 | 2 | 0 | 0 | 10 | 0.001 | `z3-binary` | absent |
| scoreboard | `QF_UFLIA` / `qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts` | `decide-strong` | 6 | 6 | 6 | 0 | 4 | 2 | 0 | 0 | 10 | 0.002 | `z3-binary` | absent |
| scoreboard | `QF_UFLIA` / `qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts` | `decide-strong` | 2 | 2 | 2 | 0 | 0 | 2 | 0 | 0 | 10 | 2.294 | `z3-binary` | absent |
| scoreboard | `QF_UFLIA` / `qf-uflia-cvc5-regress-clean` | `decide-strong` | 8 | 8 | 8 | 0 | 4 | 4 | 0 | 0 | 10 | 0.572 | `z3-binary` | absent |
| scoreboard | `UF` / `uf-cvc5-regress-clean-quantified` | `frontier` | 5 | 5 | 5 | 0 | 0 | 0 | 5 | 0 | 10 | 0.000 | `:status` | absent |
| scoreboard | `QF_NRA` / `qf-nra-synthetic-graduated` | `decide-strong` | 33 | — | — | 33 | 14 | 16 | 3 | 0 | 30 | 5.455 | `z3-binary` | absent |
| scoreboard | `QF_NIA` / `qf-nia-synthetic-graduated` | `decide-strong` | 32 | — | — | 32 | 16 | 16 | 0 | 0 | 30 | 6.772 | `z3-binary` | absent |
| public | `QF_BV` / `QF_BV` | `frontier` | 113 | 113 | 113 | 0 | 6 | 0 | 107 | 0 | 120 | 229.523 | `benchmark-status-partial+unadjudicated` | absent |
| public | `QF_LRA` / `QF_LRA` | `decide-strong` | 12 | 12 | 12 | 0 | 7 | 3 | 2 | 0 | 120 | 40.007 | `benchmark-status-partial+unadjudicated` | absent |
| public | `QF_UF` / `QF_UF` | `decide-strong` | 23 | 23 | 23 | 0 | 8 | 14 | 1 | 0 | 120 | 10.518 | `benchmark-status` | absent |
| public | `QF_UFBV` / `QF_UFBV` | `decide-strong` | 4 | 4 | 4 | 0 | 2 | 2 | 0 | 0 | 120 | 0.008 | `benchmark-status` | absent |
| public | `QF_UFBVFS` / `QF_UFBVFS` | `decide-strong` | 1 | 1 | 1 | 0 | 1 | 0 | 0 | 0 | 120 | 0.005 | `benchmark-status` | absent |
| public | `QF_UFBVLIA` / `QF_UFBVLIA` | `partial` | 6 | 6 | 6 | 0 | 3 | 1 | 2 | 0 | 120 | 80.003 | `benchmark-status` | absent |
| public | `QF_UFC` / `QF_UFC` | `frontier` | 3 | 3 | 3 | 0 | 0 | 0 | 3 | 0 | 120 | 240.000 | `benchmark-status` | absent |
| public | `QF_UFDTLIA` / `QF_UFDTLIA` | `frontier` | 1 | 1 | 1 | 0 | 0 | 0 | 1 | 0 | 120 | 240.000 | `benchmark-status` | absent |
| public | `QF_UFIDL` / `QF_UFIDL` | `decide-strong` | 3 | 3 | 3 | 0 | 1 | 2 | 0 | 0 | 120 | 8.516 | `benchmark-status` | absent |
| public | `QF_UFLIA` / `QF_UFLIA` | `decide-strong` | 17 | 17 | 17 | 0 | 9 | 5 | 3 | 0 | 120 | 54.791 | `benchmark-status` | absent |
| public | `QF_UFLIAFS` / `QF_UFLIAFS` | `partial` | 13 | 13 | 13 | 0 | 4 | 3 | 6 | 0 | 120 | 119.277 | `benchmark-status` | absent |
| public | `QF_UFLIRAFS` / `QF_UFLIRAFS` | `decide-strong` | 2 | 2 | 2 | 0 | 2 | 0 | 0 | 0 | 120 | 0.008 | `benchmark-status` | absent |
| public | `QF_UFLRAFS` / `QF_UFLRAFS` | `decide-strong` | 1 | 1 | 1 | 0 | 1 | 0 | 0 | 0 | 120 | 0.004 | `benchmark-status` | absent |
| public | `QF_UFNIA` / `QF_UFNIA` | `partial` | 8 | 8 | 8 | 0 | 3 | 0 | 5 | 0 | 120 | 150.013 | `benchmark-status` | absent |
| public | `QF_UFNIRA` / `QF_UFNIRA` | `frontier` | 1 | 1 | 1 | 0 | 0 | 0 | 1 | 0 | 120 | 240.000 | `benchmark-status` | absent |
| public | `QF_UFNRA` / `QF_UFNRA` | `decide-strong` | 4 | 4 | 4 | 0 | 3 | 1 | 0 | 0 | 120 | 0.034 | `benchmark-status` | absent |
| public | `QF_UFNRAT` / `QF_UFNRAT` | `frontier` | 10 | 10 | 10 | 0 | 0 | 0 | 10 | 0 | 120 | 240.000 | `benchmark-status` | absent |
| public | `QF_UFSLIA` / `QF_UFSLIA` | `frontier` | 6 | 6 | 6 | 0 | 1 | 0 | 5 | 0 | 120 | 200.001 | `benchmark-status` | absent |

## Interpretation boundary

- `Raw` counts occurrences. `IDs` deduplicates normalized paths. `SHA` deduplicates exact bytes. None of these is semantic or near-duplicate clustering.
- The coverage class is Axeyum-relative observed decide rate, not an intrinsic benchmark-difficulty label.
- PAR-2 remains row-local because rows have different time limits, hosts, selection policies, configurations, and sometimes only aggregate data.
- Z3 oracle agreement, benchmark `:status`, and neutral multi-solver agreement are different evidence classes. V1 records zero neutral rows on these exact populations.
- Source families are strata, not weights. No global parity percentage is defined by this artifact.

## Remaining G1 work

1. Add syntax-normalized and then semantic near-duplicate experiments without replacing exact-byte identity.
2. Freeze an official-selection manifest from a complete SMT-LIB release before calling any score SMT-COMP representative.
3. Run non-Z3 external solvers over each exact claimed population and record SAT/UNSAT decision-set overlap, not only totals.
4. Define a representative-selection rule before computing any deduplicated PAR-2; v1 intentionally reports deduplicated denominators only.
5. Add operator profiles and a neutral reference difficulty measure before using the word `difficulty` as anything stronger than observed coverage.

The complete machine-readable rows and all 99 exact cross-regime overlap records are in [`measurement-provenance-matrix.json`](measurement-provenance-matrix.json).
