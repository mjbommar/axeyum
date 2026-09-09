# Reduction trust ledger

Generated from `axeyum_solver::trust::ALL_TRUST_IDS` — do not edit by hand.
Regenerate after changing the enum and commit the result; a golden test
(`tests/trust_ledger.rs`) fails if this file drifts from the source of truth.

Pedantic levels mirror cvc5's `TrustId` grading: 0 = hard fail … 10 = minor.
The status is **folded from `trust::EVIDENCE_ROUTES`**, one row per (reduction, does-the-checker-re-derive-it) route: **certified** = every route that records the step re-derives it; **partially certified** = some routes do and some do not (read the per-result `TrustStep::certified`, not this column, for a given `unsat`); **trust hole** = no route re-derives it (the base Track 3 P3.5 drives to zero).

Trusted base: **4** reduction(s) are trust holes and **6** are only partially certified; **5** are fully certified.

| Reduction | Meaning | Pedantic | Status | Ref |
|---|---|---|---|---|
| bit-blast | term → AIG bit-blasting | 8 | partially certified | ADR-0006 |
| tseitin | AIG → CNF Tseitin encoding | 9 | partially certified | ADR-0006 |
| sat-refutation | CNF UNSAT from the CDCL core | 9 | partially certified | ADR-0012 |
| sat-refutation-modulo-theory | CNF UNSAT from the CDCL(T) core modulo N enumerated theory lemmas | 4 | trust hole | ADR-1704 |
| array-elim | arrays → BV (read-over-write + Ackermann) | 4 | trust hole | ADR-0010 |
| ackermann | uninterpreted functions → fresh vars + functional consistency | 4 | trust hole | ADR-0013 |
| int-blast | bounded integers → BV at a chosen width | 3 | partially certified | ADR-0014 |
| datatype-elim | datatypes folded over constructors → BV | 4 | trust hole | ADR-0022 |
| fpa2bv | floating-point operators → BV circuits | 5 | partially certified | ADR-0023 |
| term-level-enum | reduction-free exhaustive evaluation over the finite domain | 10 | certified | ADR-0005 |
| farkas | exact-rational Farkas refutation (QF_LRA) | 10 | certified | ADR-0015 |
| lra-dpll | lazy-SMT skeleton + Farkas-certified theory lemmas | 9 | certified | ADR-0021 |
| xor-gaussian | CDCL(XOR) search-only UNSAT (in-search Gaussian reasoning, no DRAT) | 3 | partially certified | ADR-0035 |
| sos | degree-2 sum-of-squares / PSD nonnegativity certificate (NRA) | 10 | certified | ADR-0039 |
| diophantine | integer-systems infeasibility (integer Farkas / Diophantine) | 10 | certified | ADR-0042 |
