# Reduction trust ledger

Generated from `axeyum_solver::trust::ALL_TRUST_IDS` — do not edit by hand.
Regenerate after changing the enum and commit the result; a golden test
(`tests/trust_ledger.rs`) fails if this file drifts from the source of truth.

Pedantic levels mirror cvc5's `TrustId` grading: 0 = hard fail … 10 = minor.
**certified** = an independent per-query checker re-derives the step (bit-blast miter / DRAT / Farkas / enumeration); **trust hole** = a sound reduction with no per-query certificate yet (the base Track 3 P3.5 drives to zero).

Trusted base: **6** reduction(s) remain trust holes.

| Reduction | Meaning | Pedantic | Status | Ref |
|---|---|---|---|---|
| bit-blast | term → AIG bit-blasting | 8 | certified | ADR-0006 |
| tseitin | AIG → CNF Tseitin encoding | 9 | certified | ADR-0006 |
| sat-refutation | CNF UNSAT from the CDCL core | 9 | certified | ADR-0012 |
| array-elim | arrays → BV (read-over-write + Ackermann) | 4 | trust hole | ADR-0010 |
| ackermann | uninterpreted functions → fresh vars + functional consistency | 4 | trust hole | ADR-0013 |
| int-blast | bounded integers → BV at a chosen width | 3 | trust hole | ADR-0014 |
| datatype-elim | datatypes folded over constructors → BV | 4 | trust hole | ADR-0022 |
| fpa2bv | floating-point operators → BV circuits | 5 | trust hole | ADR-0023 |
| term-level-enum | reduction-free exhaustive evaluation over the finite domain | 10 | certified | ADR-0005 |
| farkas | exact-rational Farkas refutation (QF_LRA) | 10 | certified | ADR-0015 |
| lra-dpll | lazy-SMT skeleton + Farkas-certified theory lemmas | 9 | certified | ADR-0021 |
| xor-gaussian | CDCL(XOR) search-only UNSAT (in-search Gaussian reasoning, no DRAT) | 3 | trust hole | ADR-0035 |
