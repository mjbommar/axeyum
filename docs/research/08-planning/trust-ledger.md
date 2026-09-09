# Reduction trust ledger

Generated from `axeyum_solver::trust::ALL_TRUST_IDS` — do not edit by hand.
Regenerate after changing the enum and commit the result; a golden test
(`tests/trust_ledger.rs`) fails if this file drifts from the source of truth.

Pedantic levels mirror cvc5's `TrustId` grading: 0 = hard fail … 10 = minor.
**certified** = every evidence route that records the step re-derives it (an independent per-query checker: the QF_BV Alethe `bitblast_*` steps / DRAT / Farkas / enumeration); **trust hole** = at least one route relies on the reduction with nothing to re-derive it (the base Track 3 P3.5 drives to zero). Both words are **folded from `trust::EVIDENCE_ROUTES`** by `TrustId::coverage`, not typed per id; the coverage table below splits the holes into *partially certified* and *no certified route at all*, which the single Status word cannot.

Trusted base: **10** reduction(s) remain trust holes.

| Reduction | Meaning | Pedantic | Status | Ref |
|---|---|---|---|---|
| bit-blast | term → AIG bit-blasting | 8 | trust hole | ADR-0006 |
| tseitin | AIG → CNF Tseitin encoding | 9 | trust hole | ADR-0006 |
| sat-refutation | CNF UNSAT from the CDCL core | 9 | trust hole | ADR-0012 |
| sat-refutation-modulo-theory | CNF UNSAT from the CDCL(T) core modulo N enumerated theory lemmas | 4 | trust hole | ADR-1704 |
| array-elim | arrays → BV (read-over-write + Ackermann) | 4 | trust hole | ADR-0010 |
| ackermann | uninterpreted functions → fresh vars + functional consistency | 4 | trust hole | ADR-0013 |
| int-blast | bounded integers → BV at a chosen width | 3 | trust hole | ADR-0014 |
| datatype-elim | datatypes folded over constructors → BV | 4 | trust hole | ADR-0022 |
| fpa2bv | floating-point operators → BV circuits | 5 | trust hole | ADR-0023 |
| term-level-enum | reduction-free exhaustive evaluation over the finite domain | 10 | certified | ADR-0005 |
| farkas | exact-rational Farkas refutation (QF_LRA) | 10 | certified | ADR-0015 |
| lra-dpll | lazy-SMT skeleton + Farkas-certified theory lemmas | 9 | certified | ADR-0021 |
| xor-gaussian | CDCL(XOR) search-only UNSAT (in-search Gaussian reasoning, no DRAT) | 3 | trust hole | ADR-0035 |
| sos | degree-2 sum-of-squares / PSD nonnegativity certificate (NRA) | 10 | certified | ADR-0039 |
| diophantine | integer-systems infeasibility (integer Farkas / Diophantine) | 10 | certified | ADR-0042 |

## Coverage, and the routes it is folded from

Of the 10 trust hole(s), **6** are *partially certified* — at least one evidence route re-derives the reduction and at least one does not — and **4** have no certified route at all. For a *given* `unsat`, read `TrustStep::certified` on the produced `EvidenceReport`, never this table.

| Reduction | Coverage | Producer | Artifact | Checker | Re-derives it |
|---|---|---|---|---|---|
| bit-blast | partially certified | `prove_qf_bv_unsat_alethe` | Evidence::UnsatAletheProof | `check_alethe` | yes |
| bit-blast | partially certified | `drat_qf_bv_evidence` | Evidence::Unsat(Some(UnsatProof)) | `UnsatProof` | no |
| tseitin | partially certified | `prove_qf_bv_unsat_alethe` | Evidence::UnsatAletheProof | `check_alethe` | yes |
| tseitin | partially certified | `pure_gauss_xor_unsat_certificate_for_query` | Evidence::Unsat(Some(UnsatProof)) | `check_drat` | no |
| sat-refutation | partially certified | `drat_qf_bv_evidence` | Evidence::Unsat(Some(UnsatProof)) | `UnsatProof` | yes |
| sat-refutation | partially certified | `drat_qf_bv_evidence` | Evidence::Unsat(None) | none | no |
| sat-refutation-modulo-theory | trust hole | `theory_refutation_trust_step` | TheoryRefutation with theory_lemma_count() > 0 | none | no |
| array-elim | trust hole | `reduction_unsat_certificate` | Evidence::Unsat(Some(UnsatProof)) | `export_qf_aufbv_unsat_proof_within` | no |
| ackermann | trust hole | `reduction_unsat_certificate` | Evidence::Unsat(Some(UnsatProof)) | `export_qf_aufbv_unsat_proof_within` | no |
| int-blast | partially certified | `certify_bounded_int_blast` | Evidence::UnsatBoundedIntBlast | `BoundedIntBlastCertificate` | yes |
| int-blast | partially certified | `prove_lia_unsat_alethe` | Evidence::UnsatArithAletheProof | `check_alethe_lra` | no |
| datatype-elim | trust hole | `reduction_unsat_certificate` | Evidence::Unsat(Some(UnsatProof)) | `export_datatype_unsat_proof` | no |
| fpa2bv | partially certified | `with_fpa2bv_step` | unsat evidence over an FP query whose operators are all faithful by construction | `fpa2bv_simple_op_certified` | yes |
| fpa2bv | partially certified | `with_fpa2bv_step` | unsat evidence over a rounding-bearing or large-format FP query | none | no |
| term-level-enum | certified | `certify_qf_bv_by_enumeration` | Evidence::UnsatTermLevel | `certify_qf_bv_by_enumeration` | yes |
| farkas | certified | `lra_farkas_certificate` | Evidence::UnsatFarkas | `FarkasCertificate` | yes |
| lra-dpll | certified | `certify_lra_dpll_unsat` | Evidence::UnsatLraDpll | `LraDpllRefutation` | yes |
| xor-gaussian | partially certified | `pure_gauss_xor_unsat_certificate_for_query` | Evidence::Unsat(Some(UnsatProof)) | `check_drat` | yes |
| xor-gaussian | partially certified | `produce_qf_bv_evidence` | Evidence::Unsat(None) | none | no |
| sos | certified | `reconstruct_sos_to_lean_module` | Evidence::UnsatSos | `SosCertificate` | yes |
| diophantine | certified | `reconstruct_diophantine_to_lean_module` | Evidence::UnsatDiophantine | `check_diophantine_certificate` | yes |
