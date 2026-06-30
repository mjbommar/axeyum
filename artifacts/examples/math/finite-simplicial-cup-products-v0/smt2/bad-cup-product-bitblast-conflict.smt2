; QF_BV bit-blast conflict for finite-simplicial-cup-products-v0.
;
; On the filled triangle [a,b,c], the Alexander-Whitney F2 cup product gives:
;
;   (alpha cup beta)([a,b,c]) = alpha([a,b]) AND beta([b,c]) = 1
;
; The malformed row claims the same cup-product cell is 0. This artifact keeps
; the final finite replay mismatch as a one-bit bit-vector contradiction so the
; generated CNF can carry checked DRAT evidence.
(set-logic QF_BV)
(declare-fun alpha_ab () (_ BitVec 1))
(declare-fun beta_bc () (_ BitVec 1))
(declare-fun cup_abc () (_ BitVec 1))
(assert (= alpha_ab #b1))
(assert (= beta_bc #b1))
(assert (= cup_abc (bvand alpha_ab beta_bc)))
(assert (= cup_abc #b0))
(check-sat)
