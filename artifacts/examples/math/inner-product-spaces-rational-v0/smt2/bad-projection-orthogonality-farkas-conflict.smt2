; QF_LRA/Farkas obstruction for inner-product-spaces-rational-v0.
;
; Finite replay computes <residual,basis> = 0 for the projection of [2,3]
; onto span([1,1]). This artifact checks the malformed claim that the same
; replayed residual inner product is 1.
(set-logic QF_LRA)
(declare-const residual_inner_basis Real)
(assert (= residual_inner_basis 0))
(assert (= residual_inner_basis 1))
(check-sat)
