; QF_LRA/Farkas obstruction for finite-product-measure-v0.
; Exact replay computes the left marginal of heads as 1/2.
(set-logic QF_LRA)
(declare-const left_marginal_heads Real)
(assert (= left_marginal_heads (/ 1 2)))
(assert (= left_marginal_heads (/ 2 3)))
(check-sat)
