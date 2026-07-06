; Source artifact for finite-hard-margin-svm-v0.
; Exact replay of the support-vector margin equalities at w = (1/2, 1/2)
; gives the maximum-margin bias svm_b = -1. The malformed row claims the
; bias is -1/2.

(set-logic QF_LRA)

(declare-const svm_b Real)

(assert (= svm_b (- 1.0)))
(assert (= svm_b (- 0.5)))

(check-sat)
