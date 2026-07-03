; Source artifact for finite-roc-auc-v0.
; Exact replay gives AUC = 2/3, represented without division as 3*auc = 2.
; The malformed row claims AUC = 3/4, represented as 4*auc = 3.

(set-logic QF_LRA)

(declare-const auc Real)

(assert (= (* 3 auc) 2))
(assert (= (* 4 auc) 3))

(check-sat)
