; Source artifact for finite-entropy-information-gain-v0.
; Exact dyadic replay gives color weighted entropy = 1/2, represented without
; division as 2*entropy_color = 1. The malformed row claims weighted entropy =
; 3/4, represented as 4*entropy_color = 3.

(set-logic QF_LRA)

(declare-const entropy_color Real)

(assert (= (* 2 entropy_color) 1))
(assert (= (* 4 entropy_color) 3))

(check-sat)
