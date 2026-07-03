; Source artifact for finite-precision-recall-v0.
; Exact replay gives average precision = 34/45, represented without division as
; 45*ap = 34. The malformed row claims average precision = 3/4, represented as
; 4*ap = 3.

(set-logic QF_LRA)

(declare-const ap Real)

(assert (= (* 45 ap) 34))
(assert (= (* 4 ap) 3))

(check-sat)
