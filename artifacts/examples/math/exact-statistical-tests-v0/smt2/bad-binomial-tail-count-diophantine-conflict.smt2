; QF_LIA Diophantine obstruction for exact-statistical-tests-v0.
;
; For Binomial(4, 1/2), the right-tail count for X >= 3 is
; C(4,3) + C(4,4) = 4 + 1 = 5 over denominator 16. A claimed p-value of 1/4
; would require numerator 4 over the same denominator. These equalities force
; the tail count to be both 5 and 4.
(set-logic QF_LIA)
(declare-fun c3 () Int)
(declare-fun c4 () Int)
(declare-fun tail_count () Int)
(assert (= c3 4))
(assert (= c4 1))
(assert (= tail_count (+ c3 c4)))
(assert (= tail_count 4))
(check-sat)
