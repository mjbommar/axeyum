; QF_LIA Diophantine obstruction for induction-patterns-v0.
;
; The finite weak-induction prefix includes 6 * (6 + 1) = 42. A bad oddness
; witness claiming 42 = 2*20 + 1 reduces to the same integer product being
; both 42 and 41.
(set-logic QF_LIA)
(declare-fun product () Int)
(assert (= product 42))
(assert (= product 41))
(check-sat)
