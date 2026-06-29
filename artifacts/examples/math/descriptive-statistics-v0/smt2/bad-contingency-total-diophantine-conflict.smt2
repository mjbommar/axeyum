; QF_LIA Diophantine obstruction for descriptive-statistics-v0.
;
; The fixed 2x2 contingency table has row sums 10 and 10, so the total count
; is 20. A claimed total count of 19 contradicts those integer margins.
(set-logic QF_LIA)
(declare-fun row0 () Int)
(declare-fun row1 () Int)
(declare-fun total () Int)
(assert (= row0 10))
(assert (= row1 10))
(assert (= total (+ row0 row1)))
(assert (= total 19))
(check-sat)
