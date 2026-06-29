; QF_LIA Diophantine obstruction for finite-simplicial-homology-v0.
;
; The oriented boundary of [a,b,c] contains -[a,c]. A bad boundary claim that
; gives [a,c] coefficient +1 forces the same integer coefficient to be both
; -1 and +1.
(set-logic QF_LIA)
(declare-fun coeff_ac () Int)
(assert (= coeff_ac (- 1)))
(assert (= coeff_ac 1))
(check-sat)
