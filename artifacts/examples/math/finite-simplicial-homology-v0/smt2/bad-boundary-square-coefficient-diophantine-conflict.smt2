; QF_LIA Diophantine obstruction for finite-simplicial-homology-v0.
;
; In the filled triangle, the coefficient of vertex [b] in
; boundary(boundary([a,b,c])) cancels to 0: [b] appears with coefficient -1
; from boundary([b,c]) and +1 from boundary([a,b]). A bad chain-complex row
; that claims coefficient +1 forces the same integer coefficient to be both
; 0 and 1.
(set-logic QF_LIA)
(declare-fun coeff_b () Int)
(assert (= coeff_b 0))
(assert (= coeff_b 1))
(check-sat)
