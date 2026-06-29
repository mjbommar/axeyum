; QF_LIA Diophantine obstruction for modular-arithmetic-v0.
;
; Asking for an inverse of 2 modulo 6 is asking for integers b,k with
; 2*b - 6*k = 1. Since gcd(2,6)=2 does not divide 1, the equation has no
; integer solution. Axeyum's Diophantine certificate records this gcd
; obstruction and checks it independently.
(set-logic QF_LIA)
(declare-fun b () Int)
(declare-fun k () Int)
(assert (= (- (* 2 b) (* 6 k)) 1))
(check-sat)
