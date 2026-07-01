; QF_LIA Diophantine obstruction for number-theory-v0.
;
; The row asks for integers x,y with 14*x + 21*y = 5. Since gcd(14,21)=7
; does not divide 5, the equation has no integer solution. Axeyum's
; Diophantine certificate records this gcd obstruction and checks it
; independently.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ (* 14 x) (* 21 y)) 5))
(check-sat)
