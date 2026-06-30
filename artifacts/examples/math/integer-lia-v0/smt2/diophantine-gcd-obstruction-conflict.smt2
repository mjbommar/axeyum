; QF_LIA Diophantine obstruction for integer-lia-v0.
;
; The row asks for integers x,y with 2*x + 4*y = 3. Since gcd(2,4)=2
; does not divide 3, the equation has no integer solution. Axeyum's
; Diophantine certificate records this gcd obstruction and checks it
; independently.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ (* 2 x) (* 4 y)) 3))
(check-sat)
