; QF_LIA Diophantine obstruction for modular-arithmetic-v0.
;
; The malformed CRT row asks for an integer x satisfying:
;
;   x == 1 mod 4
;   x == 2 mod 6
;
; This is equivalent to asking for integers a,b with 1 + 4*a = 2 + 6*b, or
; 4*a - 6*b = 1. Since gcd(4,6)=2 does not divide 1, the two congruences are
; incompatible. Axeyum's Diophantine certificate records this gcd obstruction
; and checks it independently.
(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (- (* 4 a) (* 6 b)) 1))
(check-sat)
