(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y,z)=(21,28,35) satisfies x^2+y^2=z^2 (21^2+28^2=35^2) and 1<=.<=35; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= (+ (* x x) (* y y)) (* z z)))
(assert (and (<= 1 x) (<= x 35)))
(assert (and (<= 1 y) (<= y 35)))
(assert (and (<= 1 z) (<= z 35)))
(check-sat)
