(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y,z)=(6,8,10) satisfies x^2+y^2=z^2 (6^2+8^2=10^2) and 1<=.<=10; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= (+ (* x x) (* y y)) (* z z)))
(assert (and (<= 1 x) (<= x 10)))
(assert (and (<= 1 y) (<= y 10)))
(assert (and (<= 1 z) (<= z 10)))
(check-sat)
