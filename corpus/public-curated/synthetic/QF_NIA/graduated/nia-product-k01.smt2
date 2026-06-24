(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(3,5) gives x*y=15 with 2<=.<=5; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x y) 15))
(assert (and (<= 2 x) (<= x 5)))
(assert (and (<= 2 y) (<= y 5)))
(check-sat)
