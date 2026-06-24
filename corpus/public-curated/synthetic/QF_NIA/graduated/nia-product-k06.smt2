(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(37,41) gives x*y=1517 with 2<=.<=41; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x y) 1517))
(assert (and (<= 2 x) (<= x 41)))
(assert (and (<= 2 y) (<= y 41)))
(check-sat)
