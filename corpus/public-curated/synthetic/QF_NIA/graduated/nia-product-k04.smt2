(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(19,23) gives x*y=437 with 2<=.<=23; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x y) 437))
(assert (and (<= 2 x) (<= x 23)))
(assert (and (<= 2 y) (<= y 23)))
(check-sat)
