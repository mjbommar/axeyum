(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(7,11) gives x*y=77 with 2<=.<=11; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x y) 77))
(assert (and (<= 2 x) (<= x 11)))
(assert (and (<= 2 y) (<= y 11)))
(check-sat)
