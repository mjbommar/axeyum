(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(53,59) gives x*y=3127 with 2<=.<=59; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x y) 3127))
(assert (and (<= 2 x) (<= x 59)))
(assert (and (<= 2 y) (<= y 59)))
(check-sat)
