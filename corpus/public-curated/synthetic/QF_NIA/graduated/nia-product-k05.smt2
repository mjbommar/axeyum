(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(29,31) gives x*y=899 with 2<=.<=31; checked by generator.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x y) 899))
(assert (and (<= 2 x) (<= x 31)))
(assert (and (<= 2 y) (<= y 31)))
(check-sat)
