(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: x^2 = 2 y^2 has no positive-integer solution (sqrt(2) irrational / infinite descent); bounded 1<=x,y<=20 -> still infeasible.
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (* x x) (* 2 (* y y))))
(assert (and (<= 1 x) (<= x 20)))
(assert (and (<= 1 y) (<= y 20)))
(check-sat)
