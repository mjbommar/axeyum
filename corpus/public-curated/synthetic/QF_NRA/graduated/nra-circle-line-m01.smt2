(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(3,4) lies on x^2+y^2=25 (since 3^2+4^2=25) and on the line y - x = 1; both checked exactly by the generator.
(declare-fun x () Real)
(declare-fun y () Real)

(assert (= (+ (* x x) (* y y)) 25.0))
(assert (= (- y x) 1.0))
(check-sat)
