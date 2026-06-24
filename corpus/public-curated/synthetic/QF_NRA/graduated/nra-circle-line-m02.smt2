(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(5,12) lies on x^2+y^2=169 (since 5^2+12^2=169) and on the line y - x = 7; both checked exactly by the generator.
(declare-fun x () Real)
(declare-fun y () Real)

(assert (= (+ (* x x) (* y y)) 169.0))
(assert (= (- y x) 7.0))
(check-sat)
