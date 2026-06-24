(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(9,40) lies on x^2+y^2=1681 (since 9^2+40^2=1681) and on the line y - x = 31; both checked exactly by the generator.
(declare-fun x () Real)
(declare-fun y () Real)

(assert (= (+ (* x x) (* y y)) 1681.0))
(assert (= (- y x) 31.0))
(check-sat)
