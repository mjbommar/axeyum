(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: witness (x,y)=(7,24) lies on x^2+y^2=625 (since 7^2+24^2=625) and on the line y - x = 17; both checked exactly by the generator.
(declare-fun x () Real)
(declare-fun y () Real)

(assert (= (+ (* x x) (* y y)) 625.0))
(assert (= (- y x) 17.0))
(check-sat)
