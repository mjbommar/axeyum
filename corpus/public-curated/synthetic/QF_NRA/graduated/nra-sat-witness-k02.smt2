(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: explicit rational witness ['1/2', '2/3'] substituted; sum(xi^2)=25/36 holds exactly (checked by generator).
(declare-fun x1 () Real)
(declare-fun x2 () Real)

(assert (= x1 (/ 1.0 2.0)))
(assert (= x2 (/ 2.0 3.0)))
(assert (= (+ (* x1 x1) (* x2 x2)) (/ 25.0 36.0)))
(check-sat)
