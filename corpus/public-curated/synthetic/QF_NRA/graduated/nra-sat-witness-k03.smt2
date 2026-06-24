(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status sat)
; STATUS-PROOF: explicit rational witness ['1/2', '2/3', '3/4'] substituted; sum(xi^2)=181/144 holds exactly (checked by generator).
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)

(assert (= x1 (/ 1.0 2.0)))
(assert (= x2 (/ 2.0 3.0)))
(assert (= x3 (/ 3.0 4.0)))
(assert (= (+ (* x1 x1) (* x2 x2) (* x3 x3)) (/ 181.0 144.0)))
(check-sat)
