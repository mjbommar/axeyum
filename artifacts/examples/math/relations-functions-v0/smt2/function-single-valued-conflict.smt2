; QF_UF function-consistency conflict for relations-functions-v0.
;
; A function cannot map the same input to two distinct outputs. The first two
; assertions force f(x0) to equal both y0 and y1; the final assertion says the
; outputs are distinct, so the query is unsatisfiable by EUF equality reasoning.
(set-logic QF_UF)
(declare-sort Input 0)
(declare-sort Output 0)
(declare-fun x0 () Input)
(declare-fun y0 () Output)
(declare-fun y1 () Output)
(declare-fun f (Input) Output)
(assert (= (f x0) y0))
(assert (= (f x0) y1))
(assert (not (= y0 y1)))
(check-sat)
