; QF_LIA Diophantine obstruction for polynomial-identities-v0.
;
; For p(x)=x^2+1 at the fixed rational/integer candidate x=1, exact
; evaluation gives p(1)=2. A claimed root asks for p(1)=0, contradicting
; the same fixed coefficient computation.
(set-logic QF_LIA)
(declare-fun x_squared () Int)
(declare-fun value () Int)
(assert (= x_squared 1))
(assert (= value (+ x_squared 1)))
(assert (= value 0))
(check-sat)
