; Product: fact(0)=1 and fact(k+1)=fact(k)*(k+1), so fact(n) >= 1 on N.
; Nonlinear step obligation.
(set-logic UFNIA)
(set-info :status unsat)
(declare-fun fact (Int) Int)
(assert (= (fact 0) 1))
(assert (forall ((k Int)) (=> (>= k 0) (= (fact (+ k 1)) (* (fact k) (+ k 1))))))
(assert (not (forall ((n Int)) (=> (>= n 0) (>= (fact n) 1)))))
(check-sat)
