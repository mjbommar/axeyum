; f(0)=0, f(k+1)=f(k)+2  =>  f(n)=2n for all n>=0.
; Valid: SMT-LIB Int is the standard integers, so the recurrence pins f on all
; of N. Not entailed by any finite instantiation, which is the point.
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))
(assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (* 2 n))))))
(check-sat)
