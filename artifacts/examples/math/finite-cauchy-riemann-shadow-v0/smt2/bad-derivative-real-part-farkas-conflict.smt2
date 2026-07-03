(set-logic QF_LRA)
(declare-const derivative_real Real)

; Exact replay of f'(1+2i) for f(z)=z^2 computes real part 2.
(assert (= derivative_real 2))

; Malformed resource row claims real part 3.
(assert (= derivative_real 3))

(check-sat)
