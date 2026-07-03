; Source artifact for finite-perceptron-v0.
; Exact replay of the second perceptron mistake update gives the first
; weight coordinate 1 + (-1)*2 = -1. The malformed row claims the first
; coordinate is 1.

(set-logic QF_LRA)

(declare-const perceptron_w1 Real)

(assert (= perceptron_w1 (- 1.0)))
(assert (= perceptron_w1 1.0))

(check-sat)
