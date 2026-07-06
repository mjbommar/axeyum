; Source artifact for finite-value-iteration-v0.
; Exact replay of the second-iteration Bellman backup gives
; Q2(s1, a) = 1 + (1/2)*3 = 5/2. The malformed row claims the backup
; value is 2.

(set-logic QF_LRA)

(declare-const mdp_q2_s1_a Real)

(assert (= mdp_q2_s1_a 2.5))
(assert (= mdp_q2_s1_a 2.0))

(check-sat)
