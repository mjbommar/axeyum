; Source artifact for finite-policy-iteration-v0.
; Exact replay of the first policy-evaluation linear system solves
; V(s2) = 0 + (1/2)*((1/2)*2 + (1/2)*V(s2)) to mdp_v_pi0_s2 = 2/3.
; The malformed row claims the value is 1/2.

(set-logic QF_LRA)

(declare-const mdp_v_pi0_s2 Real)

(assert (= mdp_v_pi0_s2 (/ 2 3)))
(assert (= mdp_v_pi0_s2 (/ 1 2)))

(check-sat)
