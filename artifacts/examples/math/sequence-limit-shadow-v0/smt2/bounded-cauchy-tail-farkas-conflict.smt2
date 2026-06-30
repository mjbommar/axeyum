; QF_LRA/Farkas obstruction for sequence-limit-shadow-v0.
;
; Exact finite replay computes the largest pairwise distance in the listed tail
; [1/3, 1/4, 1/5, 1/6, 1/7] as 1/3 - 1/7 = 4/21. The rejected counterexample
; claim asks for a pairwise distance at least 1/2.
(set-logic QF_LRA)
(declare-const max_pair_distance Real)
(assert (= max_pair_distance (/ 4 21)))
(assert (>= max_pair_distance (/ 1 2)))
(check-sat)
