; QF_LRA/Farkas obstruction for finite-flow-cut-v0.
; Exact cut replay computes cut_capacity = 3, but the malformed row claims
; a feasible flow value 4 while also requiring value <= cut_capacity.
(set-logic QF_LRA)
(declare-const cut_capacity Real)
(declare-const claimed_flow_value Real)
(assert (= cut_capacity 3))
(assert (= claimed_flow_value 4))
(assert (<= claimed_flow_value cut_capacity))
(check-sat)
