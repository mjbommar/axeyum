; QF_UF subspace-closure conflict for finite-vector-spaces-v0.
;
; The claimed subset contains 10 and 01, but the finite vector-addition table
; gives 10 + 01 = 11 and the subset table marks 11 absent. Additive closure
; would require the sum to be present, so the row is refuted by EUF.
(set-logic QF_UF)
(declare-sort V 0)
(declare-sort Membership 0)
(declare-fun present () Membership)
(declare-fun absent () Membership)
(declare-fun v10 () V)
(declare-fun v01 () V)
(declare-fun v11 () V)
(declare-fun add (V V) V)
(declare-fun in_subset (V) Membership)
(assert (not (= present absent)))
(assert (= (in_subset v10) present))
(assert (= (in_subset v01) present))
(assert (= (add v10 v01) v11))
(assert (= (in_subset v11) absent))
(assert (= (in_subset (add v10 v01)) present))
(check-sat)
