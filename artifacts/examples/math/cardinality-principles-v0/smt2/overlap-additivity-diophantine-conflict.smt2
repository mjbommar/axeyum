; QF_LIA count obstruction for cardinality-principles-v0.
;
; Exact finite replay computes |A union B| = 4 for the overlapping sets
; A = {a,b,c} and B = {b,c,d}. The malformed disjoint-additivity row claims
; the same union count equals |A| + |B| = 6.
(set-logic QF_LIA)
(declare-fun union_count () Int)
(declare-fun claimed_disjoint_sum () Int)
(assert (= union_count 4))
(assert (= claimed_disjoint_sum 6))
(assert (= union_count claimed_disjoint_sum))
(check-sat)
