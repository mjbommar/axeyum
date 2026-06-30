; QF_UF identity-action conflict for finite-group-actions-v0.
;
; A group action must satisfy e.x = x for the identity element e. The
; malformed table sends point p to bad instead, while p and bad are distinct.
; Pure EUF congruence/transitivity is enough to refute the row.
(set-logic QF_UF)
(declare-sort G 0)
(declare-sort X 0)
(declare-fun e () G)
(declare-fun p () X)
(declare-fun bad () X)
(declare-fun act (G X) X)
(assert (= (act e p) p))
(assert (= (act e p) bad))
(assert (not (= p bad)))
(check-sat)
