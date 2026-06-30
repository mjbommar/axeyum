; QF_UF preimage-membership conflict for finite-continuous-maps-v0.
;
; For a fixed function f and codomain open set U, membership in the preimage
; must agree with membership of f(x) in U. The bad row claims f(x)=u and
; u in U, but also claims x is absent from the preimage. Pure EUF congruence
; and transitivity refute the inconsistent preimage table.
(set-logic QF_UF)
(declare-sort X 0)
(declare-sort Y 0)
(declare-sort Membership 0)
(declare-fun x0 () X)
(declare-fun u () Y)
(declare-fun present () Membership)
(declare-fun absent () Membership)
(declare-fun f (X) Y)
(declare-fun in_u (Y) Membership)
(declare-fun in_preimage_u (X) Membership)
(assert (= (f x0) u))
(assert (= (in_u u) present))
(assert (= (in_preimage_u x0) (in_u (f x0))))
(assert (= (in_preimage_u x0) absent))
(assert (not (= present absent)))
(check-sat)
