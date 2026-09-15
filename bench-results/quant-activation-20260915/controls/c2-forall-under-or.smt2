; CONTROL 2 -- THE `rej_nocontext` SHAPE: a POSITIVE universal under a
; disjunction.  `A or (forall y. B(y))` does not entail `B(t)`, so the matched
; tuple is dropped today; activation by assignment is what makes it usable.
; qshape expects: pos_forall_unit=0 pos_forall_split=1 forall_under_binder=0
;                 mbqi_exit_pred=quantifier-below-top-level
;                 activation_target=1
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const p Bool)
(assert (or p (forall ((y Int)) (> (f y) y))))
(assert (not p))
(assert (< (f a) a))
(check-sat)
