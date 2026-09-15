; CONTROL 5 -- a MULTI-BINDER prefix with a quantifier-free matrix.  MBQI's
; refutation loop is single-binder, so this exits at `multi-binder-prefix`.
; It is NOT an activation target on its own: the universal is a unit assertion
; and its instances are already admissible.  Currying is the separate half.
; qshape expects: pos_forall_unit=1 multi_binder_unit=1 pos_forall_split=0
;                 forall_under_binder=0 mbqi_exit_pred=multi-binder-prefix
;                 activation_target=0
(set-logic UFLIA)
(declare-fun h (Int Int) Int)
(assert (forall ((x Int) (y Int)) (>= (h x y) 0)))
(check-sat)
