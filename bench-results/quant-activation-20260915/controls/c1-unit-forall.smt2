; CONTROL 1 -- a UNIT top-level universal.  Nothing nested, nothing split.
; qshape expects: pos_forall_unit=1 pos_forall_split=0 forall_under_binder=0
;                 multi_binder_unit=0 mbqi_exit_pred=refutation-loop
;                 activation_target=0
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (forall ((x Int)) (> (f x) x)))
(assert (< (f a) a))
(check-sat)
