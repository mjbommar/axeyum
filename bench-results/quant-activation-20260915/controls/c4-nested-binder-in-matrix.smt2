; CONTROL 4 -- the SPARK shape: a top-level universal whose MATRIX holds
; another binder.  The first shape guard that fires is `nested-binder-in-matrix`
; (127 of 134 AUFDTLIRA files, ADR-2114 §1a).  The inner universal is positive
; and sits under a binder, so it is an activation target.
; qshape expects: pos_forall_unit=1 forall_under_binder=1
;                 mbqi_exit_pred=nested-binder-in-matrix activation_target=1
(set-logic AUFLIA)
(declare-fun g (Int Int) Int)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (=> (q x) (forall ((y Int)) (> (g x y) 0)))))
(check-sat)
