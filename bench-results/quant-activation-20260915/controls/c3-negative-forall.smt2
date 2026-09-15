; CONTROL 3 -- the NEGATIVE control for polarity.  A universal under a `not` is
; an EXISTENTIAL: skolem territory, NOT this lane's subject.  A classifier that
; counted it would inflate the ceiling with the one shape activation cannot
; reach, so this fixture must report pos_forall_split=0 and exists_pos>=1.
; qshape expects: pos_forall_unit=0 pos_forall_split=0 exists_pos=1
;                 activation_target=0
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (not (forall ((x Int)) (> (f x) x))))
(check-sat)
