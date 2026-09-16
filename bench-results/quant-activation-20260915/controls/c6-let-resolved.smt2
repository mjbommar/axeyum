; CONTROL 6 -- the universal is reachable only THROUGH a `let` reference, and
; the binding is referenced TWICE.  An expander would duplicate it; a resolver
; must attribute it at each reference site without substituting.  `?b` is
; referenced once positively under an `or` (a split occurrence) and once under a
; `not` (a negative one), so the SAME binding must be counted on both sides.
; qshape expects: pos_forall_split=1 exists_pos=1 pos_forall_unit=0
;                 activation_target=1
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const p Bool)
(declare-const r Bool)
(assert (let ((?b (forall ((y Int)) (> (f y) y))))
          (and (or p ?b) (or r (not ?b)))))
(check-sat)
