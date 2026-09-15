(set-logic AUFDTLIRA)
; CONTROL. Same shape and the same quantifier as `quantified.smt2`, but `outer`
; now has only SCALAR fields, so its expansion IS exact
; (datatype_native.rs:1576) and the congruence arm has nothing to refuse.
;
; If this file also declined, the experiment would be measuring something other
; than exactness -- the presence of a datatype, say, or of a UF over one.
(declare-datatypes ((outer 0)) (((mk_outer (oi Int) (oc Int)))))
(declare-fun f (outer) Int)
(declare-const a outer)
(declare-const b outer)
(assert (forall ((x outer)) (>= (f x) 0)))
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
