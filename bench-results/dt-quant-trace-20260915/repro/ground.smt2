(set-logic AUFDTLIRA)
; `inner` is EXACT (its only field is Int). `outer` has a DATATYPE-typed field,
; so `datatype_expansion_is_exact(outer)` -- datatype_native.rs:1576 -- is
; false: `in_` gets no expansion variable. `f` takes an `outer`, so the
; Ackermann congruence arm at datatype_native.rs:963 refuses.
;
; NO QUANTIFIER ANYWHERE. This is the ground half of the experiment.
(declare-datatypes ((inner 0)) (((mk_inner (ic Int)))))
(declare-datatypes ((outer 0)) (((mk_outer (in_ inner) (oc Int)))))
(declare-fun f (outer) Int)
(declare-const a outer)
(declare-const b outer)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
