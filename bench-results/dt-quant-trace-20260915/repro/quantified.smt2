(set-logic AUFDTLIRA)
; IDENTICAL datatypes and IDENTICAL `f` to `ground.smt2`, with a universal
; added. If the decline were a property of the QUANTIFIER, this file would
; decline and `ground.smt2` would not.
(declare-datatypes ((inner 0)) (((mk_inner (ic Int)))))
(declare-datatypes ((outer 0)) (((mk_outer (in_ inner) (oc Int)))))
(declare-fun f (outer) Int)
(declare-const a outer)
(declare-const b outer)
(assert (forall ((x outer)) (>= (f x) 0)))
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
