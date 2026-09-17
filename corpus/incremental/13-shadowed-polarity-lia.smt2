; ADR-2143: the theory-level sequence the ax-proptest audit found LiaTheory
; losing (push; assert a; push; assert (not a); pop; assert b), written at the
; script level. The front door re-solves each check-sat from scratch, so the
; theory's own push/pop is never driven by these commands and this file pins
; that every verdict stays right: the inner scope is contradictory, after the
; pop `x >= 10` must still be live against `x <= 0`, and the outer pop frees it.
; check-sat-order: unsat unsat sat
(set-logic QF_LIA)
(declare-const x Int)
(push 1)
(assert (>= x 10))
(push 1)
(assert (not (>= x 10)))
(check-sat)
(pop 1)
(assert (<= x 0))
(check-sat)
(pop 1)
(check-sat)
