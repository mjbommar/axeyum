; origin: Axeyum hand-written seed (ADR-2140), the cindergraph defects
;         example's `a + b < a` overflow shape
; expected: sat
; pins: every model wraps; the least-magnitude witnesses are (-1, 1) and
;       (1, -1), and a `least-unsigned` preference returns one of them.
(set-info :status sat)
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (bvult (bvadd a b) a))
(check-sat)
