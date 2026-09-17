; origin: Axeyum hand-written seed (ADR-2140), the cindergraph defects
;         example's `len > 256` check that passes signed and fails unsigned
; expected: sat
; pins: every model is negative; `len = -1` is the least-magnitude witness.
(set-info :status sat)
(set-logic QF_BV)
(declare-const len (_ BitVec 32))
(declare-const pad (_ BitVec 16))
(assert (bvsle len (_ bv256 32)))
(assert (bvugt len (_ bv256 32)))
(assert (bvuge pad (_ bv3 16)))
(check-sat)
