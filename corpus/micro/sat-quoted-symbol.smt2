; origin: Axeyum hand-written micro corpus
; expected: sat
; pins: quoted SMT-LIB symbol ingestion and Boolean/BV mixed assertions
(set-info :status sat)
(set-logic QF_BV)
(declare-const |x y| (_ BitVec 4))
(declare-const p Bool)
(assert (= ((_ zero_extend 4) |x y|) (_ bv10 8)))
(assert (=> p p))
(check-sat)
