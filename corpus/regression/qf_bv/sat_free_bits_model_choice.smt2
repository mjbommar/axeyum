; origin: Axeyum hand-written seed (ADR-2140)
; expected: sat
; pins: a query with MANY models -- x and z are forced, y has three witnesses
;       (0xF4, 0xF5, 0xF6) and the search reaches them through a retracted
;       branch, so a model PREFERENCE is visible here where a unique-model
;       fixture cannot show one.
(set-info :status sat)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (or (= x #x05) (bvult y #x10)))
(assert (or (= x #x05) (bvuge y #x10)))
(assert (or (= z #x07) (bvult y #xf0)))
(assert (or (= z #x07) (bvuge y #xf0)))
(assert (bvult (bvadd x y z) #x03))
(check-sat)
