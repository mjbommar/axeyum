; Bool/QF_LIA non-negative benefit check for tax-benefit-arithmetic-v0.
;
; Source clauses:
; - Rule 3(c): phase-out floors the final benefit at 0.
;
; The bad pattern asks for a negative final benefit under the piecewise-linear
; source formula.
(set-logic QF_LIA)
(declare-const income Int)
(declare-const household_size Int)
(declare-const phase_start Int)
(declare-const base Int)
(declare-const raw Int)
(declare-const benefit Int)

(assert (>= income 0))
(assert (<= income 80))
(assert (>= household_size 1))
(assert (<= household_size 3))
(assert (= phase_start 45))
(assert (= base (+ 20 (* 5 (- household_size 1)))))
(assert (= raw (- base (* 2 (- income phase_start)))))

(assert (=> (<= income phase_start) (= benefit base)))
(assert (=> (and (> income phase_start) (>= raw 0)) (= benefit raw)))
(assert (=> (and (> income phase_start) (< raw 0)) (= benefit 0)))

(assert (< benefit 0))
(check-sat)
