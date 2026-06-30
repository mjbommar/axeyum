; Bool/QF_LIA cap check for tax-benefit-arithmetic-v0.
;
; Source clauses:
; - Rule 3(a): household credit is 20 plus 5 per additional member.
; - Rule 3(b): benefit may never exceed 30 units.
;
; Since household_size is bounded to 1..3, the unreduced base is at most 30,
; and phase-out never increases it.
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

(assert (> benefit 30))
(check-sat)
