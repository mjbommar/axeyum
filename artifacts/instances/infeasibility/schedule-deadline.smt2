; Project schedule with a contractual delivery date -- INFEASIBLE.
;
; 20 tasks, continuous (Real) start times in days from project start,
; 30 precedence edges, 4 material release dates, 5 crew-availability
; windows, and one delivery deadline on t12.
;
; Nineteen of the twenty tasks can be scheduled inside the window. The
; contradiction is a single critical chain whose head is a long-lead
; material release; it is a five-row explanation in a 61-row model, and
; its Farkas refutation has every multiplier equal to 1.

(set-logic QF_LRA)
(set-option :produce-unsat-cores true)

(declare-fun s_t01 () Real)
(declare-fun s_t02 () Real)
(declare-fun s_t03 () Real)
(declare-fun s_t04 () Real)
(declare-fun s_t05 () Real)
(declare-fun s_t06 () Real)
(declare-fun s_t07 () Real)
(declare-fun s_t08 () Real)
(declare-fun s_t09 () Real)
(declare-fun s_t10 () Real)
(declare-fun s_t11 () Real)
(declare-fun s_t12 () Real)
(declare-fun s_t13 () Real)
(declare-fun s_t14 () Real)
(declare-fun s_t15 () Real)
(declare-fun s_t16 () Real)
(declare-fun s_t17 () Real)
(declare-fun s_t18 () Real)
(declare-fun s_t19 () Real)
(declare-fun s_t20 () Real)

; -- no task starts before the project does
(assert (! (>= s_t01 0.0) :named start_t01))
(assert (! (>= s_t02 0.0) :named start_t02))
(assert (! (>= s_t03 0.0) :named start_t03))
(assert (! (>= s_t04 0.0) :named start_t04))
(assert (! (>= s_t05 0.0) :named start_t05))
(assert (! (>= s_t06 0.0) :named start_t06))
(assert (! (>= s_t07 0.0) :named start_t07))
(assert (! (>= s_t08 0.0) :named start_t08))
(assert (! (>= s_t09 0.0) :named start_t09))
(assert (! (>= s_t10 0.0) :named start_t10))
(assert (! (>= s_t11 0.0) :named start_t11))
(assert (! (>= s_t12 0.0) :named start_t12))
(assert (! (>= s_t13 0.0) :named start_t13))
(assert (! (>= s_t14 0.0) :named start_t14))
(assert (! (>= s_t15 0.0) :named start_t15))
(assert (! (>= s_t16 0.0) :named start_t16))
(assert (! (>= s_t17 0.0) :named start_t17))
(assert (! (>= s_t18 0.0) :named start_t18))
(assert (! (>= s_t19 0.0) :named start_t19))
(assert (! (>= s_t20 0.0) :named start_t20))

; -- precedence: a successor waits for its predecessor to finish
(assert (! (>= s_t03 (+ s_t01 4.0)) :named prec_t01_t03))
(assert (! (>= s_t04 (+ s_t01 4.0)) :named prec_t01_t04))
(assert (! (>= s_t05 (+ s_t02 3.0)) :named prec_t02_t05))
(assert (! (>= s_t07 (+ s_t02 3.0)) :named prec_t02_t07))
(assert (! (>= s_t06 (+ s_t03 5.0)) :named prec_t03_t06))
(assert (! (>= s_t08 (+ s_t04 2.0)) :named prec_t04_t08))
(assert (! (>= s_t08 (+ s_t05 3.0)) :named prec_t05_t08))
(assert (! (>= s_t09 (+ s_t06 6.0)) :named prec_t06_t09))
(assert (! (>= s_t10 (+ s_t07 2.0)) :named prec_t07_t10))
(assert (! (>= s_t11 (+ s_t08 4.0)) :named prec_t08_t11))
(assert (! (>= s_t12 (+ s_t09 3.0)) :named prec_t09_t12))
(assert (! (>= s_t13 (+ s_t10 2.0)) :named prec_t10_t13))
(assert (! (>= s_t14 (+ s_t11 3.0)) :named prec_t11_t14))
(assert (! (>= s_t15 (+ s_t13 2.0)) :named prec_t13_t15))
(assert (! (>= s_t16 (+ s_t14 3.0)) :named prec_t14_t16))
(assert (! (>= s_t17 (+ s_t15 2.0)) :named prec_t15_t17))
(assert (! (>= s_t18 (+ s_t16 4.0)) :named prec_t16_t18))
(assert (! (>= s_t19 (+ s_t17 2.0)) :named prec_t17_t19))
(assert (! (>= s_t20 (+ s_t18 3.0)) :named prec_t18_t20))
(assert (! (>= s_t20 (+ s_t19 2.0)) :named prec_t19_t20))
(assert (! (>= s_t07 (+ s_t04 2.0)) :named prec_t04_t07))
(assert (! (>= s_t10 (+ s_t05 3.0)) :named prec_t05_t10))
(assert (! (>= s_t11 (+ s_t07 2.0)) :named prec_t07_t11))
(assert (! (>= s_t14 (+ s_t10 2.0)) :named prec_t10_t14))
(assert (! (>= s_t16 (+ s_t13 2.0)) :named prec_t13_t16))
(assert (! (>= s_t18 (+ s_t15 2.0)) :named prec_t15_t18))
(assert (! (>= s_t04 (+ s_t02 3.0)) :named prec_t02_t04))
(assert (! (>= s_t02 (+ s_t01 4.0)) :named prec_t01_t02))
(assert (! (>= s_t15 (+ s_t11 3.0)) :named prec_t11_t15))
(assert (! (>= s_t17 (+ s_t14 3.0)) :named prec_t14_t17))

; -- material release dates (long-lead procurement)
(assert (! (>= s_t03 6.0) :named material_t03))  ; long-lead casting
(assert (! (>= s_t08 2.0) :named material_t08))
(assert (! (>= s_t16 3.0) :named material_t16))
(assert (! (>= s_t20 1.0) :named material_t20))

; -- crew availability windows
(assert (! (<= s_t02 12.0) :named crew_t02))
(assert (! (<= s_t05 14.0) :named crew_t05))
(assert (! (<= s_t07 16.0) :named crew_t07))
(assert (! (<= s_t10 18.0) :named crew_t10))
(assert (! (<= s_t13 20.0) :named crew_t13))

; -- contractual delivery: t12 must finish by day 20
(assert (! (<= (+ s_t12 4.0) 20.0) :named deadline_delivery))

(check-sat)
(get-unsat-core)
(exit)
