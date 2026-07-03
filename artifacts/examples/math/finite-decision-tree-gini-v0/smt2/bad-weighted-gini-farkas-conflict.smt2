; Source artifact for finite-decision-tree-gini-v0.
; Exact replay gives color weighted Gini impurity = 3/8, represented without
; division as 8*gini_color = 3. The malformed row claims weighted impurity =
; 1/2, represented as 2*gini_color = 1.

(set-logic QF_LRA)

(declare-const gini_color Real)

(assert (= (* 8 gini_color) 3))
(assert (= (* 2 gini_color) 1))

(check-sat)
