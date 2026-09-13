; SAT: with `i` and `j` unconstrained the write at `i` is visible at `j`
; whenever `i = j`, so the two reads may differ. A route that dropped the `ite`
; from read-over-write — keeping only the "different index, unchanged" leg —
; answers `unsat` here. This is the wrong-unsat trap for the case split.
; z3 4.13.3: sat. cvc5 1.3.4: sat.
(set-logic AUFLIRA)
(declare-fun m () (Array Int Real))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Real)
(assert (not (= (select (store m i v) j) (select m j))))
(check-sat)
