; `r2` with `Real` swapped for `Int` — the pair differs in that one token.
; Over Int `0 < m[i] < 1` is UNSAT, which is what makes `r2`'s `sat` evidence
; about the element sort rather than about the solver answering `sat` to
; everything.
; z3 4.13.3: unsat. cvc5 1.3.4: unsat.
(set-logic QF_ALIA)
(declare-fun m () (Array Int Int))
(declare-fun i () Int)
(assert (> (select m i) 0))
(assert (< (select m i) 1))
(check-sat)
