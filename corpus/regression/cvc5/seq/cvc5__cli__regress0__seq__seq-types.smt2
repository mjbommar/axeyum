; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/seq-types.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/seq-types.smt2
; :status derived from upstream's own `; EXPECT: unsat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE:
;EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun s () (Seq Int))
(declare-fun n () Int)
(assert (= 5 (seq.nth s n)))
(assert (< n (seq.len s)))
(assert (> n 0))
(assert (= (seq.unit 6) (seq.at s n)))
(check-sat)

