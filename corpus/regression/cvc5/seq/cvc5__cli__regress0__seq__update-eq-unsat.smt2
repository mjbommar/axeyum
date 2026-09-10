; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/update-eq-unsat.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/update-eq-unsat.smt2
; :status derived from upstream's own `; EXPECT: unsat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --seq-array=eager
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () (Seq Int))

(assert (= (str.len x) 1))
(assert (= (seq.update x 0 (seq.unit 1)) (seq.update x 0 (seq.unit 2))))

(check-sat)
