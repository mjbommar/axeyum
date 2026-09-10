; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/seq-eval-contains.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/seq-eval-contains.smt2
; :status derived from upstream's own `; EXPECT: unsat` test metadata (no `(set-info :status ...)` in the original file).

; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(assert
(not
(seq.contains
(seq.++ (seq.unit 1) (seq.unit 2))
(seq.unit 1))))
(check-sat)
