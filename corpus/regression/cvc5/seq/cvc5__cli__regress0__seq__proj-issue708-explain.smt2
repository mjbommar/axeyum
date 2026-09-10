; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue708-explain.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue708-explain.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :check-proofs true)
(set-option :strings-eager-eval false)
(declare-const x (Seq Bool))
(assert (seq.contains (seq.++ (seq.unit x) (seq.unit (seq.rev x))) (seq.++ (seq.unit (seq.unit (seq.contains x (seq.rev x)))) (seq.unit x))))
(check-sat)
