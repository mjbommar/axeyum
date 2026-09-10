; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/seq/proj-issue733-mbqi-w.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/seq/proj-issue733-mbqi-w.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :mbqi-enum true)
(declare-const x (Seq Bool))
(assert (distinct (seq.at x 9510904) (seq.++ (seq.at x 9510904) (seq.rev (seq.at x 9510904)))))
(check-sat)
