; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/seq/proj-issue586-nth-update-no-fact.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/seq/proj-issue586-nth-update-no-fact.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :seq-array eager)
(declare-const x String)
(declare-const x5 (Bag String))
(assert (str.<= x (seq.nth (seq.update (seq.unit x) (bag.card x5) (seq.unit x)) (bag.card x5))))
(check-sat)
