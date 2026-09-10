; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/to_upper_12.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/to_upper_12.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: unrestricted-mode
; COMMAND-LINE: --seq-array=lazy
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const X String)
(assert (= (str.to_upper X) (str.to_lower X)))
(assert (>= (str.len X) 12))
(check-sat)
