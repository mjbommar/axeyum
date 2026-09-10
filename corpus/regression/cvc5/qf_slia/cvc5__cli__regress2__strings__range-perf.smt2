; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress2/strings/range-perf.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress2/strings/range-perf.smt2
; :status derived from upstream's own `; EXPECT: sat` test metadata (no `(set-info :status ...)` in the original file).

; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const x String)
(assert (str.in_re x ((_ re.loop 12 12) (re.range "0" "9"))))
(assert (str.in_re x (re.++ (re.* re.allchar) (str.to_re "01") (re.* re.allchar))))
(check-sat)
