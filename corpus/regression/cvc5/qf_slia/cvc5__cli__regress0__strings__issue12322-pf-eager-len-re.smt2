; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress0/strings/issue12322-pf-eager-len-re.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress0/strings/issue12322-pf-eager-len-re.smt2
; :status derived from upstream's own `; EXPECT: unsat` test metadata (no `(set-info :status ...)` in the original file).

; REQUIRES: no-safe-mode
; COMMAND-LINE: --strings-eager-len-re
; EXPECT: unsat
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-const x String)
(assert (str.in_re x (re.+ (str.to_re "YY"))))
(assert (> 2 (str.len x)))
(check-sat)
