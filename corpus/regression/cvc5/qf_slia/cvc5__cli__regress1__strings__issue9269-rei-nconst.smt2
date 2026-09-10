; Vendored from cvc5 (BSD-3-Clause; (C) the cvc5 authors and contributors).
; Upstream path: test/regress/cli/regress1/strings/issue9269-rei-nconst.smt2
; Upstream commit: 1689f13331f7543801f82d9dcbcaac2f70a26781
; Source: https://github.com/cvc5/cvc5/blob/1689f13331f7543801f82d9dcbcaac2f70a26781/test/regress/cli/regress1/strings/issue9269-rei-nconst.smt2

(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun v () String)
(declare-fun a () String)
(assert (not (str.in_re (str.++ v "z") (re.++ (str.to_re "b") (re.* (str.to_re (str.replace_all v v "")))))))
(assert (str.in_re (str.++ v "z" a) (re.++ (str.to_re "b") (re.* (str.to_re "z")))))
(check-sat)
